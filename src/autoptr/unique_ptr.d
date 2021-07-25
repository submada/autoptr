/**
    Implementation of unique pointer `UniquePtr` (similar to c++ std::unique_ptr).

    License:   $(HTTP www.boost.org/LICENSE_1_0.txt, Boost License 1.0).
    Authors:   $(HTTP github.com/submada/basic_string, Adam Búš)
*/
module autoptr.unique_ptr;


import autoptr.internal.mallocator : Mallocator;
import autoptr.internal.destruct : destruct;

import autoptr.common;



/**
    Check if type `T` is of type `UniquePtr!(...)`
*/
public template isUniquePtr(Type){
    import std.traits : Unqual;

    enum bool isUniquePtr = is(Unqual!Type == UniquePtr!Args, Args...);
}

///
unittest{
    static assert(!isUniquePtr!long);
    static assert(!isUniquePtr!(void*));
    static assert(isUniquePtr!(UniquePtr!long));
}


/**
    Default `ControlBlock` for `UniquePtr`.
*/
public alias DefaultUniqueControlBlock = ControlBlock!(void, void);



/**
    `UniquePtr` is a smart pointer that owns and manages object through a pointer and disposes of that object when the `UniquePtr` goes out of scope.

    The object is destroyed and its memory deallocated when either of the following happens:
        
        1. the managing `UniquePtr` object is destroyed

        2. the managing `UniquePtr` object is assigned another pointer via various methods like `opAssign` and `store`.

    The object is destroyed using delete-expression or a custom deleter that is supplied to `UniquePtr` during construction.

    A `UniquePtr` may alternatively own no object, in which case it is called empty.
    
    Template parameters:

        `_Type` type of managed object

        `_DestructorType` function pointer with attributes of destructor, to get attributes of destructor from type use `autoptr.common.DestructorType!T`. Destructor of type `_Type` must be compatible with `_DestructorType`

        `_ControlType` represent type of counter, must by of type `autoptr.common.ControlBlock`.
*/
template UniquePtr(
    _Type,
    _DestructorType = DestructorType!_Type,
    _ControlType = shared(DefaultUniqueControlBlock),
)
if(isControlBlock!_ControlType && isDestructorType!_DestructorType){
    static assert(is(_ControlType == ControlBlock!(Shared, Weak), Shared, Weak));

    static assert(is(DestructorType!void : _DestructorType),
        _Type.stringof ~ " wrong DestructorType " ~ DestructorType!void.stringof ~ " : " ~ _DestructorType.stringof
    );

    static assert(is(DestructorType!_Type : _DestructorType),
        "destructor of type '" ~ _Type.stringof ~ "' doesn't support specified finalizer " ~ _DestructorType.stringof
    );

    static if (is(_Type == class) || is(_Type == interface) || is(_Type == struct) || is(_Type == union))
        static assert(!__traits(isNested, _Type), "UniquePtr does not support nested types.");


    import std.experimental.allocator : stateSize;
    import std.meta : AliasSeq;
    import core.atomic : MemoryOrder;
    import std.range : ElementEncodingType;
    import std.traits: Unqual, CopyTypeQualifiers, CopyConstness,
        hasIndirections, hasElaborateDestructor,
        isMutable, isAbstractClass, isDynamicArray, isStaticArray, isPointer, isCallable,
        Select;



    enum bool hasWeakCounter = _ControlType.hasWeakCounter;

    enum bool hasSharedCounter = _ControlType.hasSharedCounter;

    enum bool referenceElementType = isReferenceType!_Type || isDynamicArray!_Type;


    alias MakeEmplace(AllocatorType, bool supportGC) = .MakeEmplace!(
        _Type, 
        _DestructorType, 
        _ControlType, 
        AllocatorType, 
        supportGC
    );

    alias MakeDynamicArray(AllocatorType, bool supportGC) = .MakeDynamicArray!(
        _Type, 
        _DestructorType, 
        _ControlType, 
        AllocatorType, 
        supportGC
    );

    enum bool _isLockFree = !isDynamicArray!_Type;

    struct UniquePtr{
        /**
            Type of element managed by `UniquePtr`.
        */
        public alias ElementType = _Type;


        /**
            Type of destructor (`void function(void*)@attributes`).
        */
        public alias DestructorType = _DestructorType;


        /**
            Type of control block.
        */
        public alias ControlType = _ControlType;


        /**
            Same as `ElementType*` or `ElementType` if is class/interface/slice.
        */
        public alias ElementReferenceType = ElementReferenceTypeImpl!ElementType;


        /**
            Return thhread local `UniquePtr` if specified:

                1.  if parameter `threadLocal` is `true` then result type is thread local `UniquePtr` (!is(_ControlType == shared)).

                2.  if parameter `threadLocal` is `false` then result type is not thread local `UniquePtr` (is(_ControlType == shared)).
        */
        public template ThreadLocal(bool threadLocal){
            static if(threadLocal)
                alias ThreadLocal = UniquePtr!(
                    _Type,
                    _DestructorType,
                    Unqual!_ControlType
                );
            else
                alias ThreadLocal = UniquePtr!(
                    _Type,
                    _DestructorType,
                    shared(_ControlType)
                );
        }

        /**
            `true` if shared `UniquePtr` has lock free operations `store` and `exchange`, otherwise 'false'
        */
        public alias isLockFree = _isLockFree;

        static if(isLockFree)
        static assert(ElementReferenceType.sizeof == size_t.sizeof);


        /**
            Destructor

            If `this` owns an object then the object is destroyed.
        */
        public ~this(){
            this._release();
        }



        private this(Elm, this This)(Elm element)pure nothrow @safe @nogc
        if(is(Elm : GetElementReferenceType!This) && !is(Unqual!Elm == typeof(null))){
            this._element = element;
        }

        private this(Rhs, this This)(scope Rhs rhs, typeof(null) nil)@trusted
        if(true
            && isUniquePtr!Rhs
            && isOverlapable!(Rhs.ElementType, This.ElementType)
            && isAliasable!(Rhs, This)
            && !is(Rhs == shared)
        ){
            mixin validateUniquePtr!(This, Rhs);

            this._set_element(cast(typeof(this._element))rhs._element);
            rhs._const_reset();
            //rhs._const_set_element(null);
        }



        /**
            Constructs a `UniquePtr` without managed object. Same as `UniquePtr.init`

            Examples:
                --------------------
                UniquePtr!long x = null;

                assert(x == null);
                assert(x == UniquePtr!long.init);
                --------------------
        */
        public this(this This)(typeof(null) nil)pure nothrow @safe @nogc{
            mixin validateUniquePtr!This;
        }



        /**
            Move constructor.

            Examples:
                --------------------
                TODO
                --------------------
        */
        public this(Rhs, this This)(scope Rhs rhs)@trusted
        if(true
            && isUniquePtr!Rhs
            //&& !is(Unqual!This == Unqual!Rhs) ///TODO move ctor
            && isConstructable!(Rhs, This)
            && !is(Rhs == shared)
        ){
            mixin validateUniquePtr!(This, Rhs);

            this(rhs._element);
            //this._element = rhs._element;   //this._set_element(rhs._element);
            rhs._const_reset();
        }

        @disable public this(scope ref const typeof(this) rhs)pure nothrow @safe @nogc;

        @disable public this(scope ref const shared typeof(this) rhs)pure nothrow @safe @nogc;


        /**
            Releases the ownership of the managed object, if any.

            After the call, this manages no object.

            Examples:
                --------------------
                {
                    UniquePtr!long x = UniquePtr!long.make(1);

                    assert(x != null);
                    assert(*x == 1);
                    x = null;
                    assert(x == null);
                }

                {
                    UniquePtr!(shared long) x = UniquePtr!(shared long).make(1);

                    assert(x != null);
                    assert(*x == 1);
                    x = null;
                    assert(x == null);
                }
                --------------------
        */
        public void opAssign(MemoryOrder order = MemoryOrder.seq, this This)(typeof(null) nil)scope
        if(isMutable!This){
            mixin validateUniquePtr!This;

            static if(is(This == shared)){
                static if(isLockFree){
                    import core.atomic : atomicExchange;

                    alias Result = ChangeElementType!(This, ElementType);
                    ()@trusted{
                        Result tmp;
                        tmp._set_element(cast(typeof(this._element))atomicExchange!order(
                            cast(Unqual!(This.ElementReferenceType)*)&this._element,
                            null
                        ));
                    }();
                }
                else{
                    return this.lockUniquePtr!(
                        (ref scope self) => self.opAssign!order(null)
                    )();
                }
            }
            else{
                this._release();
                this._reset();

            }
        }



        /**
            Move ownership of the object managed by `rhs`.

            If `rhs` manages no object, `this` manages no object too.

            Examples:
                --------------------
                import core.lifetime : move;
                {
                    UniquePtr!long px1 = UniquePtr!long.make(1);
                    UniquePtr!long px2 = UniquePtr!long.make(2);

                    px1 = move(px2);
                    assert(px2 == null);
                    assert(px1 != null);
                    assert(*px1 == 2);
                }


                {
                    UniquePtr!long px = UniquePtr!long.make(1);
                    UniquePtr!(const long) pcx = UniquePtr!long.make(2);

                    pcx = move(px);
                    assert(px == null);
                    assert(pcx != null);
                    assert(*pcx == 1);

                }
                --------------------
        */
        public void opAssign(MemoryOrder order = MemoryOrder.seq, Rhs, this This)(scope Rhs rhs)scope @safe
        if(true
            && isUniquePtr!Rhs
            && isAssignable!(Rhs, This)
            && !is(Rhs == shared)
            && isMutable!This
        ){
            mixin validateUniquePtr!(Rhs, This);

            static if(is(This == shared)){
                static if(isLockFree){
                    import core.atomic : atomicExchange;

                    alias Result = ChangeElementType!(This, ElementType);
                    ()@trusted{
                        Result tmp;
                        GetElementReferenceType!This source = rhs._element;    //interface/class cast

                        tmp._set_element(cast(typeof(this._element))atomicExchange!order(
                            cast(Unqual!(This.ElementReferenceType)*)&this._element,
                            cast(Unqual!(This.ElementReferenceType))source
                        ));
                        rhs._const_reset();
                    }();
                }
                else{
                    return this.lockUniquePtr!(
                        (ref scope self, Rhs x) => self.opAssign!order(x.move)
                    )(rhs.move);
                }
            }
            else{
                this._release();

                ()@trusted{
                    this._element = cast(typeof(this._element))rhs._element;
                    rhs._const_reset();
                }();
            }
        }



        /**
            Constructs an object of type `ElementType` and wraps it in a `UniquePtr` using args as the parameter list for the constructor of `ElementType`.

            The object is constructed as if by the expression `emplace!ElementType(_payload, forward!args)`, where _payload is an internal pointer to storage suitable to hold an object of type `ElementType`.

            Examples:
                --------------------
                {
                    UniquePtr!long a = UniquePtr!long.make();
                    assert(a.get == 0);

                    UniquePtr!(const long) b = UniquePtr!long.make(2);
                    assert(b.get == 2);
                }

                {
                    static struct Struct{
                        int i = 7;

                        this(int i)pure nothrow @safe @nogc{
                            this.i = i;
                        }
                    }

                    UniquePtr!Struct s1 = UniquePtr!Struct.make();
                    assert(s1.get.i == 7);

                    UniquePtr!Struct s2 = UniquePtr!Struct.make(123);
                    assert(s2.get.i == 123);
                }
                --------------------
        */
        public static UniquePtr make
            (AllocatorType = DefaultAllocator, bool supportGC = platformSupportGC, Args...)
            (auto ref Args args)
        if(stateSize!AllocatorType == 0 && !isDynamicArray!ElementType){

            import core.lifetime : forward;

            auto m = MakeEmplace!(AllocatorType, supportGC).make(forward!(args));

            if(m is null)
                return typeof(return).init;


            auto ptr = typeof(this).init;

            //ptr._control = m.base;
            ptr._element = m.get;

            return ptr.move; //.move;
        }



        /**
            Constructs an object of array type `ElementType` including its array elements and wraps it in a `UniquePtr`.

            Parameters:
                n = Array length

                args = parameters for constructor for each array element.

            The array elements are constructed as if by the expression `emplace!ElementType(_payload, args)`, where _payload is an internal pointer to storage suitable to hold an object of type `ElementType`.
            The storage is typically larger than `ElementType.sizeof * n` in order to use one allocation for both the control block and the each array element.

            Examples:
                --------------------
                auto arr = UniquePtr!(long[]).make(6, -1);
                assert(arr.length == 6);
                assert(arr.get.length == 6);

                import std.algorithm : all;
                assert(arr.get.all!(x => x == -1));

                for(long i = 0; i < 6; ++i)
                    arr.get[i] = i;

                assert(arr.get == [0, 1, 2, 3, 4, 5]);
                --------------------
        */
        public static UniquePtr make
            (AllocatorType = DefaultAllocator, bool supportGC = platformSupportGC, Args...)
            (const size_t n, auto ref Args args)
        if(stateSize!AllocatorType == 0 && isDynamicArray!ElementType){
            import core.lifetime : forward;

            auto m = MakeDynamicArray!(AllocatorType, supportGC).make(n, forward!(args));

            if(m is null)
                return typeof(return).init;


            auto ptr = typeof(this).init;

            //ptr._control = m.base;
            ptr._set_element(m.get);

            return ptr.move;
        }

        /**
            Constructs an object of type `ElementType` and wraps it in a `UniquePtr` using args as the parameter list for the constructor of `ElementType`.

            The object is constructed as if by the expression `emplace!ElementType(_payload, forward!args)`, where _payload is an internal pointer to storage suitable to hold an object of type `ElementType`.

            Examples:
                --------------------
                import std.experimental.allocator : allocatorObject;
                auto a = allocatorObject(Mallocator.instance);
                {
                    UniquePtr!long x = UniquePtr!long.alloc(a);
                    assert(x.get == 0);

                    UniquePtr!(const long) y = UniquePtr!long.alloc(a, 2);
                    assert(y.get == 2);
                }

                {
                    static struct Struct{
                        int i = 7;

                        this(int i)pure nothrow @safe @nogc{
                            this.i = i;
                        }
                    }

                    UniquePtr!Struct s1 = UniquePtr!Struct.alloc(a);
                    assert(s1.get.i == 7);

                    UniquePtr!Struct s2 = UniquePtr!Struct.alloc(a, 123);
                    assert(s2.get.i == 123);
                }
                --------------------
        */
        public static UniquePtr alloc
            (AllocatorType, bool supportGC = platformSupportGC, Args...)
            (AllocatorType a, auto ref Args args)
        if(stateSize!AllocatorType >= 0 && !isDynamicArray!ElementType){
            import core.lifetime : forward;

            auto m = MakeEmplace!(AllocatorType, supportGC).make(forward!(a, args));


            if(m is null)
                return typeof(return).init;


            auto ptr = typeof(this).init;

            //ptr._control = m.base;
            ptr._element = m.get;

            return ptr.move; //.move;
        }


        /**
            Constructs an object of array type `ElementType` including its array elements and wraps it in a `UniquePtr`.

            Parameters:
                n = Array length

                args = parameters for constructor for each array element.

            The array elements are constructed as if by the expression `emplace!ElementType(_payload, args)`, where _payload is an internal pointer to storage suitable to hold an object of type `ElementType`.
            The storage is typically larger than `ElementType.sizeof * n` in order to use one allocation for both the control block and the each array element.

            Examples:
                --------------------
                auto a = allocatorObject(Mallocator.instance);
                auto arr = UniquePtr!(long[], DestructorType!(typeof(a))).alloc(a, 6, -1);
                assert(arr.length == 6);
                assert(arr.get.length == 6);

                import std.algorithm : all;
                assert(arr.get.all!(x => x == -1));

                for(long i = 0; i < 6; ++i)
                    arr.get[i] = i;

                assert(arr.get == [0, 1, 2, 3, 4, 5]);
                --------------------
        */
        public static UniquePtr alloc
            (AllocatorType, bool supportGC = platformSupportGC, Args...)
            (AllocatorType a, const size_t n, auto ref Args args)
        if(stateSize!AllocatorType >= 0 && isDynamicArray!ElementType){
            import core.lifetime : forward;

            auto m = MakeDynamicArray!(AllocatorType, supportGC).make(forward!(a, n, args));

            if(m is null)
                return typeof(return).init;

            auto ptr = typeof(this).init;

            ptr._set_element(m.get);

            return ptr.move;
        }

        /**
            Swap `this` with `rhs`

            Examples:
                --------------------
                {
                    UniquePtr!long a = UniquePtr!long.make(1);
                    UniquePtr!long b = UniquePtr!long.make(2);
                    a.proxySwap(b);
                    assert(*a == 2);
                    assert(*b == 1);
                    import std.algorithm : swap;
                    swap(a, b);
                    assert(*a == 1);
                    assert(*b == 2);
                }
                --------------------
        */
        public void proxySwap(ref scope typeof(this) rhs)scope @trusted pure nothrow @nogc{
            auto tmp = this._element;
            this._set_element(rhs._element);
            rhs._set_element(tmp);
        }


        /**
            Stores the non `shared` rvalue `UniquePtr` parameter `ptr` to `this`.

            If `this` is shared then operation is atomic or guarded by mutex.

            Template parameter `order` has type `core.atomic.MemoryOrder`.

            Examples:
                --------------------
                //null store:
                {
                    shared x = UniquePtr!(shared long).make(123);
                    //*x == 123

                    x.store(null);
                    //x is null
                }

                //rvalue store:
                {
                    shared x = UniquePtr!(shared long).make(123);
                    //*x == 123

                    x.store(UniquePtr!(shared long).make(42));
                    //*x == 42

                    auto tmp = x.exchange(null);
                    //x is null
                    assert(tmp.get == 42);
                }
                --------------------
        */
        public void store(MemoryOrder order = MemoryOrder.seq, this This)(typeof(null) desired)scope
        if(isMutable!This){
            mixin validateUniquePtr!This;

            this.opAssign!order(null);

        }

        /// ditto
        public void store(MemoryOrder order = MemoryOrder.seq, Ptr, this This)(scope Ptr desired)scope
        if(true
            && isUniquePtr!Ptr
            && !is(Ptr == shared)
            && isAssignable!(Ptr, This)
        ){
            mixin validateUniquePtr!(Ptr, This);

            this.opAssign!order(desired.move);
        }



        /**
            Stores the non `shared` rvalue `UniquePtr` parameter `ptr` to `this` and returns the value formerly pointed-to by this.

            If `this` is shared then operation is atomic or guarded by mutex (depends on `isLockFree`).

            Template parameter `order` has type `core.atomic.MemoryOrder`.

            Examples:
                --------------------
                {
                    shared UniquePtr!(shared long) x = UniquePtr!(shared long).make(123);
                    UniquePtr!(shared long) y = UniquePtr!(shared long).make(42);

                    auto z = x.exchange(y.move);
                    assert(y == null);
                    assert(*z == 123);

                    auto tmp = x.exchange(null);
                    assert(*tmp == 42);
                }

                //swap:
                {
                    shared UniquePtr!(shared long) x = UniquePtr!(shared long).make(123);
                    UniquePtr!(shared long) y = UniquePtr!(shared long).make(42);

                    y = x.exchange(y.move);
                    assert(*y == 123);

                    auto tmp = x.exchange(null);
                    assert(*tmp == 42);
                }
                --------------------
        */
        public auto exchange(MemoryOrder order = MemoryOrder.seq, this This)(typeof(null) ptr)scope
        if(isMutable!This){
            mixin validateUniquePtr!This;

            static if(is(This == shared)){
                static if(isLockFree){
                    import core.atomic : atomicExchange;

                    alias Result = ChangeElementType!(This, ElementType);
                    return()@trusted{
                        Result result;

                        result._set_element(cast(typeof(this._element))atomicExchange!order(
                            cast(Unqual!(This.ElementReferenceType)*)&this._element,
                            null
                        ));

                        return result.move;
                    }();
                }
                else{
                    return this.lockUniquePtr!(
                        (ref scope self) => self.exchange!order(null)
                    )();
                }
            }
            else{
                return this.move;
            }
        }

        /// ditto
        public auto exchange(MemoryOrder order = MemoryOrder.seq, Ptr, this This)(scope Ptr ptr)scope
        if(true
            && isUniquePtr!Ptr
            && !is(Ptr == shared)
            && isAssignable!(Ptr, This)
        ){
            mixin validateUniquePtr!(Ptr, This);

            static if(is(This == shared)){
                static if(isLockFree){
                    import core.atomic : atomicExchange;

                    alias Result = ChangeElementType!(This, ElementType);
                    return()@trusted{
                        Result result;
                        GetElementReferenceType!This source = ptr._element;    //interface/class cast

                        result._set_element(cast(typeof(this._element))atomicExchange!order(
                            cast(Unqual!(This.ElementReferenceType)*)&this._element,
                            cast(Unqual!(This.ElementReferenceType))source
                        ));
                        ptr._const_reset();


                        return result.move;
                    }();
                }
                else{
                    return this.lockUniquePtr!(
                        (ref scope self, Ptr x) => self.exchange!order(x.move)
                    )(ptr.move);
                }
            }
            else{
                auto result = this.move;

                return()@trusted{
                    this = ptr.move;
                    return result.move;
                }();
            }
        }



        /**
            Operator *

            Get reference to managed object of `ElementType`, same as `.get`

            Examples:
                --------------------
                import core.lifetime : move;

                UniquePtr!long x = UniquePtr!long.make(123);
                assert(*x == 123);
                (*x = 321);
                assert(*x == 321);
                const y = move(x);
                assert(*y == 321);
                assert(x == null);
                static assert(is(typeof(*y) == const long));
                --------------------
        */
        public alias opUnary(string op : "*") = get;



        /**
            Get reference to managed object of `ElementType`, same as `operator*``

            Examples:
                --------------------
                import core.lifetime : move;

                UniquePtr!long x = UniquePtr!long.make(123);
                assert(x.get == 123);
                x.get = 321;
                assert(x.get == 321);
                const y = move(x);
                assert(y.get == 321);
                assert(x == null);
                static assert(is(typeof(y.get) == const long));
                --------------------
        */
        static if(referenceElementType)
            public @property inout(ElementType) get()inout scope return pure nothrow @system @nogc{
                return this._element;
            }
        else static if(is(Unqual!ElementType == void))
            /// ditto
            public @property inout(ElementType) get()inout scope pure nothrow @system @nogc{
            }
        else
            /// ditto
            public @property ref inout(ElementType) get()inout scope return pure nothrow @system @nogc{
                return *cast(inout ElementType*)this._element;
            }


        /**
            Get pointer to managed object of `ElementType` or reference if `ElementType` is reference type (class or interface)

            Examples:
                --------------------
                import core.lifetime : move;

                UniquePtr!long x = UniquePtr!long.make(123);
                assert(*x.element == 123);
                x.get = 321;
                assert(*x.element == 321);
                const y = move(x);
                assert(*y.element == 321);
                assert(x == null);
                static assert(is(typeof(y.element) == const(long)*));
                --------------------
        */
        public @property ElementReferenceTypeImpl!(inout ElementType) element()
        inout scope return pure nothrow @system @nogc{
            return this._element;
        }


        /**
            Returns length of dynamic array (isDynamicArray!ElementType == true).

            Examples:
                --------------------
                auto x = UniquePtr!(int[]).make(10, -1);
                assert(x.length == 10);
                assert(x.get.length == 10);

                import std.algorithm : all;
                assert(x.get.all!(i => i == -1));
                --------------------
        */
        static if(isDynamicArray!ElementType)
        public @property size_t length()const scope pure nothrow @safe @nogc{
            return this._element.length;
        }



        /**
            Checks if `this` stores a non-null pointer, i.e. whether `this != null`.

            Examples:
                --------------------
                UniquePtr!long x = UniquePtr!long.make(123);
                assert(cast(bool)x);    //explicit cast
                assert(x);              //implicit cast
                x = null;
                assert(!cast(bool)x);   //explicit cast
                assert(!x);             //implicit cast
                --------------------
        */
        public bool opCast(To : bool)()const scope pure nothrow @safe @nogc
        if(is(To : bool)){ //docs
            return (this != null);
        }



        /**
            Operator == and != .

            Examples:
                --------------------
                {
                    UniquePtr!long x = UniquePtr!long.make(0);
                    assert(x != null);
                    x = null;
                    assert(x == null);
                }

                {
                    UniquePtr!long x = UniquePtr!long.make(123);
                    UniquePtr!long y = UniquePtr!long.make(123);
                    assert(x == x);
                    assert(y == y);
                    assert(x != y);
                }

                {
                    UniquePtr!long x;
                    UniquePtr!(const long) y;
                    assert(x == x);
                    assert(y == y);
                    assert(x == y);
                }

                {
                    UniquePtr!long x = UniquePtr!long.make(123);
                    UniquePtr!long y = UniquePtr!long.make(123);
                    assert(x == x.element);
                    assert(y.element == y);
                    assert(x != y.element);
                }
                --------------------
        */
        public bool opEquals(typeof(null) nil)const @safe scope pure nothrow @nogc{
            static if(isDynamicArray!ElementType)
                return (this._element.length == 0);
            else
                return (this._element is null);
        }

        /// ditto
        public bool opEquals(Rhs)(auto ref scope const Rhs rhs)const @safe scope pure nothrow @nogc
        if(isUniquePtr!Rhs && !is(Rhs == shared)){
            return this.opEquals(rhs._element);
        }

        /// ditto
        public bool opEquals(Elm)(scope const Elm elm)const @safe scope pure nothrow @nogc
        if(is(Elm : GetElementReferenceType!(typeof(this)))){
            static if(isDynamicArray!ElementType){
                static assert(isDynamicArray!Elm);

                if(this._element.length != elm.length)
                    return false;

                if(this._element.ptr is elm.ptr)
                    return true;

                return (this._element.length == 0);
            }
            else{
                return (this._element is elm);
            }
        }



        /**
            Operators <, <=, >, >= for `UniquePtr`.

            Compare address of payload.

            Examples:
                --------------------
                {
                    const a = UniquePtr!long.make(42);
                    const b = UniquePtr!long.make(123);
                    const n = UniquePtr!long.init;

                    assert((a < b) == !(a >= b));
                    assert((a > b) == !(a <= b));

                    assert(a > n);
                    assert(n < a);
                }

                {
                    const a = UniquePtr!long.make(42);
                    const b = UniquePtr!long.make(123);

                    assert((a < b.element) == !(a.element >= b));
                    assert((a > b.element) == !(a.element <= b));
                }
                --------------------
        */
        public sizediff_t opCmp(typeof(null) nil)const @trusted scope pure nothrow @nogc{
            static if(isDynamicArray!ElementType){
                return this._element.length;
            }
            else{
                return (cast(const void*)this._element) - (cast(const void*)null);
            }
        }

        /// ditto
        public sizediff_t opCmp(Elm)(scope const Elm elm)const @trusted scope pure nothrow @nogc
        if(is(Elm : GetElementReferenceType!(typeof(this)))){
            static if(isDynamicArray!ElementType){
                const void* lhs = cast(const void*)(this._element.ptr + this._element.length);
                const void* rhs = cast(const void*)(elm.ptr + elm.length);

                return lhs - rhs;
            }
            else{
                return (cast(const void*)this._element) - (cast(const void*)elm);
            }
        }

        /// ditto
        public sizediff_t opCmp(Rhs)(auto ref scope const Rhs rhs)const @trusted scope pure nothrow @nogc
        if(isUniquePtr!Rhs && !is(Rhs == shared)){
            return this.opCmp(rhs._element);
        }



        /**
            Generate hash

            Return:
                Address of payload as `size_t`

            Examples:
                --------------------
                import core.lifetime : move;
                {
                    UniquePtr!long x = UniquePtr!long.make(123);
                    UniquePtr!long y = UniquePtr!long.make(123);
                    assert(x.toHash == x.toHash);
                    assert(y.toHash == y.toHash);
                    assert(x.toHash != y.toHash);

                    const x_hash = x.toHash;
                    UniquePtr!(const long) z = move(x);
                    assert(x_hash == z.toHash);
                }
                {
                    UniquePtr!long x;
                    UniquePtr!(const long) y;
                    assert(x.toHash == x.toHash);
                    assert(y.toHash == y.toHash);
                    assert(x.toHash == y.toHash);
                }
                --------------------
        */
        public @property size_t toHash()@trusted scope const pure nothrow @nogc {
            static if(isDynamicArray!ElementType)
                return cast(size_t)cast(void*)(this._element.ptr + this._element.length);
            else
                return cast(size_t)cast(void*)this._element;
        }



        /**
            Move `UniquePtr`
        */
        public auto move()()scope{
            import core.lifetime : move_impl = move;
            return move_impl(this);
        }


        package inout(ControlType)* _control()inout pure nothrow @trusted @nogc
        in(this._element !is null){
            static if(isDynamicArray!ElementType){
                return cast(inout(ControlType)*)((cast(void*)this._element.ptr) - ControlType.sizeof);
            }
            else static if(is(ElementType == interface)){
                static assert(__traits(getLinkage, ElementType) == "D");
                return cast(inout(ControlType)*)((cast(void*)cast(Object)cast(Unqual!ElementType)this._element) - ControlType.sizeof);
            }
            else{
                return cast(inout(ControlType)*)((cast(void*)this._element) - ControlType.sizeof);
            }
        }

        private ElementReferenceType _element;


        private void _release()scope /*pure nothrow @safe @nogc*/ {
            if(false){
                DestructorType dt;
                dt(null);
            }

            import std.traits : hasIndirections;
            import core.memory : GC;

            if(this._is_null)
                return;

            static if(hasSharedCounter)
                assert(this._control.count!(false) == 0);
            static if(hasWeakCounter)
                assert(this._control.count!(true) == 0);

            this._control.manual_destroy(true);
        }


        private void _set_element(ElementReferenceType e)pure nothrow @trusted @nogc{
            (*cast(Unqual!ElementReferenceType*)&this._element) = cast(Unqual!ElementReferenceType)e;
        }

        private void _reset()scope pure nothrow @trusted @nogc{
            this._set_element(null);
        }

        package void _const_reset()scope const pure nothrow @trusted @nogc{
            auto self = cast(Unqual!(typeof(this))*)&this;

            self._reset();
        }

        private bool _is_null()scope const pure nothrow @safe @nogc{
            return (this._element is null);
        }


    }
}

/// ditto
public template UniquePtr(
    _Type,
    _ControlType,
    _DestructorType = DestructorType!_Type
)
if(isControlBlock!_ControlType && isDestructorType!_DestructorType){
    alias UniquePtr = .UniquePtr!(_Type, _DestructorType, _ControlType);
}



/**
    Create `SharedPtr` from parameter `ptr` if `ControlType` of `ptr` has shared counter.
*/
auto sharedPtr(Ptr)(scope Ptr ptr)@trusted
if(isUniquePtr!Ptr && Ptr.ControlType.hasSharedCounter){
    import std.traits : CopyTypeQualifiers;
    import autoptr.shared_ptr : SharedPtr;

    alias ResultPtr = SharedPtr!(
        CopyTypeQualifiers!(Ptr, Ptr.ElementType),
        Ptr.DestructorType,
        Ptr.ControlType
    );

    if(ptr == null)
        return ResultPtr.init;

    auto result = ResultPtr(ptr._control, ptr.element);
    ptr._const_reset();

    import core.lifetime : move;
    return (()@trusted => move(result) )();
}


/// 
unittest{
    alias ControlType = ControlBlock!(int, void);

    alias UPtr(T) = UniquePtr!(
        T,
        DestructorType!T,
        shared ControlType
    );

    auto x = UPtr!long.make(42);
    assert(*x == 42);

    auto s = sharedPtr(x.move);
    import autoptr.shared_ptr : isSharedPtr;

    static assert(isSharedPtr!(typeof(s)));
    static assert(is(typeof(s).ControlType == shared ControlType));

}

///
pure nothrow @nogc unittest{
    import core.lifetime : move;

    import autoptr.shared_ptr : SharedPtr, DefaultSharedControlBlock;

    alias Uptr(T) = UniquePtr!(
        T,
        DestructorType!T,
        shared DefaultSharedControlBlock
    );

    {
        auto u = Uptr!long.make(42);

        auto s = sharedPtr(move(u));
        assert(u == null);
        assert(s != null);
    }

    {
        auto u = Uptr!long.make(42);

        SharedPtr!long.ThreadLocal!false s = sharedPtr(move(u));
        assert(u == null);
        assert(s != null);
        assert(s.useCount == 1);
        assert(*s == 42);
    }
}



/**
    Return `shared UniquePtr` pointing to same managed object like parameter `ptr`.

    Type of parameter `ptr` must be `SharedPtr` with `shared(ControlType)` and `shared`/`immutable` `ElementType` .
*/
public shared(Ptr) share(Ptr)(scope Ptr ptr)
if(isUniquePtr!Ptr){
    mixin validateUniquePtr!Ptr;

    import core.lifetime : forward;
    static if(is(Ptr == shared)){
        return forward!ptr;
    }
    else{
        static assert(is(Ptr.ControlType == shared),
            "`UniquePtr` has not shared `ControlType`."
        );

        static assert(is(Ptr.ElementType == shared) || is(Ptr.ElementType == immutable),
            "`UniquePtr` has not shared/immutable `ElementType`."
        );

        alias Result = shared(Ptr);
        mixin validateUniquePtr!Result;

        return Result(forward!ptr);
    }
}

///
nothrow @nogc unittest{
    {
        auto x = UniquePtr!(shared long).make(123);

        shared s = share(x.move);
        assert(x == null);

        auto y = s.exchange(null);
        assert(*y == 123);
    }

    {
        auto x = UniquePtr!(long).make(123);

        ///error `shared UniquePtr` need shared `ControlType` and shared `ElementType`.
        //shared s = share(x);

    }
}




/+
import std.traits : isPointer, isDynamicArray;

public ChangeElementType!(Ptr, Elm) alaisToMove(Ptr, Elm)(ref Ptr ptr, Elm elm)@trusted
if(isReferenceType!Elm || isPointer!Elm || isDynamicArray!Elm){
    const void* from = ptr.element.elementAddress;

    if(from is null)
        return typeof(return).init;

    const void* from = elm.elementAddress;



    static if(isDynamicArray!ElementReferenceType)
        return cast(const void*)this._element.ptr;
    else static if(isRefereceType!ElementReferenceType)
        return cast(const void*)cast(const Object)cast(const Unqual!ElementType)this._element;
    else static if(isPointer!ElementReferenceType)
        return cast(const void*)this._element;
    else static if(is(Unqual!Elm : typeof(null))){
    }
    else static assert(0, "no impl");


}+/



/**
    TODO
*/
public auto first(Ptr)(scope Ptr ptr)@trusted
if(isUniquePtr!Ptr && is(Ptr.ElementType : T[], T)){
    import std.traits : isDynamicArray, isStaticArray;
    import std.range : ElementEncodingType;

    alias Result = ChangeElementType!(
        Ptr,
        ElementEncodingType!(Ptr.ElementType)
    );

    if(ptr == null)
        return Result.init;

    static if(isDynamicArray!(Ptr.ElementType) || isStaticArray!(Ptr.ElementType)){
        auto ptr_element = ptr._element.ptr;
        ptr._const_reset();
        return Result(ptr_element);
    }
    else static assert(0, "no impl");
}

///
pure nothrow @nogc unittest{
    {
        auto x = UniquePtr!(long[]).make(10, -1);
        assert(x.length == 10);

        auto y = first(x.move);
        static assert(is(typeof(y) == UniquePtr!long));
        assert(*y == -1);
    }

    {
        auto x = UniquePtr!(long[10]).make(-1);
        assert(x.get.length == 10);

        auto y = first(x.move);
        static assert(is(typeof(y) == UniquePtr!long));
        assert(*y == -1);
    }
}


//mutex:
private static auto lockUniquePtr(alias fn, Ptr, Args...)(auto ref shared Ptr ptr, auto ref scope return Args args){
    import std.traits : CopyConstness, CopyTypeQualifiers, Unqual;
    import core.lifetime : forward;
    import autoptr.mutex : getMutex;


    //static assert(!Ptr.threadLocal);
    shared mutex = getMutex(ptr);

    mutex.lock();
    scope(exit)mutex.unlock();

    alias Result = ChangeElementType!(
        CopyConstness!(Ptr, Unqual!Ptr),      //remove shared from this
        CopyTypeQualifiers!(shared Ptr, Ptr.ElementType)
    );


    return fn(
        *(()@trusted => cast(Result*)&ptr )(),
        forward!args
    );
}


/**
    Dynamic cast for shared pointers if `ElementType` is class with D linkage.

    Creates a new instance of `UniquePtr` whose stored pointer is obtained from `ptr`'s stored pointer using a dynaic cast expression.

    If `ptr` is null or dynamic cast fail then result `UniquePtr` is null.
    Otherwise, the new `UniquePtr` will share ownership with the initial value of `ptr`.
*/
public ChangeElementType!(Ptr, T) dynCastMove(T, Ptr)(auto ref scope Ptr ptr)
if(true
    && isUniquePtr!Ptr && !is(Ptr == shared)
    && isReferenceType!T && (__traits(getLinkage, T) == "D")
    && isReferenceType!(Ptr.ElementType) && (__traits(getLinkage, Ptr.ElementType) == "D")
){

    import std.traits : CopyTypeQualifiers;

    alias Return = typeof(return);

    //static assert(is(CopyTypeQualifiers!(GetElementReferenceType!Ptr, void*) : CopyTypeQualifiers!(GetElementReferenceType!Return, void*) ));

    if(ptr == null)
        return Return.init;

    if(auto element = cast(Return.ElementType)ptr._element){
        assert(element is ptr._element);
        return (()@trusted => Return(ptr.move, null) )();

    }

    return Return.init;
}

///
pure nothrow unittest{
    static class Foo{
        int i;

        this(int i)pure nothrow @safe @nogc{
            this.i = i;
        }
    }

    static class Bar : Foo{
        double d;

        this(int i, double d)pure nothrow @safe @nogc{
            super(i);
            this.d = d;
        }
    }

    static class Zee{
    }

    {
        UniquePtr!(const Foo) foo = UniquePtr!Bar.make(42, 3.14);
        assert(foo.get.i == 42);

        auto bar = dynCastMove!Bar(foo);
        assert(bar != null);
        assert(foo == null);
        assert(bar.get.d == 3.14);
        static assert(is(typeof(bar) == UniquePtr!(const Bar)));

        auto zee = dynCastMove!Zee(bar);
        assert(zee == null);
        assert(bar != null);
        static assert(is(typeof(zee) == UniquePtr!(const Zee)));
    }
}



/**
    Same as `dynCastMove` but parameter `ptr` is rvalue.
*/
public ChangeElementType!(Ptr, T) dynCast(T, Ptr)(scope Ptr ptr)
if(true
    && isUniquePtr!Ptr && !is(Ptr == shared)
    && is(T == class) && (__traits(getLinkage, T) == "D")
    && is(Ptr.ElementType == class) && (__traits(getLinkage, Ptr.ElementType) == "D")
){

    return dynCastMove!T(ptr);
}

///
unittest{
    static class Foo{
        int i;

        this(int i)pure nothrow @safe @nogc{
            this.i = i;
        }
    }

    static class Bar : Foo{
        double d;

        this(int i, double d)pure nothrow @safe @nogc{
            super(i);
            this.d = d;
        }
    }

    static class Zee{
    }

    {
        UniquePtr!(const Foo) foo = UniquePtr!Bar.make(42, 3.14);
        assert(foo.get.i == 42);

        auto bar = dynCast!Bar(foo.move);
        assert(bar != null);
        assert(foo == null);
        assert(bar.get.d == 3.14);
        static assert(is(typeof(bar) == UniquePtr!(const Bar)));

        auto zee = dynCast!Zee(bar.move);
        assert(zee == null);
        assert(bar == null);
        static assert(is(typeof(zee) == UniquePtr!(const Zee)));
    }
}




//local traits:
private{
    package mixin template validateUniquePtr(Ts...){
        static foreach(alias T; Ts){
            static assert(isUniquePtr!T);
            static assert(!is(T == shared) || is(T.ControlType == shared),
                "shared `UniquePtr` is valid only if its `ControlType` is shared."
            );
        }
    }

    template isOverlapable(From, To)
    if(!isUniquePtr!From && !isUniquePtr!To){
        import std.traits : Unqual;

        static if(is(Unqual!From == Unqual!To))
            enum bool isOverlapable = true;

        else static if(isReferenceType!From && isReferenceType!To)
            enum bool isOverlapable = true
                && (__traits(getLinkage, From) == "D")
                && (__traits(getLinkage, To) == "D");

        else
            enum bool isOverlapable = false;
    }

    template isAliasable(From, To)
    if(isUniquePtr!From && isUniquePtr!To){
        import std.traits : CopyTypeQualifiers, Unqual;

        alias FromType = CopyTypeQualifiers!(
            From,
            CopyTypeQualifiers!(From.ElementType, void)
        );
        alias ToType = CopyTypeQualifiers!(
            To,
            CopyTypeQualifiers!(To.ElementType, void)
        );

        enum bool isAliasable = true
            //&& isOverlapable!(From.ElementType, To.ElementType)
            && is(FromType* : ToType*)
            && is(From.DestructorType : To.DestructorType)
            && is(From.ControlType == To.ControlType);
    }

    version(unittest){
  
        unittest{
            alias Uptr(T) = UniquePtr!T.ThreadLocal!false;

            //Type:
            static assert(isAliasable!(Uptr!long, Uptr!long));

            static assert(isAliasable!(Uptr!long, Uptr!(const long)));
            static assert(!isAliasable!(Uptr!(const long), Uptr!(long)));
            static assert(isAliasable!(Uptr!(const long), Uptr!(const long)));


            static assert(!isAliasable!(Uptr!(shared long), Uptr!(long)));
            static assert(!isAliasable!(Uptr!(long), Uptr!(shared long)));
            static assert(isAliasable!(Uptr!(shared long), Uptr!(shared long)));

            static assert(!isAliasable!(Uptr!(immutable long), Uptr!(long)));
            static assert(!isAliasable!(Uptr!(long), Uptr!(immutable long)));
            static assert(isAliasable!(Uptr!(immutable long), Uptr!(immutable long)));


            static assert(isAliasable!(Uptr!(immutable long), Uptr!(shared const long)));
            static assert(!isAliasable!(Uptr!(shared const long), Uptr!(immutable long)));

            //UniquePtr:
            static assert(isAliasable!(Uptr!long, const Uptr!long));
            static assert(!isAliasable!(const Uptr!long, Uptr!long));
        }
        unittest{
            alias Uptr(T) = UniquePtr!T.ThreadLocal!true;

            //Type:
            static assert(isAliasable!(Uptr!long, Uptr!long));

            static assert(isAliasable!(Uptr!long, Uptr!(const long)));
            static assert(!isAliasable!(Uptr!(const long), Uptr!(long)));
            static assert(isAliasable!(Uptr!(const long), Uptr!(const long)));


            static assert(!isAliasable!(Uptr!(shared long), Uptr!(long)));
            static assert(!isAliasable!(Uptr!(long), Uptr!(shared long)));
            static assert(isAliasable!(Uptr!(shared long), Uptr!(shared long)));

            static assert(!isAliasable!(Uptr!(immutable long), Uptr!(long)));
            static assert(!isAliasable!(Uptr!(long), Uptr!(immutable long)));
            static assert(isAliasable!(Uptr!(immutable long), Uptr!(immutable long)));


            static assert(isAliasable!(Uptr!(immutable long), Uptr!(shared const long)));
            static assert(!isAliasable!(Uptr!(shared const long), Uptr!(immutable long)));

            //UniquePtr:
            static assert(isAliasable!(Uptr!long, const Uptr!long));
            static assert(!isAliasable!(const Uptr!long, Uptr!long));
        }

    }

    template isConstructable(From, To)
    if(isUniquePtr!From && isUniquePtr!To){
        import std.traits : CopyTypeQualifiers, Unqual;

        alias FromPtr = CopyTypeQualifiers!(From, From.ElementReferenceType);
        alias ToPtr = CopyTypeQualifiers!(To, To.ElementReferenceType);

        enum bool isConstructable = true
            && isOverlapable!(From.ElementType, To.ElementType) //&& is(Unqual!(From.ElementType) == Unqual!(To.ElementType))
            && is(FromPtr : ToPtr)
            && is(From.DestructorType : To.DestructorType)
            && is(From.ControlType == To.ControlType)            ;
    }

    template isAssignable(From, To)
    if(isUniquePtr!From && isUniquePtr!To){
        import std.traits : isMutable;

        enum bool isAssignable = true
            && isConstructable!(From, To)
            && isMutable!To;
    }

    template GetElementReferenceType(Ptr)
    if(isUniquePtr!Ptr){
        import std.traits : CopyTypeQualifiers, Select, isDynamicArray;
        import std.range : ElementEncodingType;

        alias ElementType = CopyTypeQualifiers!(Ptr, Ptr.ElementType);

        alias GetElementReferenceType = ElementReferenceTypeImpl!ElementType;
    }

    template ChangeElementType(Ptr, T)
    if(isUniquePtr!Ptr){
        import std.traits : CopyTypeQualifiers, Unqual;

        alias FromType = CopyTypeQualifiers!(Ptr, Ptr.ElementType);
        alias ResultType = CopyTypeQualifiers!(FromType, T);

        //static assert(is(Unqual!ResultType == Unqual!FromType), Unqual!ResultType.stringof ~ " != " ~ Unqual!FromType.stringof);

        alias ResultPtr = UniquePtr!(
            ResultType,

            Ptr.DestructorType,
            //Ptr.threadLocal,
            Ptr.ControlType,
        );

        /+static if(is(Ptr == shared))
            alias ChangeElementType = shared ResultPtr;
        else+/
        alias ChangeElementType = ResultPtr;
    }

}


version(unittest){


    //this null
    pure nothrow @nogc unittest{
        UniquePtr!long x = null;

        assert(x == null);
        assert(x == UniquePtr!long.init);
    }

    //this rhs
    pure nothrow @nogc unittest{
        //TODO
    }


    //opAssign null
    pure nothrow @nogc unittest{

        {
            UniquePtr!long x = UniquePtr!long.make(1);

            assert(x != null);
            assert(*x == 1);
            x = null;
            assert(x == null);
        }

        {
            UniquePtr!(shared long) x = UniquePtr!(shared long).make(1);

            assert(x != null);
            assert(*x == 1);
            x = null;
            assert(x == null);
        }
    }

    //opAssign UniquePtr
    pure nothrow @nogc unittest{

        import core.lifetime : move;
        {
            UniquePtr!long px1 = UniquePtr!long.make(1);
            UniquePtr!long px2 = UniquePtr!long.make(2);

            px1 = move(px2);
            assert(px2 == null);
            assert(px1 != null);
            assert(*px1 == 2);
        }


        {
            UniquePtr!long px = UniquePtr!long.make(1);
            UniquePtr!(const long) pcx = UniquePtr!long.make(2);

            pcx = move(px);
            assert(px == null);
            assert(pcx != null);
            assert(*pcx == 1);

        }
    }

    //store
    nothrow @nogc unittest{
        //null store:
        {
            shared x = UniquePtr!(shared long).make(123);
            //*x == 123

            x.store(null);
            //x is null
        }

        //rvalue store:
        {
            shared x = UniquePtr!(shared long).make(123);
            //*x == 123

            x.store(UniquePtr!(shared long).make(42));
            //*x == 42

            auto tmp = x.exchange(null);
            //x is null
            assert(tmp.get == 42);
        }
    }

    //exchange
    pure nothrow @nogc unittest{
        {
            shared UniquePtr!(shared long) x = UniquePtr!(shared long).make(123);
            UniquePtr!(shared long) y = UniquePtr!(shared long).make(42);

            auto z = x.exchange(y.move);
            assert(y == null);
            assert(*z == 123);

            auto tmp = x.exchange(null);
            assert(*tmp == 42);
        }

        //swap:
        {
            shared UniquePtr!(shared long) x = UniquePtr!(shared long).make(123);
            UniquePtr!(shared long) y = UniquePtr!(shared long).make(42);

            y = x.exchange(y.move);
            assert(*y == 123);

            auto tmp = x.exchange(null);
            assert(*tmp == 42);
        }
    }

    //make
    pure nothrow @nogc unittest{

        {
            UniquePtr!long a = UniquePtr!long.make();
            assert(a.get == 0);

            UniquePtr!(const long) b = UniquePtr!long.make(2);
            assert(b.get == 2);
        }

        {
            static struct Struct{
                int i = 7;

                this(int i)pure nothrow @safe @nogc{
                    this.i = i;
                }
            }

            UniquePtr!Struct s1 = UniquePtr!Struct.make();
            assert(s1.get.i == 7);

            UniquePtr!Struct s2 = UniquePtr!Struct.make(123);
            assert(s2.get.i == 123);
        }
    }

    //make dynamic array
    pure nothrow @nogc unittest{
        auto arr = UniquePtr!(long[]).make(6, -1);
        assert(arr.length == 6);
        assert(arr.get.length == 6);

        import std.algorithm : all;
        assert(arr.get.all!(x => x == -1));

        for(long i = 0; i < 6; ++i)
            arr.get[i] = i;

        assert(arr.get == [0, 1, 2, 3, 4, 5]);
    }

    //alloc
    nothrow unittest{
        import std.experimental.allocator : allocatorObject;
        auto a = allocatorObject(Mallocator.instance);
        {
            UniquePtr!long x = UniquePtr!long.alloc(a);
            assert(x.get == 0);

            UniquePtr!(const long) y = UniquePtr!long.alloc(a, 2);
            assert(y.get == 2);
        }

        {
            static struct Struct{
                int i = 7;

                this(int i)pure nothrow @safe @nogc{
                    this.i = i;
                }
            }

            UniquePtr!Struct s1 = UniquePtr!Struct.alloc(a);
            assert(s1.get.i == 7);

            UniquePtr!Struct s2 = UniquePtr!Struct.alloc(a, 123);
            assert(s2.get.i == 123);
        }
    }

    //alloc dynamic array
    nothrow unittest{
        import std.experimental.allocator : allocatorObject;
        auto a = allocatorObject(Mallocator.instance);
        {
            UniquePtr!long x = UniquePtr!long.alloc(a);
            assert(x.get == 0);

            UniquePtr!(const long) y = UniquePtr!long.alloc(a, 2);
            assert(y.get == 2);
        }

        {
            static struct Struct{
                int i = 7;

                this(int i)pure nothrow @safe @nogc{
                    this.i = i;
                }
            }

            UniquePtr!Struct s1 = UniquePtr!Struct.alloc(a);
            assert(s1.get.i == 7);

            UniquePtr!Struct s2 = UniquePtr!Struct.alloc(a, 123);
            assert(s2.get.i == 123);
        }
    }

    //proxySwap
    pure nothrow @nogc unittest{
        {
            UniquePtr!long a = UniquePtr!long.make(1);
            UniquePtr!long b = UniquePtr!long.make(2);
            a.proxySwap(b);
            assert(*a == 2);
            assert(*b == 1);
            import std.algorithm : swap;
            swap(a, b);
            assert(*a == 1);
            assert(*b == 2);
        }
    }

    //opUnary : '*'
    pure nothrow @nogc unittest{
        import core.lifetime : move;

        UniquePtr!long x = UniquePtr!long.make(123);
        assert(*x == 123);
        (*x = 321);
        assert(*x == 321);
        const y = move(x);
        assert(*y == 321);
        assert(x == null);
        static assert(is(typeof(*y) == const long));
    }

    //get
    pure nothrow @nogc unittest{
        import core.lifetime : move;

        UniquePtr!long x = UniquePtr!long.make(123);
        assert(x.get == 123);
        x.get = 321;
        assert(x.get == 321);
        const y = move(x);
        assert(y.get == 321);
        assert(x == null);
        static assert(is(typeof(y.get) == const long));
    }

    //element
    pure nothrow @nogc unittest{
        import core.lifetime : move;

        UniquePtr!long x = UniquePtr!long.make(123);
        assert(*x.element == 123);
        x.get = 321;
        assert(*x.element == 321);
        const y = move(x);
        assert(*y.element == 321);
        assert(x == null);
        static assert(is(typeof(y.element) == const(long)*));
    }

    //length
    pure nothrow @nogc unittest{
        auto x = UniquePtr!(int[]).make(10, -1);
        assert(x.length == 10);
        assert(x.get.length == 10);

        import std.algorithm : all;
        assert(x.get.all!(i => i == -1));
    }

    //opCast : bool
    pure nothrow @nogc unittest{

        UniquePtr!long x = UniquePtr!long.make(123);
        assert(cast(bool)x);    //explicit cast
        assert(x);              //implicit cast
        x = null;
        assert(!cast(bool)x);   //explicit cast
        assert(!x);             //implicit cast
    }

    //opEquals 
    pure nothrow @nogc unittest{

        {
            UniquePtr!long x = UniquePtr!long.make(0);
            assert(x != null);
            x = null;
            assert(x == null);
        }

        {
            UniquePtr!long x = UniquePtr!long.make(123);
            UniquePtr!long y = UniquePtr!long.make(123);
            assert(x == x);
            assert(y == y);
            assert(x != y);
        }

        {
            UniquePtr!long x;
            UniquePtr!(const long) y;
            assert(x == x);
            assert(y == y);
            assert(x == y);
        }

        {
            UniquePtr!long x = UniquePtr!long.make(123);
            UniquePtr!long y = UniquePtr!long.make(123);
            assert(x == x.element);
            assert(y.element == y);
            assert(x != y.element);
        }
    }

    //opCmp
    pure nothrow @nogc unittest{
        {
            const a = UniquePtr!long.make(42);
            const b = UniquePtr!long.make(123);
            const n = UniquePtr!long.init;

            assert((a < b) == !(a >= b));
            assert((a > b) == !(a <= b));

            assert(a > n);
            assert(n < a);
        }

        {
            const a = UniquePtr!long.make(42);
            const b = UniquePtr!long.make(123);

            assert((a < b.element) == !(a.element >= b));
            assert((a > b.element) == !(a.element <= b));
        }
    }

    //toHash
    pure nothrow @nogc unittest{
        import core.lifetime : move;
        {
            UniquePtr!long x = UniquePtr!long.make(123);
            UniquePtr!long y = UniquePtr!long.make(123);
            assert(x.toHash == x.toHash);
            assert(y.toHash == y.toHash);
            assert(x.toHash != y.toHash);

            const x_hash = x.toHash;
            UniquePtr!(const long) z = move(x);
            assert(x_hash == z.toHash);
        }
        {
            UniquePtr!long x;
            UniquePtr!(const long) y;
            assert(x.toHash == x.toHash);
            assert(y.toHash == y.toHash);
            assert(x.toHash == y.toHash);
        }
    }


}

/+
// 
version(D_BetterC){}else
pure nothrow @nogc unittest{

    static interface I{

    }
    
    static class Foo : I{
        int i;

        this(int i)pure nothrow @safe @nogc{
            this.i = i;
        }
    }

    static class Bar : Foo{
        double d;

        this(int i, double d)pure nothrow @safe @nogc{
            super(i);
            this.d = d;
        }
    }

    UniquePtr!I i = UniquePtr!Bar.make(42, 3.14);

    UniquePtr!Foo foo = dynCastMove!Foo(i);
    assert(i == null);
    assert(foo != null);
    assert(foo.get.i == 42);
    
    UniquePtr!Bar bar = dynCast!Bar(UniquePtr!Bar.init);
    assert(bar == null);

}+/


pure nothrow @safe @nogc unittest{
    UniquePtr!void u = UniquePtr!void.make();
}
