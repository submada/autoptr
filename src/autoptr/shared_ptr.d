/**
    Implementation of reference counted pointer `SharedPtr` (similar to c++ std::shared_ptr).

	License:   $(HTTP www.boost.org/LICENSE_1_0.txt, Boost License 1.0).
	Authors:   $(HTTP github.com/submada/basic_string, Adam Búš)
*/
module autoptr.shared_ptr;

import std.stdio : writeln;
import std.conv : to;

import autoptr.internal.mallocator : Mallocator;
import autoptr.internal.destruct : destruct;

import autoptr.common;
import autoptr.unique_ptr : isUniquePtr, UniquePtr;
import autoptr.rc_ptr : isRcPtr, RcPtr;



/** 
    Check if type `T` is of type `SharedPtr!(...)`.
*/
public template isSharedPtr(Type){
    import std.traits : Unqual;

    enum bool isSharedPtr = is(Unqual!Type == SharedPtr!Args, Args...);
}

///
unittest{
    static assert(!isSharedPtr!long);
    static assert(!isSharedPtr!(void*));
    static assert(isSharedPtr!(SharedPtr!long));
    static assert(isSharedPtr!(WeakPtr!long));
}



/**
    Default `ControlBlock` for `SharedPtr`.
*/
public alias DefaultSharedControlBlock = ControlBlock!(int, int);



/**
    `SharedPtr` is a smart pointer that retains shared ownership of an object through a pointer.

    Several `SharedPtr` objects may own the same object.

    The object is destroyed and its memory deallocated when either of the following happens:

        1. the last remaining `SharedPtr` owning the object is destroyed.

        2. the last remaining `SharedPtr` owning the object is assigned another pointer via various methods like `opAssign` and `store`.

    The object is destroyed using delete-expression or a custom deleter that is supplied to `SharedPtr` during construction.

    A `SharedPtr` can share ownership of an object while storing a pointer to another object.
    This feature can be used to point to member objects while owning the object they belong to.
    The stored pointer is the one accessed by `get()`, the dereference and the comparison operators.
    The managed pointer is the one passed to the deleter when use count reaches zero.

    A `SharedPtr` may also own no objects, in which case it is called empty (an empty `SharedPtr` may have a non-null stored pointer if the aliasing constructor was used to create it).

    If template parameter `_ControlType` is `shared`  then all member functions (including copy constructor and copy assignment)
    can be called by multiple threads on different instances of `SharedPtr` without additional synchronization even if these instances are copies and share ownership of the same object.

    If multiple threads of execution access the same `SharedPtr` (`shared SharedPtr`) then only some methods can be called (`load`, `store`, `exchange`, `compareExchange`, `useCount`).

    Template parameters:

        `_Type` type of managed object

        `_DestructorType` function pointer with attributes of destructor, to get attributes of destructor from type use `autoptr.common.DestructorType!T`. Destructor of type `_Type` must be compatible with `_DestructorType`

        `_ControlType` represent type of counter, must by of type `autoptr.common.ControlBlock`. if is shared then ref counting is atomic.

        `_weakPtr` if `true` then `SharedPtr` represent weak ptr

*/
public template SharedPtr(
    _Type,
    _DestructorType = DestructorType!_Type,
    _ControlType = ControlTypeDeduction!(_Type, DefaultSharedControlBlock),
    bool _weakPtr = false
)
if(isControlBlock!_ControlType && isDestructorType!_DestructorType){
    static assert(is(_ControlType == ControlBlock!(Shared, Weak), Shared, Weak));
    static assert(_ControlType.hasSharedCounter);


    static if(_weakPtr)
    static assert(_ControlType.hasWeakCounter);


    static assert(is(DestructorType!void : _DestructorType),
        _Type.stringof ~ " wrong DestructorType " ~ DestructorType!void.stringof ~ 
        " : " ~ _DestructorType.stringof
    );

    static assert(is(DestructorType!_Type : _DestructorType),
        "destructor of type '" ~ _Type.stringof ~ 
        "' doesn't support specified finalizer " ~ _DestructorType.stringof
    );

    static if (is(_Type == class) || is(_Type == interface) || is(_Type == struct) || is(_Type == union))
        static assert(!__traits(isNested, _Type), "SharedPtr does not support nested types.");


    import std.experimental.allocator : stateSize;
    import std.meta : AliasSeq;
    import core.atomic : MemoryOrder;
    import std.range : ElementEncodingType;
    import std.traits: Unqual, CopyTypeQualifiers, CopyConstness,
        hasIndirections, hasElaborateDestructor,
        isMutable, isAbstractClass, isDynamicArray, isStaticArray, isCallable, Select, isArray;



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

    alias MakeDeleter(DeleterType, AllocatorType, bool supportGC) = .SharedPtrMakeDeleter!(
        _Type, 
        _DestructorType, 
        _ControlType, 
        DeleterType, 
        AllocatorType, 
        supportGC
    );


    enum bool _isLockFree = false;

    struct SharedPtr{
        /**
            Type of element managed by `SharedPtr`.
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
            `true` if `SharedPtr` is weak ptr.
        */
        public enum bool weakPtr = _weakPtr;


        /**
            Same as `ElementType*` or `ElementType` if is class/interface/slice.
        */
        public alias ElementReferenceType = ElementReferenceTypeImpl!ElementType;


        /**
            Type of weak ptr (must have weak counter).
        */
        static if(hasWeakCounter && !weakPtr)
        public alias WeakType = SharedPtr!(
            _Type,
            _DestructorType,
            _ControlType,
            true
        );


        /**
            Type of non weak ptr (must have weak counter).
        */
        static if(weakPtr)
        public alias SharedType = SharedPtr!(
            _Type,
            _DestructorType,
            _ControlType,
            false
        );


        /**
            Return thhread local `SharedPtr` if specified:

                1.  if parameter `threadLocal` is `true` then result type is thread local `SharedPtr` (!is(_ControlType == shared)).

                2.  if parameter `threadLocal` is `false` then result type is not thread local `SharedPtr` (is(_ControlType == shared)).
        */
        public template ThreadLocal(bool threadLocal = true){
            static if(threadLocal)
                alias ThreadLocal = SharedPtr!(
                    _Type,
                    _DestructorType,
                    Unqual!_ControlType,
                    weakPtr
                );
            else
                alias ThreadLocal = SharedPtr!(
                    _Type,
                    _DestructorType,
                    shared(_ControlType),
                    weakPtr
                );
        }


        /**
            `true` if shared `SharedPtr` has lock free operations `store`, `load`, `exchange`, `compareExchange`, otherwise 'false'
        */
        public alias isLockFree = _isLockFree;

        static if(isLockFree)
        static assert(ElementReferenceType.sizeof == size_t.sizeof);


        /**
            Destructor

            If `this` owns an object and it is the last `SharedPtr` owning it, the object is destroyed.
            After the destruction, the smart pointers that shared ownership with `this`, if any, will report a `useCount()` that is one less than its previous value.
        */
        public ~this(){
            this._release();
        }



        //necesary for autoptr.unique_ptr.sharedPtr
        package this(C, Elm, this This)(C* control, Elm element)pure nothrow @safe @nogc
        if(true
            && is(C* : ControlType*)
            && is(Elm : GetElementReferenceType!This)
            && !is(This == shared)
        ){
            mixin validateSharedPtr!This;

            this._control = control;
            this._element = element;
        }


        /**
            Constructs a `SharedPtr` without managed object. Same as `SharedPtr.init`

            Examples:
                --------------------
                SharedPtr!long x = null;

                assert(x == null);
                assert(x == SharedPtr!long.init);
                --------------------
        */
        public this(this This)(typeof(null) nil)pure nothrow @safe @nogc{
            mixin validateSharedPtr!This;
        }


        /**
            Constructs a `SharedPtr` which shares ownership of the object managed by `rhs` and pointing to `element`.

            The aliasing constructor: constructs a `SharedPtr` which shares ownership information with the initial value of `rhs`, 
                but holds an unrelated and unmanaged pointer ptr. If this `SharedPtr` is the last of the group to go out of scope, 
                it will call the stored deleter for the object originally managed by `rhs`. 
                However, calling `get()` or `ptr()` on this `SharedPtr` will always return a copy of `element`.
                It is the responsibility of the programmer to make sure that this ptr remains valid as long as this `SharedPtr` exists, 
                such as in the typical use cases where `element` is a member of the object managed by `rhs` or is an alias (e.g., downcast) of `rhs.get()`.

            Examples:
                --------------------
                static struct Foo{
                    int i;
                    double d;
                }
                SharedPtr!Foo foo = SharedPtr!Foo.make(42, 3.14);

                auto x = SharedPtr!double(foo, &foo.d);
                assert(foo.useCount == 2);
                assert(foo.get == 3.14);
                --------------------
        */
        public this(Rhs, Elm, this This)(ref scope Rhs rhs, Elm element)@trusted
        if(true
            && isSharedPtr!Rhs
            && is(Elm : GetElementReferenceType!This)
            && isAliasable!(Rhs, This)
            && !needLock!(Rhs, This)
            && !is(Rhs == shared)
        ){
            mixin validateSharedPtr!(This, Rhs);

            this._control = cast(typeof(this._control))rhs._control;
            this._element = element;

            if(this._control !is null)
                (cast(ControlType*)this._control).add!weakPtr;
        }

        /// ditto
        public this(Rhs, Elm, this This)(scope Rhs rhs, Elm element)@trusted
        if(true
            && isSharedPtr!Rhs
            && is(Elm : GetElementReferenceType!This)
            && isAliasable!(Rhs, This)
            && !needLock!(Rhs, This)
            && !is(Rhs == shared)
        ){
            mixin validateSharedPtr!(This, Rhs);

            this._control = cast(typeof(this._control))rhs._control;
            this._element = element;

            rhs._const_set_counter(null);
            //rhs._const_set_element(null);
        }

        /**
            Constructs a `SharedPtr` which shares ownership of the object managed by `rhs`.

            If rhs manages no object, this manages no object too.
            If rhs if rvalue then ownership is moved.
            The template overload doesn't participate in overload resolution if ElementType of `typeof(rhs)` is not implicitly convertible to `ElementType`.
            If rhs if `WeakType` then this ctor is equivalent to `this(rhs.lock())`.

            Examples:
                --------------------
                {
                    SharedPtr!long x = SharedPtr!long.make(123);
                    assert(x.useCount == 1);

                    SharedPtr!long a = x;         //lvalue copy ctor
                    assert(a == x);

                    const SharedPtr!long b = x;   //lvalue copy ctor
                    assert(b == x);

                    SharedPtr!(const long) c = x; //lvalue ctor
                    assert(c == x);

                    const SharedPtr!long d = b;   //lvalue ctor
                    assert(d == x);

                    assert(x.useCount == 5);
                }

                {
                    import core.lifetime : move;
                    SharedPtr!long x = SharedPtr!long.make(123);
                    assert(x.useCount == 1);

                    SharedPtr!long a = move(x);        //rvalue copy ctor
                    assert(a.useCount == 1);

                    const SharedPtr!long b = move(a);  //rvalue copy ctor
                    assert(b.useCount == 1);

                    SharedPtr!(const long) c = b.load;  //rvalue ctor
                    assert(c.useCount == 2);

                    const SharedPtr!long d = move(c);  //rvalue ctor
                    assert(d.useCount == 2);
                }

                {
                    import core.lifetime : move;
                    auto u = UniquePtr!(long, DefaultSharedControlBlock).make(123);

                    SharedPtr!long s = move(u);        //rvalue copy ctor
                    assert(s != null);
                    assert(s.useCount == 1);

                    SharedPtr!long s2 = UniquePtr!(long, DefaultSharedControlBlock).init;
                    assert(s2 == null);
                }

                {
                    import core.lifetime : move;
                    auto rc = RcPtr!(long).make(123);
                    assert(rc.useCount == 1);

                    SharedPtr!long s = rc;
                    assert(s != null);
                    assert(s.useCount == 2);
                    assert(rc.useCount == 2);

                    SharedPtr!long s2 = RcPtr!(long).init;
                    assert(s2 == null);
                }
                --------------------
        */
        public this(Rhs, this This)(ref scope Rhs rhs)@trusted
        if(true
            && isSharedPtr!Rhs
            && !is(Unqual!This == Unqual!Rhs)   ///copy ctors
            && isConstructable!(Rhs, This)
            && !needLock!(Rhs, This)
            && !is(Rhs == shared)
        ){
            mixin validateSharedPtr!(This, Rhs);

            this(rhs, rhs._element);
        }

        /// ditto
        public this(Rhs, this This)(scope Rhs rhs)@trusted
        if(true
            && isSharedPtr!Rhs
            //&& !is(Unqual!This == Unqual!Rhs) //TODO move ctors need this
            && isConstructable!(Rhs, This)
            && !needLock!(Rhs, This)
            && !is(Rhs == shared)
        ){
            mixin validateSharedPtr!(This, Rhs);

            auto element = rhs._element;
            this(rhs.move, element);
        }

        /// ditto
        public this(Rhs, this This)(auto ref scope Rhs rhs)@trusted
        if(true
            && isSharedPtr!Rhs
            && isConstructable!(Rhs, This)
            && needLock!(Rhs, This)
            && !is(Rhs == shared)
        ){
            mixin validateSharedPtr!(This, Rhs);

            if(rhs._control !is null && rhs._control.add_shared_if_exists()){
                this._control = cast(typeof(this._control))rhs._control;
                this._element = rhs._element;
            }
            else{
                this._control = null;
                this._element = null;
            }
        }

        /// ditto
        public this(Rhs, this This)(scope Rhs rhs)@trusted
        if(true
            && isUniquePtr!Rhs
            && isConstructable!(Rhs, This)
            && !is(Rhs == shared)
        ){
            import autoptr.unique_ptr : validateUniquePtr;
            mixin validateSharedPtr!This;
            mixin validateUniquePtr!Rhs;

            if(rhs == null){
                this(null);
            }
            else{
                this(rhs._control, rhs.element);
                rhs._const_reset();
            }
        }

        /// ditto
        public this(Rhs, this This)(scope Rhs rhs)@trusted
        if(true
            && isRcPtr!Rhs
            && isConstructable!(Rhs, This)
            && !is(Rhs == shared)
        ){
            import autoptr.rc_ptr : validateRcPtr;
            mixin validateSharedPtr!This;
            mixin validateRcPtr!Rhs;

            if(rhs == null){
                this(null);
            }
            else{
                this(rhs._control, rhs.element);
                rhs._const_reset();
            }
        }



        //copy ctors:
        //mutable:
        static if(is(Unqual!ElementType == ElementType)){
            //mutable rhs:
			this(ref scope typeof(this) rhs)@trusted{this(rhs, rhs._element);}
			this(ref scope typeof(this) rhs)const @trusted{this(rhs, rhs._element);}
			@disable this(ref scope typeof(this) rhs)immutable @safe;
            @disable this(ref scope typeof(this) rhs)shared @safe;
			@disable this(ref scope typeof(this) rhs)const shared @safe;

            //const rhs:
			@disable this(ref scope const typeof(this) rhs)@safe;
            this(ref scope const typeof(this) rhs)const @trusted{this(rhs, rhs._element);}
			@disable this(ref scope const typeof(this) rhs)immutable @safe;
            @disable this(ref scope const typeof(this) rhs)shared @safe;
			@disable this(ref scope const typeof(this) rhs)const shared @safe;

            //immutable(Ptr) iptr;
            @disable this(ref scope immutable typeof(this) rhs)@safe;
            this(ref scope immutable typeof(this) rhs)const @trusted{this(rhs, rhs._element);}
            this(ref scope immutable typeof(this) rhs)immutable @trusted{this(rhs, rhs._element);}
            @disable this(ref scope immutable typeof(this) rhs)shared @safe;
            static if(is(ControlType == shared))
                this(ref scope immutable typeof(this) rhs)const shared @trusted{this(rhs, rhs._element);}
            else
                @disable this(ref scope immutable typeof(this) rhs)const shared @safe;

        }
        //const:
        else static if(is(const Unqual!ElementType == ElementType)){
            //mutable rhs:
			this(ref scope typeof(this) rhs)@trusted{this(rhs, rhs._element);}
			this(ref scope typeof(this) rhs)const @trusted{this(rhs, rhs._element);}
			@disable this(ref scope typeof(this) rhs)immutable @safe;
            @disable this(ref scope typeof(this) rhs)shared @safe;
			@disable this(ref scope typeof(this) rhs)const shared @safe;

			//const rhs:
			this(ref scope const typeof(this) rhs)@trusted{this(rhs, rhs._element);}
            this(ref scope const typeof(this) rhs)const @trusted{this(rhs, rhs._element);}
			@disable this(ref scope const typeof(this) rhs)immutable @safe;
            @disable this(ref scope const typeof(this) rhs)shared @safe;
			@disable this(ref scope const typeof(this) rhs)const shared @safe;

            //immutable rhs:
            this(ref scope immutable typeof(this) rhs)@trusted{this(rhs, rhs._element);}
            this(ref scope immutable typeof(this) rhs)const @trusted{this(rhs, rhs._element);}
            this(ref scope immutable typeof(this) rhs)immutable @trusted{this(rhs, rhs._element);}
            static if(is(ControlType == shared)){
                this(ref scope immutable typeof(this) rhs)shared @trusted{this(rhs, rhs._element);}
                this(ref scope immutable typeof(this) rhs)const shared @trusted{this(rhs, rhs._element);}
            }
            else{
                @disable this(ref scope immutable typeof(this) rhs)shared @safe;
                @disable this(ref scope immutable typeof(this) rhs)const shared @safe;
            }
        }
        //immutable:
        else static if(is(immutable Unqual!ElementType == ElementType)){
			//mutable rhs:
			this(ref scope typeof(this) rhs)@trusted{this(rhs, rhs._element);}
			this(ref scope typeof(this) rhs)const @trusted{this(rhs, rhs._element);}
			this(ref scope typeof(this) rhs)immutable @trusted{this(rhs, rhs._element);}
            static if(is(ControlType == shared)){
                this(ref scope typeof(this) rhs)shared @trusted{this(rhs, rhs._element);}
                this(ref scope typeof(this) rhs)const shared @trusted{this(rhs, rhs._element);}
            }
            else{
                @disable this(ref scope typeof(this) rhs)shared @safe;
                @disable this(ref scope typeof(this) rhs)const shared @safe;
            }

            //const rhs:
			this(ref scope const typeof(this) rhs)@trusted{this(rhs, rhs._element);}
			this(ref scope const typeof(this) rhs)const @trusted{this(rhs, rhs._element);}
			this(ref scope const typeof(this) rhs)immutable @trusted{this(rhs, rhs._element);}	//??
            static if(is(ControlType == shared)){
                this(ref scope const typeof(this) rhs)shared @trusted{this(rhs, rhs._element);}
                this(ref scope const typeof(this) rhs)const shared @trusted{this(rhs, rhs._element);}
            }
            else{
                @disable this(ref scope const typeof(this) rhs)shared @safe;
                @disable this(ref scope const typeof(this) rhs)const shared @safe;
            }

			//immutable rhs:
			this(ref scope immutable typeof(this) rhs)@trusted{this(rhs, rhs._element);}	//??
			this(ref scope immutable typeof(this) rhs)const @trusted{this(rhs, rhs._element);}
			this(ref scope immutable typeof(this) rhs)immutable @trusted{this(rhs, rhs._element);}
            static if(is(ControlType == shared)){
                this(ref scope immutable typeof(this) rhs)shared @trusted{this(rhs, rhs._element);}
                this(ref scope immutable typeof(this) rhs)const shared @trusted{this(rhs, rhs._element);}
            }
            else{
                @disable this(ref scope immutable typeof(this) rhs)shared @safe;
                @disable this(ref scope immutable typeof(this) rhs)const shared @safe;
            }
        }
        //shared:
        else static if(is(shared Unqual!ElementType == ElementType)){
            //static assert(!threadLocal);

			//mutable rhs:
			this(ref scope typeof(this) rhs)@trusted{this(rhs, rhs._element);}
			this(ref scope typeof(this) rhs)const @trusted{this(rhs, rhs._element);}
			@disable this(ref scope typeof(this) rhs)immutable @safe;
            static if(is(ControlType == shared)){
                this(ref scope typeof(this) rhs)shared @trusted{this(rhs, rhs._element);}
			    this(ref scope typeof(this) rhs)const shared @trusted{this(rhs, rhs._element);}
            }
            else{
                @disable this(ref scope typeof(this) rhs)shared @safe;
                @disable this(ref scope typeof(this) rhs)const shared @safe;
            }
			
            //const rhs:
			@disable this(ref scope const typeof(this) rhs)@safe;
			this(ref scope const typeof(this) rhs)const @trusted{this(rhs, rhs._element);}
			@disable this(ref scope const typeof(this) rhs)immutable @safe;
            @disable this(ref scope const typeof(this) rhs)shared @safe;
            static if(is(ControlType == shared))
                this(ref scope const typeof(this) rhs)const shared @trusted{this(rhs, rhs._element);}
            else
                @disable this(ref scope const typeof(this) rhs)const shared @safe;
			
			//immutable rhs:
			@disable this(ref scope immutable typeof(this) rhs)@safe;
			this(ref scope immutable typeof(this) rhs)const @trusted{this(rhs, rhs._element);}
			this(ref scope immutable typeof(this) rhs)immutable @trusted{this(rhs, rhs._element);}
            @disable this(ref scope immutable typeof(this) rhs)shared @safe;
            static if(is(ControlType == shared))
			    this(ref scope immutable typeof(this) rhs)const shared @trusted{this(rhs, rhs._element);}
            else
                @disable this(ref scope immutable typeof(this) rhs)const shared @safe;
        }
		//shared const:
        else static if(is(const shared Unqual!ElementType == ElementType)){
            //static assert(!threadLocal);

			//mutable rhs:
			this(ref scope typeof(this) rhs)@trusted{this(rhs, rhs._element);}
			this(ref scope typeof(this) rhs)const @trusted{this(rhs, rhs._element);}
			@disable this(ref scope typeof(this) rhs)immutable @safe;
            static if(is(ControlType == shared)){
                this(ref scope typeof(this) rhs)shared @trusted{this(rhs, rhs._element);}
			    this(ref scope typeof(this) rhs)const shared @trusted{this(rhs, rhs._element);}
            }
            else{
                @disable this(ref scope typeof(this) rhs)shared @safe;
                @disable this(ref scope typeof(this) rhs)const shared @safe;
            }

            //const rhs:
			this(ref scope const typeof(this) rhs)@trusted{this(rhs, rhs._element);}
			this(ref scope const typeof(this) rhs)const @trusted{this(rhs, rhs._element);}
			@disable this(ref scope const typeof(this) rhs)immutable @safe;
            static if(is(ControlType == shared)){
                this(ref scope const typeof(this) rhs)shared @trusted{this(rhs, rhs._element);}
			    this(ref scope const typeof(this) rhs)const shared @trusted{this(rhs, rhs._element);}
            }
            else{
                @disable this(ref scope const typeof(this) rhs)shared @safe;
                @disable this(ref scope const typeof(this) rhs)const shared @safe;
            }
			
			//immutable rhs:
			this(ref scope immutable typeof(this) rhs)@trusted{this(rhs, rhs._element);}	//??
			this(ref scope immutable typeof(this) rhs)const @trusted{this(rhs, rhs._element);}
			this(ref scope immutable typeof(this) rhs)immutable @trusted{this(rhs, rhs._element);}
            static if(is(ControlType == shared)){
                this(ref scope immutable typeof(this) rhs)shared @trusted{this(rhs, rhs._element);}
			    this(ref scope immutable typeof(this) rhs)const shared @trusted{this(rhs, rhs._element);}
            }
            else{
                @disable this(ref scope immutable typeof(this) rhs)shared @safe;
                @disable this(ref scope immutable typeof(this) rhs)const shared @safe;
            }

        }
		else static assert(0, "no impl");

        //shared rhs:
        @disable this(ref scope shared typeof(this) rhs)@safe;
        @disable this(ref scope shared typeof(this) rhs)const @safe;
        @disable this(ref scope shared typeof(this) rhs)immutable @safe;
        @disable this(ref scope shared typeof(this) rhs)shared @safe;
        @disable this(ref scope shared typeof(this) rhs)const shared @safe;

        //const shared rhs:
        @disable this(ref scope const shared typeof(this) rhs)@safe;
        @disable this(ref scope const shared typeof(this) rhs)const @safe;
        @disable this(ref scope const shared typeof(this) rhs)immutable @safe;
        @disable this(ref scope const shared typeof(this) rhs)shared @safe;
        @disable this(ref scope const shared typeof(this) rhs)const shared @safe;



        /**
            Releases the ownership of the managed object, if any.

            After the call, this manages no object.

            Examples:
                --------------------
                {
                    SharedPtr!long x = SharedPtr!long.make(1);

                    assert(x.useCount == 1);
                    x = null;
                    assert(x.useCount == 0);
                    assert(x == null);
                }

                {
                    SharedPtr!(shared long) x = SharedPtr!(shared long).make(1);

                    assert(x.useCount == 1);
                    x = null;
                    assert(x.useCount == 0);
                    assert(x == null);
                }

                {
                    shared SharedPtr!(long).ThreadLocal!false x = SharedPtr!(shared long).ThreadLocal!false.make(1);

                    assert(x.useCount == 1);
                    x = null;
                    assert(x.useCount == 0);
                    assert(x == null);
                }
                --------------------
        */
        public void opAssign(MemoryOrder order = MemoryOrder.seq, this This)(typeof(null) nil)scope
        if(isMutable!This){
            static if(is(This == shared)){
                this.lockSharedPtr!(
                    (ref scope self) => self.opAssign!order(null)
                )();
            }
            else{
                this._release();
                this._reset();
            }
        }

        /**
            Shares ownership of the object managed by `rhs`.

            If `rhs` manages no object, `this` manages no object too.
            If `rhs` is rvalue then move-assigns a `SharedPtr` from `rhs`

            Examples:
                --------------------
                {
                    SharedPtr!long px1 = SharedPtr!long.make(1);
                    SharedPtr!long px2 = SharedPtr!long.make(2);

                    assert(px2.useCount == 1);
                    px1 = px2;
                    assert(*px1 == 2);
                    assert(px2.useCount == 2);
                }


                {
                    SharedPtr!long px = SharedPtr!long.make(1);
                    SharedPtr!(const long) pcx = SharedPtr!long.make(2);

                    assert(px.useCount == 1);
                    pcx = px;
                    assert(*pcx == 1);
                    assert(pcx.useCount == 2);

                }


                {
                    const SharedPtr!long cpx = SharedPtr!long.make(1);
                    SharedPtr!(const long) pcx = SharedPtr!long.make(2);

                    assert(pcx.useCount == 1);
                    pcx = cpx;
                    assert(*pcx == 1);
                    assert(pcx.useCount == 2);

                }

                {
                    SharedPtr!(immutable long) pix = SharedPtr!(immutable long).make(123);
                    SharedPtr!(const long) pcx = SharedPtr!long.make(2);

                    assert(pix.useCount == 1);
                    pcx = pix;
                    assert(*pcx == 123);
                    assert(pcx.useCount == 2);

                }
                --------------------
        */
        public void opAssign(MemoryOrder order = MemoryOrder.seq, Rhs, this This)(ref scope Rhs desired)scope
        if(true
            && isSharedPtr!Rhs
            && isAssignable!(Rhs, This)
            && !needLock!(Rhs, This)
            && !is(Rhs == shared)
        ){
            mixin validateSharedPtr!(Rhs, This);

            if((()@trusted => cast(const void*)&desired is cast(const void*)&this)())
                return;

            static if(is(This == shared)){
                this.lockSharedPtr!(
                    (ref scope self, ref scope Rhs x) => self.opAssign!order(x)
                )(desired);
            }
            else{
                this._release();
                ()@trusted{
                    auto control = this._control = cast(typeof(this._control))desired._control;
                    this._set_element(desired._element);

                    if(control !is null)
                        this._control.add!weakPtr;

                }();
            }
        }

        ///ditto
        public void opAssign(MemoryOrder order = MemoryOrder.seq, Rhs, this This)(scope Rhs desired)scope
        if(true
            && isSharedPtr!Rhs
            && isAssignable!(Rhs, This)
            && !needLock!(Rhs, This)
            && !is(Rhs == shared)
        ){
            mixin validateSharedPtr!(Rhs, This);

            static if(is(This == shared)){
                this.lockSharedPtr!(
                    (ref scope self, scope Rhs x) => self.opAssign!order(x.move)
                )(desired.move);
            }
            else{

                this._release();

                ()@trusted{
                    this._control = cast(typeof(this._control))desired._control;
                    this._set_element(desired._element);

                    desired._const_set_counter(null);
                    //desired._const_set_element(null);

                }();

            }
        }



        /**
            Constructs an object of type `ElementType` and wraps it in a `SharedPtr` using args as the parameter list for the constructor of `ElementType`.

            The object is constructed as if by the expression `emplace!ElementType(_payload, forward!args)`, where _payload is an internal pointer to storage suitable to hold an object of type `ElementType`.
            The storage is typically larger than `ElementType.sizeof` in order to use one allocation for both the control block and the `ElementType` object.

            Examples:
                --------------------
                {
                    SharedPtr!long a = SharedPtr!long.make();
                    assert(a.get == 0);

                    SharedPtr!(const long) b = SharedPtr!long.make(2);
                    assert(b.get == 2);
                }

                {
                    static struct Struct{
                        int i = 7;

                        this(int i)pure nothrow @safe @nogc{
                            this.i = i;
                        }
                    }

                    SharedPtr!Struct s1 = SharedPtr!Struct.make();
                    assert(s1.get.i == 7);

                    SharedPtr!Struct s2 = SharedPtr!Struct.make(123);
                    assert(s2.get.i == 123);
                }

                {
                    static interface Interface{
                    }
                    static class Class : Interface{
                        int i;

                        this(int i)pure nothrow @safe @nogc{
                            this.i = i;
                        }
                    }

                    SharedPtr!Interface x = SharedPtr!Class.make(3);
                    //assert(x.dynTo!Class.get.i == 3);
                }
                --------------------
        */
        static if(!weakPtr)
        public static SharedPtr make
            (AllocatorType = DefaultAllocator, bool supportGC = platformSupportGC, Args...)
            (auto ref Args args)
        if(stateSize!AllocatorType == 0 && !isDynamicArray!ElementType){
            static assert(!weakPtr);

            import core.lifetime : forward;

            auto m = MakeEmplace!(AllocatorType, supportGC).make(forward!(args));

            if(m is null)
                return typeof(return).init;


            auto ptr = typeof(this).init;

            ptr._control = m.base;
            ptr._set_element(m.get);

            return ptr.move;
        }

        /**
            Constructs a `SharedPtr` with `element` as the pointer to the managed object.

            Uses the specified `deleter` as the deleter. The expression `deleter(element)` must be well formed, have well-defined behavior and not throw any exceptions.
            The construction of `deleter` and of the stored deleter from d must not throw exceptions.

            Examples:
                --------------------
                long deleted = -1;
                auto x = SharedPtr!long.make(new long(123), (long* data){
                    deleted = *data;
                });
                assert(deleted == -1);
                assert(*x == 123);

                x = null;
                assert(deleted == 123);
                --------------------
        */
        static if(!weakPtr)
        public static SharedPtr make
            (AllocatorType = DefaultAllocator, bool supportGC = platformSupportGC, DeleterType)
            (ElementReferenceType element, DeleterType deleter)
        if(stateSize!AllocatorType == 0 && isCallable!DeleterType){
            static assert(!weakPtr);

            import core.lifetime : forward;

            auto m = MakeDeleter!(DeleterType, AllocatorType, supportGC).make(forward!(element, deleter));

            if(m is null)
                return typeof(return).init;


            auto ptr = typeof(this).init;

            ptr._control = m.base;
            ptr._set_element(m.get);

            return ptr.move;
        }


        /**
            Constructs an object of array type `ElementType` including its array elements and wraps it in a `SharedPtr`.

            Parameters:
                n = Array length

                args = parameters for constructor for each array element.

            The array elements are constructed as if by the expression `emplace!ElementType(_payload, args)`, where _payload is an internal pointer to storage suitable to hold an object of type `ElementType`.
            The storage is typically larger than `ElementType.sizeof * n` in order to use one allocation for both the control block and the each array element.

            Examples:
                --------------------
                auto arr = SharedPtr!(long[]).make(6, -1);
                assert(arr.length == 6);
                assert(arr.get.length == 6);

                import std.algorithm : all;
                assert(arr.get.all!(x => x == -1));

                for(long i = 0; i < 6; ++i)
                    arr.get[i] = i;

                assert(arr.get == [0, 1, 2, 3, 4, 5]);
                --------------------
        */
        static if(!weakPtr)
        public static SharedPtr make
            (AllocatorType = DefaultAllocator, bool supportGC = platformSupportGC, Args...)
            (const size_t n, auto ref Args args)
        if(stateSize!AllocatorType == 0 && isDynamicArray!ElementType){
            static assert(!weakPtr);

            import core.lifetime : forward;

            auto m = MakeDynamicArray!(AllocatorType, supportGC).make(n, forward!(args));

            if(m is null)
                return typeof(return).init;

            auto ptr = typeof(this).init;

            ptr._control = m.base;
            ptr._set_element(m.get);

            return ()@trusted{
                return ptr.move;
            }();
        }



        /**
            Constructs an object of type `ElementType` and wraps it in a `SharedPtr` using args as the parameter list for the constructor of `ElementType`.

            The object is constructed as if by the expression `emplace!ElementType(_payload, forward!args)`, where _payload is an internal pointer to storage suitable to hold an object of type `ElementType`.
            The storage is typically larger than `ElementType.sizeof` in order to use one allocation for both the control block and the `ElementType` object.

            Examples:
                --------------------
                auto a = allocatorObject(Mallocator.instance);
                {
                    SharedPtr!long a = SharedPtr!long.alloc(a);
                    assert(a.get == 0);

                    SharedPtr!(const long) b = SharedPtr!long.alloc(a, 2);
                    assert(b.get == 2);
                }

                {
                    static struct Struct{
                        int i = 7;

                        this(int i)pure nothrow @safe @nogc{
                            this.i = i;
                        }
                    }

                    SharedPtr!Struct s1 = SharedPtr!Struct.alloc(a);
                    assert(s1.get.i == 7);

                    SharedPtr!Struct s2 = SharedPtr!Struct.alloc(a, 123);
                    assert(s2.get.i == 123);
                }

                {
                    static interface Interface{
                    }
                    static class Class : Interface{
                        int i;

                        this(int i)pure nothrow @safe @nogc{
                            this.i = i;
                        }
                    }

                    SharedPtr!Interface x = SharedPtr!Class.alloc(a, 3);
                    //assert(x.dynTo!Class.get.i == 3);
                }
                --------------------
        */
        static if(!weakPtr)
        public static SharedPtr alloc
            (AllocatorType, bool supportGC = platformSupportGC, Args...)
            (AllocatorType a, auto ref Args args)
        if(stateSize!AllocatorType >= 0 && !isDynamicArray!ElementType){
            static assert(!weakPtr);

            import core.lifetime : forward;

            auto m = MakeEmplace!(AllocatorType, supportGC).make(forward!(a, args));

            if(m is null)
                return typeof(return).init;

            auto ptr = typeof(this).init;

            ptr._control = m.base;
            ptr._set_element(m.get);

            return ptr.move;
        }


        /**
            Constructs a `SharedPtr` with `element` as the pointer to the managed object using `allocator` with state.

            Uses the specified `deleter` as the deleter. The expression `deleter(element)` must be well formed, have well-defined behavior and not throw any exceptions.
            The construction of `deleter` and of the stored deleter from d must not throw exceptions.

            Examples:
                --------------------
                auto a = allocatorObject(Mallocator.instance);

                long deleted = -1;
                auto x = SharedPtr!long.make(new long(123), (long* data){
                    deleted = *data;
                }, a);
                assert(deleted == -1);
                assert(*x == 123);

                x = null;
                assert(deleted == 123);
                --------------------
        */
        static if(!weakPtr)
        public static SharedPtr alloc
            (AllocatorType, bool supportGC = platformSupportGC, DeleterType)
            (AllocatorType allocator, ElementReferenceType element, DeleterType deleter)
        if(stateSize!AllocatorType >= 0 && isCallable!DeleterType){
            static assert(!weakPtr);

            import core.lifetime : forward;

            auto m = MakeDeleter!(DeleterType, AllocatorType, supportGC).make(forward!(element, deleter, allocator));

            if(m is null)
                return typeof(return).init;

            auto ptr = typeof(this).init;

            ptr._control = m.base;
            ptr._set_element(m.get);

            return ptr.move;
        }



        /**
            Constructs an object of array type `ElementType` including its array elements and wraps it in a `SharedPtr`.

            Parameters:
                n = Array length

                args = parameters for constructor for each array element.

            The array elements are constructed as if by the expression `emplace!ElementType(_payload, args)`, where _payload is an internal pointer to storage suitable to hold an object of type `ElementType`.
            The storage is typically larger than `ElementType.sizeof * n` in order to use one allocation for both the control block and the each array element.

            Examples:
                --------------------
                auto a = allocatorObject(Mallocator.instance);
                auto arr = SharedPtr!(long[], DestructorType!(typeof(a))).alloc(a, 6, -1);
                assert(arr.length == 6);
                assert(arr.get.length == 6);

                import std.algorithm : all;
                assert(arr.get.all!(x => x == -1));

                for(long i = 0; i < 6; ++i)
                    arr.get[i] = i;

                assert(arr.get == [0, 1, 2, 3, 4, 5]);
                --------------------
        */
        static if(!weakPtr)
        public static SharedPtr alloc
            (AllocatorType, bool supportGC = platformSupportGC, Args...)
            (AllocatorType a, const size_t n, auto ref Args args)
        if(stateSize!AllocatorType >= 0 && isDynamicArray!ElementType){
            static assert(!weakPtr);

            import core.lifetime : forward;

            auto m = MakeDynamicArray!(AllocatorType, supportGC).make(forward!(a, n, args));

            if(m is null)
                return typeof(return).init;

            auto ptr = typeof(this).init;

            ptr._control = m.base;
            ptr._set_element(m.get);

            return ptr.move;
        }



        /**
            Returns the number of different `SharedPtr` instances

            Returns the number of different `SharedPtr` instances (`this` included) managing the current object or `0` if there is no managed object.

            Examples:
                --------------------
                SharedPtr!long x = null;

                assert(x.useCount == 0);

                x = SharedPtr!long.make(123);
                assert(x.useCount == 1);

                auto y = x;
                assert(x.useCount == 2);

                auto w1 = x.weak;    //weak ptr
                assert(x.useCount == 2);

                SharedPtr!long.WeakType w2 = x;   //weak ptr
                assert(x.useCount == 2);

                y = null;
                assert(x.useCount == 1);

                x = null;
                assert(x.useCount == 0);
                assert(w1.useCount == 0);
                --------------------
        */
        public @property ControlType.Shared useCount(this This)()const scope nothrow @trusted @nogc{
            mixin validateSharedPtr!This;

            static if(is(This == shared)){
                static assert(is(ControlType == shared));

                return this.lockSharedPtr!(
                    (ref scope return self) => self.useCount()
                )();
            }
            else{
                const ControlType* control = this._control;
                    
                return (control is null)
                    ? 0
                    : control.count!false + 1;
            }

        }


        /**
            Returns the number of different `WeakPtr` instances

            Returns the number of different `WeakPtr` instances (`this` included) managing the current object or `0` if there is no managed object.

            Examples:
                --------------------
                SharedPtr!long x = null;
                assert(x.useCount == 0);
                assert(x.weakCount == 0);

                x = SharedPtr!long.make(123);
                assert(x.useCount == 1);
                assert(x.weakCount == 0);

                auto w = x.weak();
                assert(x.useCount == 1);
                assert(x.weakCount == 1);
                --------------------
        */
        public @property ControlType.Weak weakCount(this This)()const scope nothrow @safe @nogc{
            mixin validateSharedPtr!This;

            static if(is(This == shared)){
                static assert(is(ControlType == shared));

                return this.lockSharedPtr!(
                    (ref scope return self) => self.weakCount()
                )();
            }
            else{
                const ControlType* control = this._control;
                
                return (control is null)
                    ? 0
                    : control.count!true;
            }

        }



        /**
            Swap `this` with `rhs`

            Examples:
                --------------------
                {
                    SharedPtr!long a = SharedPtr!long.make(1);
                    SharedPtr!long b = SharedPtr!long.make(2);
                    a.proxySwap(b);
                    assert(*a == 2);
                    assert(*b == 1);
                    import std.algorithm : swap;
                    swap(a, b);
                    assert(*a == 1);
                    assert(*b == 2);
                    assert(a.useCount == 1);
                    assert(b.useCount == 1);
                }
                --------------------
        */
        public void proxySwap(ref scope typeof(this) rhs)scope @trusted pure nothrow @nogc{
            auto control = this._control;
            auto element = this._element;

            this._control = rhs._control;
            this._set_element(rhs._element);

            rhs._control = control;
            rhs._set_element(element);
        }



        /**
            Returns the non `shared` `SharedPtr` pointer pointed-to by `shared` `this`.

            Examples:
                --------------------
                shared SharedPtr!(long).ThreadLocal!false x = SharedPtr!(shared long).ThreadLocal!false.make(123);

                {
                    SharedPtr!(shared long) y = x.load();
                    assert(y.useCount == 2);

                    assert(y.get == 123);
                }
                --------------------
        */
        public auto load(MemoryOrder order = MemoryOrder.seq, this This)()scope return{
            mixin validateSharedPtr!This;

            static if(is(This == shared)){
                static assert(is(ControlType == shared));

                return this.lockSharedPtr!(
                    (ref scope return self) => self.load!order()
                )();
            }
            else{
                alias Result = ChangeElementType!(
                    This,
                    CopyTypeQualifiers!(This, ElementType)
                );

                return Result(this);
            }
        }



        /**
            Stores the non `shared` `SharedPtr` parameter `ptr` to `this`.

            If `this` is shared then operation is atomic or guarded by mutex.

            Template parameter `order` has type `core.atomic.MemoryOrder`.

            Examples:
                --------------------
                //null store:
                {
                    shared x = SharedPtr!(shared long).make(123);
                    assert(x.load.get == 123);

                    x.store(null);
                    assert(x.useCount == 0);
                    assert(x.load == null);
                }

                //rvalue store:
                {
                    shared x = SharedPtr!(shared long).make(123);
                    assert(x.load.get == 123);

                    x.store(SharedPtr!(shared long).make(42));
                    assert(x.load.get == 42);
                }

                //lvalue store:
                {
                    shared x = SharedPtr!(shared long).make(123);
                    auto y = SharedPtr!(shared long).make(42);

                    assert(x.load.get == 123);
                    assert(y.load.get == 42);

                    x.store(y);
                    assert(x.load.get == 42);
                    assert(x.useCount == 2);
                }
                --------------------
        */
        public void store(MemoryOrder order = MemoryOrder.seq, this This)(typeof(null) nil)scope
        if(isMutable!This){
            mixin validateSharedPtr!(This);

            this.opAssign!order(null);
        }

        /// ditto
        public void store(MemoryOrder order = MemoryOrder.seq, Ptr, this This)(auto ref scope Ptr desired)scope
        if(true
            && isSharedPtr!Ptr 
            && !is(Ptr == shared) 
            && !needLock!(Ptr, This)
            && isAssignable!(Ptr, This)
        ){
            mixin validateSharedPtr!(Ptr, This);

            import core.lifetime : forward;
            this.opAssign!order(forward!desired);
        }



        /**
            Stores the non `shared` `SharedPtr` pointer ptr in the `shared(SharedPtr)` pointed to by `this` and returns the value formerly pointed-to by this, atomically or with mutex.

            Examples:
                --------------------
                //lvalue exchange
                {
                    shared x = SharedPtr!(shared long).make(123);
                    auto y = SharedPtr!(shared long).make(42);

                    auto z = x.exchange(y);

                    assert(x.load.get == 42);
                    assert(y.get == 42);
                    assert(z.get == 123);
                }

                //rvalue exchange
                {
                    shared x = SharedPtr!(shared long).make(123);
                    auto y = SharedPtr!(shared long).make(42);

                    auto z = x.exchange(y.move);

                    assert(x.load.get == 42);
                    assert(y == null);
                    assert(z.get == 123);
                }

                //null exchange (same as move)
                {
                    shared x = SharedPtr!(shared long).make(123);

                    auto z = x.exchange(null);

                    assert(x.load == null);
                    assert(z.get == 123);
                }

                //swap:
                {
                    shared x = SharedPtr!(shared long).make(123);
                    auto y = SharedPtr!(shared long).make(42);

                    //opAssign is same as store
                    y = x.exchange(y.move);

                    assert(x.load.get == 42);
                    assert(y.get == 123);
                }
                --------------------
        */
        public auto exchange(MemoryOrder order = MemoryOrder.seq, this This)(typeof(null))scope
        if(isMutable!This){
            mixin validateSharedPtr!This;

            static if(is(This == shared))
                return this.lockSharedPtr!(
                    (ref scope self) => self.exchange!order(null)
                )();
            else{
                return this.move;
            }
        }

        /// ditto
        public auto exchange(MemoryOrder order = MemoryOrder.seq, Ptr, this This)(Ptr ptr)scope
        if(isSharedPtr!Ptr && !is(Ptr == shared) && isAssignable!(Ptr, This)){
            mixin validateSharedPtr!(Ptr, This);

            static if(is(This == shared))
                return this.lockSharedPtr!(
                    (ref scope self, Ptr x) => self.exchange!order(x.move)
                )(ptr.move);
            else{
                auto result = this.move;

                return()@trusted{
                    this = ptr.move;
                    return result.move;
                }();
            }
        }


        /**
            Compares the `SharedPtr` pointers pointed-to by `this` and `expected`.

            If they are equivalent (store the same pointer value, and either share ownership of the same object or are both empty), assigns `desired` into `this` using the memory ordering constraints specified by `success` and returns `true`.
            If they are not equivalent, assigns `this` into `expected` using the memory ordering constraints specified by `failure` and returns `false`.

            More info in c++ std::atomic<std::shared_ptr>.

            Examples:
                --------------------
                static foreach(enum bool weak; [true, false]){
                    //fail
                    {
                        SharedPtr!long a = SharedPtr!long.make(123);
                        SharedPtr!long b = SharedPtr!long.make(42);
                        SharedPtr!long c = SharedPtr!long.make(666);

                        static if(weak)a.compareExchangeWeak(b, c);
                        else a.compareExchangeStrong(b, c);

                        assert(*a == 123);
                        assert(*b == 123);
                        assert(*c == 666);

                    }

                    //success
                    {
                        SharedPtr!long a = SharedPtr!long.make(123);
                        SharedPtr!long b = a;
                        SharedPtr!long c = SharedPtr!long.make(666);

                        static if(weak)a.compareExchangeWeak(b, c);
                        else a.compareExchangeStrong(b, c);

                        assert(*a == 666);
                        assert(*b == 123);
                        assert(*c == 666);
                    }

                    //shared fail
                    {
                        shared SharedPtr!(shared long) a = SharedPtr!(shared long).make(123);
                        SharedPtr!(shared long) b = SharedPtr!(shared long).make(42);
                        SharedPtr!(shared long) c = SharedPtr!(shared long).make(666);

                        static if(weak)a.compareExchangeWeak(b, c);
                        else a.compareExchangeStrong(b, c);

                        auto tmp = a.exchange(null);
                        assert(*tmp == 123);
                        assert(*b == 123);
                        assert(*c == 666);
                    }

                    //shared success
                    {
                        SharedPtr!(shared long) b = SharedPtr!(shared long).make(123);
                        shared SharedPtr!(shared long) a = b;
                        SharedPtr!(shared long) c = SharedPtr!(shared long).make(666);

                        static if(weak)a.compareExchangeWeak(b, c);
                        else a.compareExchangeStrong(b, c);

                        auto tmp = a.exchange(null);
                        assert(*tmp == 666);
                        assert(*b == 123);
                        assert(*c == 666);
                    }
                }
                --------------------
        */
        public bool compareExchangeStrong
            (MemoryOrder success = MemoryOrder.seq, MemoryOrder failure = success, E, D, this This)
            (ref scope E expected, scope D desired)scope
        if(true
            && isSharedPtr!E && !is(E == shared) 
            && isSharedPtr!D && !is(D == shared) 
            && isAssignable!(D, This)
            && isAssignable!(This, E)
        ){
            mixin validateSharedPtr!(E, D, This);

            return this.compareExchange!(success, failure)(expected, desired.move);
        }



        /**
            Same as `compareExchangeStrong` but may fail spuriously.

            More info in c++ `std::atomic<std::shared_ptr>`.
        */
        public bool compareExchangeWeak
            (MemoryOrder success = MemoryOrder.seq, MemoryOrder failure = success, E, D, this This)
            (ref scope E expected, scope D desired)scope
        if(true
            && isSharedPtr!E && !is(E == shared) 
            && isSharedPtr!D && !is(D == shared) 
            && isAssignable!(D, This)
            && isAssignable!(This, E)
        ){
            mixin validateSharedPtr!(E, D, This);

            return this.compareExchange!(success, failure)(expected, desired.move);
        }



        /*
            implementation of `compareExchangeWeak` and `compareExchangeStrong`
        */
        private bool compareExchange
            (MemoryOrder success = MemoryOrder.seq, MemoryOrder failure = success, E, D, this This)
            (ref scope E expected, scope D desired)scope @trusted
        if(true
            && isSharedPtr!E && !is(E == shared) 
            && isSharedPtr!D && !is(D == shared) 
            && isAssignable!(D, This)
            && isAssignable!(This, E)
        ){
            mixin validateSharedPtr!(E, D, This);

            static if(is(This == shared)){
                import autoptr.internal.mutex : getMutex;

                shared mutex = getMutex(this);

                mutex.lock();

                alias Self = ChangeElementType!(
                    This, //CopyConstness!(This, Unqual!This),
                    CopyTypeQualifiers!(This, ElementType)
                );

                static assert(!is(Self == shared));

                Self* self = cast(Self*)&this;

                if(*self == expected){
                    auto tmp = self.move;   //destructor is called after  mutex.unlock();
                    *self = desired.move;

                    mutex.unlock();
                    return true;
                }

                auto tmp = expected.move;   //destructor is called after  mutex.unlock();
                expected = *self;

                mutex.unlock();
                return false;
            }
            else{
                if(this == expected){
                    this = desired.move;

                    return true;
                }
                expected = this;

                return false;
            }
        }



        /**
            Creates a new non weak `SharedPtr` that shares ownership of the managed object (must be `WeakPtr`).

            If there is no managed object, i.e. this is empty or this is `expired`, then the returned `SharedPtr` is empty.
            Method exists only if `SharedPtr` is `weakPtr`

            Examples:
                --------------------
                {
                    SharedPtr!long x = SharedPtr!long.make(123);

                    auto w = x.weak;    //weak ptr

                    SharedPtr!long y = w.lock;

                    assert(x == y);
                    assert(x.useCount == 2);
                    assert(y.get == 123);
                }

                {
                    SharedPtr!long x = SharedPtr!long.make(123);

                    auto w = x.weak;    //weak ptr

                    assert(w.expired == false);

                    x = SharedPtr!long.make(321);

                    assert(w.expired == true);

                    SharedPtr!long y = w.lock;

                    assert(y == null);
                }
                --------------------
        */
        static if(weakPtr)
        public CopyConstness!(This, SharedType) lock(this This)()scope @trusted
        if(!is(This == shared)){
            mixin validateSharedPtr!This;

            static assert(needLock!(This, typeof(return)));

            return typeof(return)(this);
        }



        /**
            Equivalent to `useCount() == 0` (must be `WeakPtr`).

            Method exists only if `SharedPtr` is `weakPtr`

            Examples:
                --------------------
                {
                    SharedPtr!long x = SharedPtr!long.make(123);

                    auto wx = x.weak;   //weak pointer

                    assert(wx.expired == false);

                    x = null;

                    assert(wx.expired == true);
                }
                --------------------
        */
        static if(weakPtr)
        public @property bool expired(this This)()scope const{
            mixin validateSharedPtr!This;
            return (this.useCount == 0);
        }


        static if(!weakPtr){
            /**
                Operator *, same as method 'get'.

                Examples:
                    --------------------
                    SharedPtr!long x = SharedPtr!long.make(123);
                    assert(*x == 123);
                    (*x = 321);
                    assert(*x == 321);
                    const y = x;
                    assert(*y == 321);
                    assert(*x == 321);
                    static assert(is(typeof(*y) == const long));
                    --------------------
            */
            public template opUnary(string op : "*")
            if(op == "*"){  //doc
                alias opUnary = get;
            }



            /**
                Get reference to managed object of `ElementType` or value if `ElementType` is reference type (class or interface) or dynamic array.

                Examples:
                    --------------------
                    SharedPtr!long x = SharedPtr!long.make(123);
                    assert(x.get == 123);
                    x.get = 321;
                    assert(x.get == 321);
                    const y = x;
                    assert(y.get == 321);
                    assert(x.get == 321);
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
                Get pointer to managed object of `ElementType` or reference if `ElementType` is reference type (class or interface) or dynamic array

                Examples:
                    --------------------
                    SharedPtr!long x = SharedPtr!long.make(123);
                    assert(*x.element == 123);
                    x.get = 321;
                    assert(*x.element == 321);
                    const y = x;
                    assert(*y.element == 321);
                    assert(*x.element == 321);
                    static assert(is(typeof(y.ptr) == const(long)*));
                    --------------------
            */
            public @property ElementReferenceTypeImpl!(inout ElementType) element()
            inout scope return pure nothrow @system @nogc{
                return this._element;
            }

        }



        /**
            Returns length of dynamic array (isDynamicArray!ElementType == true).

            Examples:
                --------------------
                auto x = SharedPtr!(int[]).make(10, -1);
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
            Returns weak pointer (must have weak counter).

            Examples:
                --------------------
                SharedPtr!long x = SharedPtr!long.make(123);
                assert(x.useCount == 1);
                auto wx = x.weak;   //weak pointer
                assert(wx.expired == false);
                assert(wx.lock.get == 123);
                assert(wx.useCount == 1);
                x = null;
                assert(wx.expired == true);
                assert(wx.useCount == 0);
                --------------------
        */
        static if(hasWeakCounter)
        public CopyTypeQualifiers!(This, WeakType) weak(this This)()scope @safe
        if(!is(This == shared)){
            mixin validateSharedPtr!This;
            return typeof(return)(this);
        }



        /**
            Checks if `this` stores a non-null pointer, i.e. whether `this != null`.

            Examples:
                --------------------
                SharedPtr!long x = SharedPtr!long.make(123);
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
            Cast `this` to different type `To` when `isSharedPtr!To`.

            Examples:
                --------------------
                SharedPtr!long x = SharedPtr!long.make(123);
                auto y = cast(SharedPtr!(const long))x;
                auto z = cast(const SharedPtr!long)x;
                auto u = cast(const SharedPtr!(const long))x;
                assert(x.useCount == 4);
                --------------------
        */
        public To opCast(To, this This)()scope
        if(isSharedPtr!To && !is(This == shared)){
            mixin validateSharedPtr!This;
            return To(this);
        }


        /**
            Operator == and != .
            Compare pointers.

            Examples:
                --------------------
                {
                    SharedPtr!long x = SharedPtr!long.make(0);
                    assert(x != null);
                    x = null;
                    assert(x == null);
                }

                {
                    SharedPtr!long x = SharedPtr!long.make(123);
                    SharedPtr!long y = SharedPtr!long.make(123);
                    assert(x == x);
                    assert(y == y);
                    assert(x != y);
                }

                {
                    SharedPtr!long x;
                    SharedPtr!(const long) y;
                    assert(x == x);
                    assert(y == y);
                    assert(x == y);
                }

                {
                    SharedPtr!long x = SharedPtr!long.make(123);
                    SharedPtr!long y = SharedPtr!long.make(123);
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
        if(isSharedPtr!Rhs && !is(Rhs == shared)){
            mixin validateSharedPtr!Rhs;
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
            Operators <, <=, >, >= for `SharedPtr`.

            Compare address of payload.

            Examples:
                --------------------
                {
                    const a = SharedPtr!long.make(42);
                    const b = SharedPtr!long.make(123);
                    const n = SharedPtr!long.init;

                    assert(a <= a);
                    assert(a >= a);

                    assert((a < b) == !(a >= b));
                    assert((a > b) == !(a <= b));

                    assert(a > n);
                    assert(a > null);
                    
                    assert(n < a);
                    assert(null < a);
                }

                {
                    const a = SharedPtr!long.make(42);
                    const b = SharedPtr!long.make(123);

                    assert(a <= a.element);
                    assert(a.element >= a);

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
        if(isSharedPtr!Rhs && !is(Rhs == shared)){
            mixin validateSharedPtr!Rhs;
            return this.opCmp(rhs._element);
        }



        /**
            Generate hash

            Return:
                Address of payload as `size_t`

            Examples:
                --------------------
                {
                    SharedPtr!long x = SharedPtr!long.make(123);
                    SharedPtr!long y = SharedPtr!long.make(123);
                    assert(x.toHash == x.toHash);
                    assert(y.toHash == y.toHash);
                    assert(x.toHash != y.toHash);
                    SharedPtr!(const long) z = x;
                    assert(x.toHash == z.toHash);
                }
                {
                    SharedPtr!long x;
                    SharedPtr!(const long) y;
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
            Move `SharedPtr`
        */
        public auto move()()scope{
            import core.lifetime : move_impl = move;

            return move_impl(this);
        }


        private ControlType* _control;
        private ElementReferenceType _element;

        private void _set_element(ElementReferenceType e)pure nothrow @trusted @nogc{
            static if(isMutable!ElementReferenceType)
                this._element = e;
            else
                (*cast(Unqual!ElementReferenceType*)&this._element) = cast(Unqual!ElementReferenceType)e;
        }

        private void _const_set_element(ElementReferenceType e)const pure nothrow @trusted @nogc{
            auto self = cast(Unqual!(typeof(this))*)&this;

            static if(isMutable!ElementReferenceType)
                self._element = e;
            else
                (*cast(Unqual!ElementReferenceType*)&self._element) = cast(Unqual!ElementReferenceType)e;
        }

        private void _const_set_counter(ControlType* c)const pure nothrow @trusted @nogc{
            auto self = cast(Unqual!(typeof(this))*)&this;

            self._control = c;
        }

        private void _release()scope /*pure nothrow @safe @nogc*/ {
            if(false){
                DestructorType dt;
                dt(null);
            }

            import std.traits : hasIndirections;
            import core.memory : GC;

            if(this._control is null)
                return;

            this._control.release!weakPtr;
        }

        private void _reset()scope pure nothrow @trusted @nogc{
            this._control = null;
            this._set_element(null);
        }
    }

}

/// ditto
public template SharedPtr(
    _Type,
    _ControlType,
    _DestructorType = DestructorType!_Type
)
if(isControlBlock!_ControlType && isDestructorType!_DestructorType){
    alias SharedPtr = .SharedPtr!(_Type, _DestructorType, _ControlType, false);
}

///
pure nothrow @nogc unittest{

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

    //implicit qualifier cast
    {
        SharedPtr!(const Foo) foo =  SharedPtr!Foo.make(42);
        assert(foo.get.i == 42);
        assert(foo.useCount == 1);

        const SharedPtr!Foo foo2 = foo;
        assert(foo2.get.i == 42);
        assert(foo.useCount == 2);

    }

    //polymorphic classes:
    {
        SharedPtr!Foo foo = SharedPtr!Bar.make(42, 3.14);
        assert(foo != null);
        assert(foo.useCount == 1);
        assert(foo.get.i == 42);

        //dynamic cast:
        {
            SharedPtr!Bar bar = dynCast!Bar(foo);
            assert(foo.useCount == 2);

            assert(bar.get.i == 42);
            assert(bar.get.d == 3.14);
        }

    }

    //aliasing:
    {
        SharedPtr!Foo foo = SharedPtr!Bar.make(42, 3.14);
        assert(foo.useCount == 1);

        auto x = SharedPtr!int(foo, &foo.get.i);
        assert(foo.useCount == 2);
        assert(x.useCount == 2);

        assert(*x == 42);
    }

    //weak references:
    {
        auto x = SharedPtr!double.make(3.14);
        assert(x.useCount == 1);
        assert(x.weakCount == 0);

        auto w = x.weak();  //weak pointer
        assert(x.useCount == 1);
        assert(x.weakCount == 1);
        assert(*w.lock == 3.14);

        WeakPtr!double w2 = x;
        assert(x.useCount == 1);
        assert(x.weakCount == 2);

        assert(w2.expired == false);
        x = null;
        assert(w2.expired == true);
    }

    //dynamic array
    {
        import std.algorithm : all;

        {
            auto arr = SharedPtr!(long[]).make(10, -1);

            assert(arr.length == 10);
            assert(arr.get.all!(x => x == -1));
        }

        {
            auto arr = SharedPtr!(long[]).make(8);
            assert(arr.length == 8);
            assert(arr.get.all!(x => x == long.init));
        }
    }

    //static array
    {
        import std.algorithm : all;

        {
            auto arr = SharedPtr!(long[4]).make(-1);
            assert(arr.get[].all!(x => x == -1));

        }

        {
            long[4] tmp = [0, 1, 2, 3];
            auto arr = SharedPtr!(long[4]).make(tmp);
            assert(arr.get[] == tmp[]);
        }
    }

}

///
pure nothrow @safe @nogc unittest{
    //make SharedPtr object
    static struct Foo{
        int i;

        this(int i)pure nothrow @safe @nogc{
            this.i = i;
        }
    }

    {
        auto foo = SharedPtr!Foo.make(42);
        auto foo2 = SharedPtr!Foo.make!Mallocator(42);  //explicit stateless allocator
    }

    {
        import std.experimental.allocator : make, dispose;

        static void deleter(long* x)pure nothrow @trusted @nogc{
            Mallocator.instance.dispose(x);
        }
        long* element = Mallocator.instance.make!long;

        auto x = SharedPtr!long.make(element, &deleter);
    }

    {
        auto arr = SharedPtr!(long[]).make(10); //dynamic array with length 10
        assert(arr.length == 10);
    }
}

///
nothrow unittest{
    //alloc SharedPtr object
    import std.experimental.allocator : make, dispose, allocatorObject;

    auto allocator = allocatorObject(Mallocator.instance);

    {
        auto x = SharedPtr!long.alloc(allocator, 42);
    }

    {
        static void deleter(long* x)pure nothrow @trusted @nogc{
            Mallocator.instance.dispose(x);
        }
        long* element = Mallocator.instance.make!long;
        auto x = SharedPtr!long.alloc(allocator, element, &deleter);
    }

    {
        auto arr = SharedPtr!(long[]).alloc(allocator, 10); //dynamic array with length 10
        assert(arr.length == 10);
    }

}


private template SharedPtrMakeDeleter(_Type, _DestructorType, _ControlType, DeleterType, AllocatorType, bool supportGC){
    alias AllocatorWithState = .AllocatorWithState!AllocatorType;

    enum bool hasStatelessAllocator = (AllocatorWithState.length == 0);

    static assert(false
        || hasStatelessAllocator 
        || isReferenceType!AllocatorType 
        || is(.DestructorType!AllocatorType : _DestructorType),
            "destructor of type '" ~ AllocatorType.stringof ~ 
            "' doesn't support specified finalizer " ~ _DestructorType.stringof
    );
    static assert(false
        || isReferenceType!DeleterType 
        || is(.DestructorType!DeleterType : _DestructorType),
            "destructor of type '" ~ DeleterType.stringof ~ 
            "' doesn't support specified finalizer " ~ _DestructorType.stringof
    );
    
    import std.traits: hasIndirections, isAbstractClass, isDynamicArray, Unqual;

    enum bool hasWeakCounter = _ControlType.hasWeakCounter;

    enum bool hasSharedCounter = _ControlType.hasSharedCounter;

    enum bool allocatorGCRange = supportGC
        && !hasStatelessAllocator
        && hasIndirections!AllocatorType;

    enum bool deleterGCRange = supportGC
        && hasIndirections!DeleterType;

    enum bool dataGCRange = supportGC;

    alias Vtable = _ControlType.Vtable;

    alias ElementReferenceType = ElementReferenceTypeImpl!_Type;

    struct SharedPtrMakeDeleter{
        static assert(control.offsetof == 0);

        private _ControlType control;

        static if(!hasStatelessAllocator)
            private AllocatorType allocator;

        private DeleterType deleter;
        private ElementReferenceType data;

        private static immutable Vtable vtable;

        version(D_BetterC)
            private static void shared_static_this()pure nothrow @trusted @nogc{
                assumePure((){
                    Vtable* vptr = cast(Vtable*)&vtable;
                    
                    static if(hasSharedCounter)
                        vptr.on_zero_shared = &virtual_on_zero_shared;

                    static if(hasWeakCounter)
                        vptr.on_zero_weak = &virtual_on_zero_weak;

                    vptr.manual_destroy = &virtual_manual_destroy;
                })();

            }
        else
            shared static this(){
                static if(hasWeakCounter){
                    vtable = Vtable(
                        &virtual_on_zero_shared,
                        &virtual_on_zero_weak,
                        &virtual_manual_destroy
                    );
                }
                else static if(hasSharedCounter){
                    vtable = Vtable(
                        &virtual_on_zero_shared,
                        &virtual_manual_destroy
                    );
                }
                else vtable = Vtable(
                    &virtual_manual_destroy
                );
            }


        public _ControlType* base()pure nothrow @safe @nogc{
            return &this.control;
        }

        public alias get = data;


        public static SharedPtrMakeDeleter* make
            (Args...)
            (ElementReferenceType data, DeleterType deleter, AllocatorWithState[0 .. $] a)
        {
            import std.traits: hasIndirections;
            import core.lifetime : forward, emplace;

            static assert(!isAbstractClass!_Type,
                "cannot create object of abstract class" ~ Unqual!_Type.stringof
            );
            static assert(!is(_Type == interface),
                "cannot create object of interface type " ~ Unqual!_Type.stringof
            );


            static if(hasStatelessAllocator)
                void[] raw = statelessAllcoator!AllocatorType.allocate(typeof(this).sizeof);
            else
                void[] raw = a[0].allocate(typeof(this).sizeof);

            if(raw.length == 0)
                return null;


            debug _log_ptr_allocate();

            SharedPtrMakeDeleter* result = (()@trusted => cast(SharedPtrMakeDeleter*)raw.ptr)();

            static if(allocatorGCRange){
                static assert(supportGC);
                static assert(typeof(this).data.offsetof >= typeof(this).deleter.offsetof);
                static assert(typeof(this).deleter.offsetof >= typeof(this).allocator.offsetof);

                static if(dataGCRange)
                    enum size_t gc_range_size = typeof(this).data.offsetof
                        - typeof(this).allocator.offsetof
                        + typeof(this.data).sizeof;
                else static if(deleterGCRange)
                    enum size_t gc_range_size = typeof(this).deleter.offsetof
                        - typeof(this).allocator.offsetof
                        + typeof(this.deleter).sizeof;
                else
                    enum size_t gc_range_size = AllocatorType.sizeof;

                gc_add_range(
                    cast(void*)&result.allocator,
                    gc_range_size
                );
            }
            else static if(deleterGCRange){
                static assert(supportGC);
                static assert(!allocatorGCRange);
                static assert(typeof(this).data.offsetof >= typeof(this).deleter.offsetof);

                static if(dataGCRange)
                    enum size_t gc_range_size = typeof(this).data.offsetof
                        - typeof(this).deleter.offsetof
                        + typeof(this.data).sizeof;
                else
                    enum size_t gc_range_size = _DeleterType.sizeof;

                gc_add_range(
                    cast(void*)&result.deleter,
                    gc_range_size
                );
            }
            else static if(dataGCRange){
                static assert(supportGC);
                static assert(!allocatorGCRange);
                static assert(!deleterGCRange);

                gc_add_range(
                    &result.data,
                    ElementReferenceType.sizeof
                );
            }

            return emplace(result, forward!(deleter, a, data));
        }


        public this(Args...)(DeleterType deleter, AllocatorWithState[0 .. $] a, ElementReferenceType data){
            import core.lifetime : forward, emplace;

            debug _log_ptr_construct();

            version(D_BetterC){
                if(!vtable.initialized())
                    shared_static_this();
            }
            else 
                assert(vtable.initialized());
                
            this.control = _ControlType(&vtable);
            assert(vtable.valid, "vtables are not initialized");

            static if(!hasStatelessAllocator)
                this.allocator = a[0];

            this.deleter = forward!deleter;
            this.data = data;
        }


        static if(hasSharedCounter){
            public static void virtual_on_zero_shared(Unqual!_ControlType* control)pure nothrow @nogc @safe{
                auto self = get_offset_this(control);
                self.destruct();

                static if(!hasWeakCounter)
                    self.deallocate();
            }
        }

        static if(hasWeakCounter){
            public static void virtual_on_zero_weak(Unqual!_ControlType* control)pure nothrow @nogc @safe{
                auto self = get_offset_this(control);
                self.deallocate();
            }
        }

        public static void virtual_manual_destroy(Unqual!_ControlType* control, bool dealocate)pure nothrow @nogc @safe{
            auto self = get_offset_this(control);
            self.destruct();
            if(dealocate)
                self.deallocate();

        }
        
        private static inout(SharedPtrMakeDeleter)* get_offset_this(inout(Unqual!_ControlType)* control)pure nothrow @trusted @nogc{
            assert(control !is null);
            return cast(typeof(return))((cast(void*)control) - SharedPtrMakeDeleter.control.offsetof);
        }

        private void destruct()pure nothrow @trusted @nogc{
            assumePureNoGcNothrow((ref DeleterType deleter, ElementReferenceType data){
                deleter(data);
            })(this.deleter, this.data);

            static if(!allocatorGCRange && !deleterGCRange && dataGCRange){
                static assert(supportGC);

                gc_remove_range(&this.data);
            }

            debug _log_ptr_destruct();
        }

        private void deallocate()pure nothrow @trusted @nogc{
            void* self = cast(void*)&this;
            _destruct!(typeof(this), DestructorType!void)(self);


            void[] raw = self[0 .. typeof(this).sizeof];


            static if(hasStatelessAllocator)
                assumePureNoGcNothrow(function(void[] raw)@trusted => statelessAllcoator!AllocatorType.deallocate(raw))(raw);
            else
                assumePureNoGcNothrow(function(void[] raw, ref typeof(this.allocator) allo)@trusted => allo.deallocate(raw))(raw, this.allocator);



            static if(allocatorGCRange){
                static assert(supportGC);

                gc_remove_range(&this.allocator);
            }
            else static if(deleterGCRange){
                static assert(supportGC);
                static assert(!allocatorGCRange);

                gc_remove_range(&this.deleter);
            }

            debug _log_ptr_deallocate();
        }
    }
}


/+
class SharedPtrThis_test : SharedPtrThis!(DestructorType!long){

}+/
template SharedPtrThis(
    _DestructorType,
    bool _threadLocal = false,
    _ControlType = ControlTypeDeduction!(_Type, DefaultSharedControlBlock)
){


    enum bool hasWeakCounter = _ControlType.hasWeakCounter;

    enum bool hasSharedCounter = _ControlType.hasSharedCounter;

    static if(hasSharedCounter){

        static void on_zero_shared_impl(bool atomic)(SharedPtrThis self)pure nothrow @nogc @safe{
            self.destruct();

            static if(hasWeakCounter){
                if(self._shared_ptr_counter.count!(true, atomic) == 0){
                    self.deallocate();
                }
            }
            else{
                self.deallocate();
            }
        }

        static void virtual_on_zero_shared_atomic(SharedPtrThis self){
            on_zero_shared_impl!true(self);
        }
        static void virtual_on_zero_shared(SharedPtrThis self){
            on_zero_shared_impl!true(self);
        }
    }

    static if(hasWeakCounter){
        static void virtual_on_zero_weak_atomic(SharedPtrThis self){

        }
        static void virtual_on_zero_weak(SharedPtrThis self){

        }
    }

    static void virtual_manual_destroy(SharedPtrThis self, bool dealloc){

    }

    alias Vtable = _ControlType.Vtable;

    static immutable Vtable vtable;

    shared static this(){
        static if(hasWeakCounter){
            vtable = Vtable(
                SharedPtrThis._shared_ptr_counter.offsetof,

                cast(typeof(Vtable.on_zero_shared_atomic))&virtual_on_zero_shared_atomic,
                cast(typeof(Vtable.on_zero_shared))&virtual_on_zero_shared,

                cast(typeof(Vtable.on_zero_weak_atomic))&virtual_on_zero_weak_atomic,
                cast(typeof(Vtable.on_zero_weak))&virtual_on_zero_weak,

                cast(typeof(Vtable.manual_destroy))&virtual_manual_destroy
            );
        }
        else static if(hasSharedCounter){
            vtable = Vtable(
                SharedPtrThis._shared_ptr_counter.offsetof,

                cast(typeof(Vtable.on_zero_shared_atomic))&virtual_on_zero_shared_atomic,
                cast(typeof(Vtable.on_zero_shared))&virtual_on_zero_shared,

                cast(typeof(Vtable.manual_destroy))&virtual_manual_destroy
            );
        }
        else vtable = Vtable(
            SharedPtrThis._shared_ptr_counter.offsetof,

            cast(typeof(Vtable.manual_destroy))&virtual_manual_destroy
        );
    }

    class SharedPtrThis{
        package _ControlType _shared_ptr_counter;



        this()pure nothrow @safe @nogc{

        }

    }


}

/**
    Weak pointer

    `WeakPtr` is a smart pointer that holds a non-owning ("weak") reference to an object that is managed by `SharedPtr`.
    It must be converted to `SharedPtr` in order to access the referenced object.

    `WeakPtr` models temporary ownership: when an object needs to be accessed only if it exists, and it may be deleted at any time by someone else,
    `WeakPtr` is used to track the object, and it is converted to `SharedPtr` to assume temporary ownership.
    If the original `SharedPtr` is destroyed at this time, the object's lifetime is extended until the temporary `SharedPtr` is destroyed as well.

    Another use for `WeakPtr` is to break reference cycles formed by objects managed by `SharedPtr`.
    If such cycle is orphaned (i,e. there are no outside shared pointers into the cycle), the `SharedPtr` reference counts cannot reach zero and the memory is leaked.
    To prevent this, one of the pointers in the cycle can be made weak.
*/
public template WeakPtr(
    _Type,
    _DestructorType = DestructorType!_Type,
    _ControlType = ControlTypeDeduction!(_Type, DefaultSharedControlBlock),
)
if(isControlBlock!_ControlType && isDestructorType!_DestructorType){
    alias WeakPtr = .SharedPtr!(_Type, _DestructorType, _ControlType, true);
}

/// ditto
public template WeakPtr(
    _Type,
    _ControlType,
    _DestructorType = DestructorType!_Type,
)
if(isControlBlock!_ControlType && isDestructorType!_DestructorType){
    alias WeakPtr = .SharedPtr!(_Type, _DestructorType, _ControlType, true);
}


/**
    Dynamic cast for shared pointers if `ElementType` is class with D linkage.

    Creates a new instance of `SharedPtr` whose stored pointer is obtained from `ptr`'s stored pointer using a dynaic cast expression.

    If `ptr` is null or dynamic cast fail then result `SharedPtr` is null.
    Otherwise, the new `SharedPtr` will share ownership with the initial value of `ptr`.
*/
public ChangeElementType!(Ptr, T) dynCast(T, Ptr)(auto ref scope Ptr ptr)
if(true
    && isSharedPtr!Ptr && !is(Ptr == shared) && !Ptr.weakPtr
    && isReferenceType!T && __traits(getLinkage, T) == "D"
    && isReferenceType!(Ptr.ElementType) && __traits(getLinkage, Ptr.ElementType) == "D"
){

    import std.traits : CopyTypeQualifiers;
    import core.lifetime : forward;

    alias Return = typeof(return);

    static assert(is(
        CopyTypeQualifiers!(GetElementReferenceType!Ptr, void*) 
            : CopyTypeQualifiers!(GetElementReferenceType!Return, void*) 
    ));

    if(ptr == null)
        return Return.init;

    if(auto element = cast(Return.ElementType)ptr._element){
        return (()@trusted => Return(forward!ptr, element) )();

    }

    return Return.init;
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
        SharedPtr!(const Foo) foo = SharedPtr!Bar.make(42, 3.14);
        assert(foo.get.i == 42);

        auto bar = dynCast!Bar(foo);
        assert(bar != null);
        assert(bar.get.d == 3.14);
        static assert(is(typeof(bar) == SharedPtr!(const Bar)));

        auto zee = dynCast!Zee(foo);
        assert(zee == null);
        static assert(is(typeof(zee) == SharedPtr!(const Zee)));
    }
}



/**
    Return `shared SharedPtr` pointing to same managed object like parameter `ptr`.

    Type of parameter `ptr` must be `SharedPtr` with `shared(ControlType)` and `shared`/`immutable` `ElementType` .
*/
public shared(Ptr) share(Ptr)(auto ref Ptr ptr)
if(isSharedPtr!Ptr){
    mixin validateSharedPtr!Ptr;

    import core.lifetime : forward;
    static if(is(Ptr == shared)){
        return forward!ptr;
    }
    else{
        static assert(is(Ptr.ControlType == shared),
            "`SharedPtr` has not shared ref counter `ControlType`."
        );

        static assert(is(Ptr.ElementType == shared) || is(Ptr.ElementType == immutable),
            "`SharedPtr` has not shared/immutable `ElementType`."
        );

        alias Result = shared(Ptr);
        mixin validateSharedPtr!Result;

        return Result(forward!ptr);
    }
}

///
nothrow @nogc unittest{
    {
        auto x = SharedPtr!(shared long).make(123);
        assert(x.useCount == 1);

        shared s1 = share(x);
        assert(x.useCount == 2);


        shared s2 = share(x.move);
        assert(x == null);
        assert(s2.useCount == 2);
        assert(s2.load.get == 123);

    }

    {
        auto x = SharedPtr!(long).make(123);
        assert(x.useCount == 1);

        ///error `shared SharedPtr` need shared `ControlType` and shared `ElementType`.
        //shared s1 = share(x);

    }

}


//local traits:
private{
    package mixin template validateSharedPtr(Ts...){
        static foreach(alias T; Ts){
            static assert(isSharedPtr!T);
            static assert(!is(T == shared) || is(T.ControlType == shared),
                "shared `SharedPtr` is valid only if its `ControlType` is shared. (" ~ T.stringof ~ ")."
            );
        }
    }

    template needLock(From, To)
    if(isSharedPtr!From && isSharedPtr!To){
        enum needLock = (From.weakPtr && !To.weakPtr);
    }

    template isAliasable(From, To)
    if(isSharedPtr!From && isSharedPtr!To){
        /+import std.traits : CopyTypeQualifiers;

        alias FromType = CopyTypeQualifiers!(
            From,
            CopyTypeQualifiers!(From.ElementType, void)
        );
        alias ToType = CopyTypeQualifiers!(
            To,
            CopyTypeQualifiers!(To.ElementType, void)
        );+/


        enum bool isAliasable = true
            //&& is(FromType* : ToType*)
            && is(From.DestructorType : To.DestructorType)
            && is(From.ControlType == To.ControlType);
    }

    template isConstructable(From, To)
    if((isSharedPtr!From || isUniquePtr!From || isRcPtr!From) && isSharedPtr!To){
        import std.traits : CopyTypeQualifiers;

        alias FromPtr = CopyTypeQualifiers!(From, From.ElementReferenceType);
        alias ToPtr = CopyTypeQualifiers!(To, To.ElementReferenceType);

        enum bool isConstructable = true
            && is(FromPtr : ToPtr)
            && is(From.DestructorType : To.DestructorType)
            && is(From.ControlType == To.ControlType)            ;
    }

    template isAssignable(From, To)
    if(isSharedPtr!From && isSharedPtr!To){
        import std.traits : isMutable;

        enum bool isAssignable = true
            && isConstructable!(From, To)
            && isMutable!To;
    }

    template ChangeElementType(Ptr, T)
    if(isSharedPtr!Ptr){
        import std.traits : CopyTypeQualifiers;

        alias FromType = CopyTypeQualifiers!(Ptr, Ptr.ElementType);
        alias ResultType = CopyTypeQualifiers!(FromType, T);

        alias ResultPtr = SharedPtr!(
            ResultType,

            Ptr.DestructorType,
            Ptr.ControlType,
            Ptr.weakPtr
        );

        alias ChangeElementType = ResultPtr;
    }

    template GetElementReferenceType(Ptr)
    if(isSharedPtr!Ptr){
        import std.traits : CopyTypeQualifiers, isDynamicArray;
        import std.range : ElementEncodingType;

        alias ElementType = CopyTypeQualifiers!(Ptr, Ptr.ElementType);

        alias GetElementReferenceType = ElementReferenceTypeImpl!ElementType;
    }

}

//mutex:
private static auto lockSharedPtr
    (alias fn, Ptr, Args...)
    (auto ref scope shared Ptr ptr, auto ref scope return Args args)
{
    import std.traits : CopyConstness, CopyTypeQualifiers, Unqual;
    import core.lifetime : forward;
    import autoptr.internal.mutex : getMutex;


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



version(unittest){
    struct TestAllocator{
        static assert(stateSize!TestAllocator > 0);
        private int x;
        import std.experimental.allocator.common : platformAlignment, stateSize;

        enum uint alignment = platformAlignment;

        void[] allocate(size_t bytes)@trusted @nogc nothrow pure{
            import core.memory : pureMalloc;
            if (!bytes) return null;
            auto p = pureMalloc(bytes);
            return p ? p[0 .. bytes] : null;
        }

        bool deallocate(void[] b)@system @nogc nothrow pure{
            import core.memory : pureFree;
            pureFree(b.ptr);
            return true;
        }

        bool reallocate(ref void[] b, size_t s)@system @nogc nothrow pure{
            import core.memory : pureRealloc;
            if (!s){
                // fuzzy area in the C standard, see http://goo.gl/ZpWeSE
                // so just deallocate and nullify the pointer
                deallocate(b);
                b = null;
                return true;
            }

            auto p = cast(ubyte*) pureRealloc(b.ptr, s);
            if (!p) return false;
            b = p[0 .. s];
            return true;
        }

        //static TestAllocator instance;

    }

    //this(SharedPtr, Element)
    pure nothrow @nogc unittest{
        {
            static struct Foo{
                int i;
                double d;
            }
            SharedPtr!Foo foo = SharedPtr!Foo.make(42, 3.14);

            auto x = SharedPtr!double(foo, &foo.get.d);
            assert(foo.useCount == 2);
            assert(x.get == 3.14);
        }

        {
            auto x1 = SharedPtr!long.make(1);

            const float f;
            auto x2 = const SharedPtr!float(x1, &f);

            assert(x1.useCount == 2);

            const double d;
            auto x3 = SharedPtr!(const double)((() => x2)(), &d);
            assert(x1.useCount == 3);

            /+shared bool b;
            auto x4 = SharedPtr!(shared bool)(x3, &b);
            assert(x1.useCount == 4);+/
        }

    }

    //copy ctor
    pure nothrow @nogc unittest{


        static struct Test{}

        import std.meta : AliasSeq;
        //alias Test = long;
        static foreach(alias ControlType; AliasSeq!(DefaultSharedControlBlock, shared DefaultSharedControlBlock)){{
            alias SPtr(T) = SharedPtr!(T, DestructorType!T, ControlType);

            //mutable:
            {
                alias Ptr = SPtr!(Test);
                Ptr ptr;
                static assert(__traits(compiles, Ptr(ptr)));
                static assert(__traits(compiles, const(Ptr)(ptr)));
                static assert(!__traits(compiles, immutable(Ptr)(ptr)));
                static assert(!__traits(compiles, shared(Ptr)(ptr)));
                static assert(!__traits(compiles, const(shared(Ptr))(ptr)));

                const(Ptr) cptr;
                static assert(!__traits(compiles, Ptr(cptr)));
                static assert(__traits(compiles, const(Ptr)(cptr)));
                static assert(!__traits(compiles, immutable(Ptr)(cptr)));
                static assert(!__traits(compiles, shared(Ptr)(cptr)));
                static assert(!__traits(compiles, const(shared(Ptr))(cptr)));

                immutable(Ptr) iptr;
                static assert(!__traits(compiles, Ptr(iptr)));
                static assert(__traits(compiles, const(Ptr)(iptr)));
                static assert(__traits(compiles, immutable(Ptr)(iptr)));
                static assert(!__traits(compiles, shared(Ptr)(iptr)));
                static assert(__traits(compiles, const(shared(Ptr))(iptr)) == is(ControlType == shared));

                shared(Ptr) sptr;
                static assert(!__traits(compiles, Ptr(sptr)));
                static assert(!__traits(compiles, const(Ptr)(sptr)));
                static assert(!__traits(compiles, immutable(Ptr)(sptr)));
                static assert(!__traits(compiles, shared(Ptr)(sptr)));   //need load
                static assert(!__traits(compiles, const shared Ptr(sptr)));  //need load
                shared(const(Ptr)) scptr;
                static assert(!__traits(compiles, Ptr(scptr)));
                static assert(!__traits(compiles, const(Ptr)(scptr)));
                static assert(!__traits(compiles, immutable(Ptr)(scptr)));
                static assert(!__traits(compiles, shared(Ptr)(scptr)));
                static assert(!__traits(compiles, const(shared(Ptr))(scptr)));  //need load
            }

            //const:
            {
                alias Ptr = SPtr!(const Test);
                Ptr ptr;
                static assert(__traits(compiles, Ptr(ptr)));
                static assert(__traits(compiles, const(Ptr)(ptr)));
                static assert(!__traits(compiles, immutable(Ptr)(ptr)));
                static assert(!__traits(compiles, shared(Ptr)(ptr)));
                static assert(!__traits(compiles, const(shared(Ptr))(ptr)));

                const(Ptr) cptr;
                static assert(__traits(compiles, Ptr(cptr)));
                static assert(__traits(compiles, const(Ptr)(cptr)));
                static assert(!__traits(compiles, immutable(Ptr)(cptr)));
                static assert(!__traits(compiles, shared(Ptr)(cptr)));
                static assert(!__traits(compiles, const(shared(Ptr))(cptr)));

                immutable(Ptr) iptr;
                static assert(__traits(compiles, Ptr(iptr)));
                static assert(__traits(compiles, const(Ptr)(iptr)));
                static assert(__traits(compiles, immutable(Ptr)(iptr)));
                static assert(__traits(compiles, shared(Ptr)(iptr)) == is(ControlType == shared));
                static assert(__traits(compiles, const(shared(Ptr))(iptr)) == is(ControlType == shared));

                shared(Ptr) sptr;
                static assert(!__traits(compiles, Ptr(sptr)));
                static assert(!__traits(compiles, const(Ptr)(sptr)));
                static assert(!__traits(compiles, immutable(Ptr)(sptr)));
                static assert(!__traits(compiles, shared(Ptr)(sptr)));          //need load
                static assert(!__traits(compiles, const shared Ptr(sptr)));     //need load
                shared(const(Ptr)) scptr;
                static assert(!__traits(compiles, Ptr(scptr)));
                static assert(!__traits(compiles, const(Ptr)(scptr)));
                static assert(!__traits(compiles, immutable(Ptr)(scptr)));
                static assert(!__traits(compiles, shared(Ptr)(scptr)));         //need load
                static assert(!__traits(compiles, const(shared(Ptr))(scptr)));  //need load
            }

            //immutable:
            {
                alias Ptr = SPtr!(immutable Test);
                Ptr ptr;
                static assert(__traits(compiles, Ptr(ptr)));
                static assert(__traits(compiles, const(Ptr)(ptr)));
                static assert(__traits(compiles, immutable(Ptr)(ptr)));
                static assert(__traits(compiles, shared(Ptr)(ptr)) == is(ControlType == shared));
                static assert(__traits(compiles, const(shared(Ptr))(ptr)) == is(ControlType == shared));

                const(Ptr) cptr;
                static assert(__traits(compiles, Ptr(cptr)));
                static assert(__traits(compiles, const(Ptr)(cptr)));
                static assert(__traits(compiles, immutable(Ptr)(cptr)));
                static assert(__traits(compiles, shared(Ptr)(cptr)) == is(ControlType == shared));
                static assert(__traits(compiles, const(shared(Ptr))(cptr)) == is(ControlType == shared));

                immutable(Ptr) iptr;
                static assert(__traits(compiles, Ptr(iptr)));
                static assert(__traits(compiles, const(Ptr)(iptr)));
                static assert(__traits(compiles, immutable(Ptr)(iptr)));
                static assert(__traits(compiles, shared(Ptr)(iptr)) == is(ControlType == shared));
                static assert(__traits(compiles, const(shared(Ptr))(iptr)) == is(ControlType == shared));

                shared(Ptr) sptr;
                static assert(!__traits(compiles, Ptr(sptr)));
                static assert(!__traits(compiles, const(Ptr)(sptr)));
                static assert(!__traits(compiles, immutable(Ptr)(sptr)));
                static assert(!__traits(compiles, shared(Ptr)(sptr)));          //need load
                static assert(!__traits(compiles, const shared Ptr(sptr)));     //need load
                shared(const(Ptr)) scptr;
                static assert(!__traits(compiles, Ptr(scptr)));
                static assert(!__traits(compiles, const(Ptr)(scptr)));
                static assert(!__traits(compiles, immutable(Ptr)(scptr)));
                static assert(!__traits(compiles, shared(Ptr)(scptr)));         //need load
                static assert(!__traits(compiles, const(shared(Ptr))(scptr)));  //need load
            }


            //shared:
            static if(is(ControlType == shared)){{
                alias Ptr = SPtr!(shared Test);
                Ptr ptr;
                static assert(__traits(compiles, Ptr(ptr)));
                static assert(__traits(compiles, const(Ptr)(ptr)));
                static assert(!__traits(compiles, immutable(Ptr)(ptr)));
                static assert(__traits(compiles, shared(Ptr)(ptr)));
                static assert(__traits(compiles, const(shared(Ptr))(ptr)));

                const(Ptr) cptr;
                static assert(!__traits(compiles, Ptr(cptr)));
                static assert(__traits(compiles, const(Ptr)(cptr)));
                static assert(!__traits(compiles, immutable(Ptr)(cptr)));
                static assert(!__traits(compiles, shared(Ptr)(cptr)));
                static assert(__traits(compiles, const(shared(Ptr))(cptr)));

                immutable(Ptr) iptr;
                static assert(!__traits(compiles, Ptr(iptr)));
                static assert(__traits(compiles, const(Ptr)(iptr)));
                static assert(__traits(compiles, immutable(Ptr)(iptr)));
                static assert(!__traits(compiles, shared(Ptr)(iptr)));
                static assert(__traits(compiles, const(shared(Ptr))(iptr)));

                shared(Ptr) sptr;
                static assert(!__traits(compiles, Ptr(sptr)));
                static assert(!__traits(compiles, const(Ptr)(sptr)));
                static assert(!__traits(compiles, immutable(Ptr)(sptr)));
                static assert(!__traits(compiles, shared(Ptr)(sptr)));          //need load
                static assert(!__traits(compiles, const shared Ptr(sptr)));     //need load
                shared(const(Ptr)) scptr;
                static assert(!__traits(compiles, Ptr(scptr)));
                static assert(!__traits(compiles, const(Ptr)(scptr)));
                static assert(!__traits(compiles, immutable(Ptr)(scptr)));
                static assert(!__traits(compiles, shared(Ptr)(scptr)));         //need load
                static assert(!__traits(compiles, const(shared(Ptr))(scptr)));  //need load
            }}


            //const shared:
            static if(is(ControlType == shared)){{
                alias Ptr = SPtr!(const shared Test);
                Ptr ptr;
                static assert(__traits(compiles, Ptr(ptr)));
                static assert(__traits(compiles, const(Ptr)(ptr)));
                static assert(!__traits(compiles, immutable(Ptr)(ptr)));
                static assert(__traits(compiles, shared(Ptr)(ptr)));
                static assert(__traits(compiles, const(shared(Ptr))(ptr)));

                const(Ptr) cptr;
                static assert(__traits(compiles, Ptr(cptr)));
                static assert(__traits(compiles, const(Ptr)(cptr)));
                static assert(!__traits(compiles, immutable(Ptr)(cptr)));
                static assert(__traits(compiles, shared(Ptr)(cptr)));
                static assert(__traits(compiles, const(shared(Ptr))(cptr)));

                immutable(Ptr) iptr;
                static assert(__traits(compiles, Ptr(iptr)));
                static assert(__traits(compiles, const(Ptr)(iptr)));
                static assert(__traits(compiles, immutable(Ptr)(iptr)));
                static assert(__traits(compiles, shared(Ptr)(iptr)));
                static assert(__traits(compiles, const(shared(Ptr))(iptr)));

                shared(Ptr) sptr;
                static assert(!__traits(compiles, Ptr(sptr)));
                static assert(!__traits(compiles, const(Ptr)(sptr)));
                static assert(!__traits(compiles, immutable(Ptr)(sptr)));
                static assert(!__traits(compiles, shared(Ptr)(sptr)));          //need load
                static assert(!__traits(compiles, const shared Ptr(sptr)));     //need load
                shared(const(Ptr)) scptr;
                static assert(!__traits(compiles, Ptr(scptr)));
                static assert(!__traits(compiles, const(Ptr)(scptr)));
                static assert(!__traits(compiles, immutable(Ptr)(scptr)));
                static assert(!__traits(compiles, shared(Ptr)(scptr)));         //need load
                static assert(!__traits(compiles, const(shared(Ptr))(scptr)));  //need load

            }}

        }}
    }

    //this(typeof(null))
    pure nothrow @safe @nogc unittest{
        SharedPtr!long x = null;

        assert(x == null);
        assert(x == SharedPtr!long.init);

    }


    //opAssign(SharedPtr)
    pure nothrow @nogc unittest{

        {
            SharedPtr!long px1 = SharedPtr!long.make(1);
            SharedPtr!long px2 = SharedPtr!long.make(2);

            assert(px2.useCount == 1);
            px1 = px2;
            assert(px1.get == 2);
            assert(px2.useCount == 2);
        }



        {
            SharedPtr!long px = SharedPtr!long.make(1);
            SharedPtr!(const long) pcx = SharedPtr!long.make(2);

            assert(px.useCount == 1);
            pcx = px;
            assert(pcx.get == 1);
            assert(pcx.useCount == 2);

        }


        {
            const SharedPtr!long cpx = SharedPtr!long.make(1);
            SharedPtr!(const long) pcx = SharedPtr!long.make(2);

            assert(pcx.useCount == 1);
            pcx = cpx;
            assert(pcx.get == 1);
            assert(pcx.useCount == 2);

        }

        {
            SharedPtr!(immutable long) pix = SharedPtr!(immutable long).make(123);
            SharedPtr!(const long) pcx = SharedPtr!long.make(2);

            assert(pix.useCount == 1);
            pcx = pix;
            assert(pcx.get == 123);
            assert(pcx.useCount == 2);

        }
    }

    //opAssign(null)
    nothrow @safe @nogc unittest{
        {
            SharedPtr!long x = SharedPtr!long.make(1);

            assert(x.useCount == 1);
            x = null;
            assert(x.useCount == 0);
            assert(x == null);
        }

        {
            SharedPtr!(shared long) x = SharedPtr!(shared long).make(1);

            assert(x.useCount == 1);
            x = null;
            assert(x.useCount == 0);
            assert(x == null);
        }

        import autoptr.internal.mutex : supportMutex;
        static if(supportMutex){
            shared SharedPtr!(long).ThreadLocal!false x = SharedPtr!(shared long).ThreadLocal!false.make(1);

            assert(x.useCount == 1);
            x = null;
            assert(x.useCount == 0);
            assert(x.load == null);
        }
    }

    //useCount
    pure nothrow @safe @nogc unittest{
        SharedPtr!long x = null;

        assert(x.useCount == 0);

        x = SharedPtr!long.make(123);
        assert(x.useCount == 1);

        auto y = x;
        assert(x.useCount == 2);

        auto w1 = x.weak;    //weak ptr
        assert(x.useCount == 2);

        SharedPtr!long.WeakType w2 = x;   //weak ptr
        assert(x.useCount == 2);

        y = null;
        assert(x.useCount == 1);

        x = null;
        assert(x.useCount == 0);
        assert(w1.useCount == 0);
    }

    //weakCount
    pure nothrow @safe @nogc unittest{

        SharedPtr!long x = null;
        assert(x.useCount == 0);
        assert(x.weakCount == 0);

        x = SharedPtr!long.make(123);
        assert(x.useCount == 1);
        assert(x.weakCount == 0);

        auto w = x.weak();
        assert(x.useCount == 1);
        assert(x.weakCount == 1);
    }

    // store:
    nothrow @nogc unittest{

        //null store:
        {
            shared x = SharedPtr!(shared long).make(123);
            assert(x.load.get == 123);

            x.store(null);
            assert(x.useCount == 0);
            assert(x.load == null);
        }

        //rvalue store:
        {
            shared x = SharedPtr!(shared long).make(123);
            assert(x.load.get == 123);

            x.store(SharedPtr!(shared long).make(42));
            assert(x.load.get == 42);
        }

        //lvalue store:
        {
            shared x = SharedPtr!(shared long).make(123);
            auto y = SharedPtr!(shared long).make(42);

            assert(x.load.get == 123);
            assert(y.load.get == 42);

            x.store(y);
            assert(x.load.get == 42);
            assert(x.useCount == 2);
        }
    }

    //load:
    nothrow @nogc unittest{

        shared SharedPtr!(long).ThreadLocal!false x = SharedPtr!(shared long).ThreadLocal!false.make(123);

        import autoptr.internal.mutex : supportMutex;
        static if(supportMutex){
            SharedPtr!(shared long) y = x.load();
            assert(y.useCount == 2);

            assert(y.get == 123);
        }

    }

    //exchange
    nothrow @nogc unittest{

        //lvalue exchange
        {
            shared x = SharedPtr!(shared long).make(123);
            auto y = SharedPtr!(shared long).make(42);

            auto z = x.exchange(y);

            assert(x.load.get == 42);
            assert(y.get == 42);
            assert(z.get == 123);
        }

        //rvalue exchange
        {
            shared x = SharedPtr!(shared long).make(123);
            auto y = SharedPtr!(shared long).make(42);

            auto z = x.exchange(y.move);

            assert(x.load.get == 42);
            assert(y == null);
            assert(z.get == 123);
        }

        //null exchange (same as move)
        {
            shared x = SharedPtr!(shared long).make(123);

            auto z = x.exchange(null);

            assert(x.load == null);
            assert(z.get == 123);
        }

        //swap:
        {
            shared x = SharedPtr!(shared long).make(123);
            auto y = SharedPtr!(shared long).make(42);

            //opAssign is same as store
            y = x.exchange(y.move);

            assert(x.load.get == 42);
            assert(y.get == 123);
        }

    }

    //compareExchange
    nothrow @nogc unittest{
        alias Type = const long;
        static foreach(enum bool weak; [true, false]){
            //fail
            {
                SharedPtr!Type a = SharedPtr!Type.make(123);
                SharedPtr!Type b = SharedPtr!Type.make(42);
                SharedPtr!Type c = SharedPtr!Type.make(666);

                static if(weak)a.compareExchangeWeak(b, c);
                else a.compareExchangeStrong(b, c);

                assert(*a == 123);
                assert(*b == 123);
                assert(*c == 666);

            }

            //success
            {
                SharedPtr!Type a = SharedPtr!Type.make(123);
                SharedPtr!Type b = a;
                SharedPtr!Type c = SharedPtr!Type.make(666);

                static if(weak)a.compareExchangeWeak(b, c);
                else a.compareExchangeStrong(b, c);

                assert(*a == 666);
                assert(*b == 123);
                assert(*c == 666);
            }

            //shared fail
            {
                shared SharedPtr!(shared Type) a = SharedPtr!(shared Type).make(123);
                SharedPtr!(shared Type) b = SharedPtr!(shared Type).make(42);
                SharedPtr!(shared Type) c = SharedPtr!(shared Type).make(666);

                static if(weak)a.compareExchangeWeak(b, c);
                else a.compareExchangeStrong(b, c);

                auto tmp = a.exchange(null);
                assert(*tmp == 123);
                assert(*b == 123);
                assert(*c == 666);
            }

            //shared success
            {
                SharedPtr!(shared Type) b = SharedPtr!(shared Type).make(123);
                shared SharedPtr!(shared Type) a = b;
                SharedPtr!(shared Type) c = SharedPtr!(shared Type).make(666);

                static if(weak)a.compareExchangeWeak(b, c);
                else a.compareExchangeStrong(b, c);

                auto tmp = a.exchange(null);
                assert(*tmp == 666);
                assert(*b == 123);
                assert(*c == 666);
            }
        }
    }

    //lock
    nothrow @nogc unittest{
        {
            SharedPtr!long x = SharedPtr!long.make(123);

            auto w = x.weak;    //weak ptr

            SharedPtr!long y = w.lock;

            assert(x == y);
            assert(x.useCount == 2);
            assert(y.get == 123);
        }

        {
            SharedPtr!long x = SharedPtr!long.make(123);

            auto w = x.weak;    //weak ptr

            assert(w.expired == false);

            x = SharedPtr!long.make(321);

            assert(w.expired == true);

            SharedPtr!long y = w.lock;

            assert(y == null);
        }
        /+{
            shared SharedPtr!long x = SharedPtr!(shared long).make(123);

            shared SharedPtr!long.WeakType w = x.weak;    //weak ptr

            assert(w.expired == false);

            x = SharedPtr!(shared long).make(321);

            assert(w.expired == true);

            SharedPtr!(shared long) y = w.lock;

            assert(y == null);
        }+/
    }

    //expired
    nothrow @nogc unittest{
        {
            SharedPtr!long x = SharedPtr!long.make(123);

            auto wx = x.weak;   //weak pointer

            assert(wx.expired == false);

            x = null;

            assert(wx.expired == true);
        }
    }

    //make
    pure nothrow @nogc unittest{
        {
            SharedPtr!long a = SharedPtr!long.make();
            assert(a.get == 0);

            SharedPtr!(const long) b = SharedPtr!long.make(2);
            assert(b.get == 2);
        }

        {
            static struct Struct{
                int i = 7;

                this(int i)pure nothrow @safe @nogc{
                    this.i = i;
                }
            }

            SharedPtr!Struct s1 = SharedPtr!Struct.make();
            assert(s1.get.i == 7);

            SharedPtr!Struct s2 = SharedPtr!Struct.make(123);
            assert(s2.get.i == 123);
        }

        static interface Interface{
        }
        static class Class : Interface{
            int i;

            this(int i)pure nothrow @safe @nogc{
                this.i = i;
            }
        }

        {

            SharedPtr!Interface x = SharedPtr!Class.make(3);
            //assert(x.dynTo!Class.get.i == 3);
        }


    }

    //make dynamic array
    pure nothrow @nogc unittest{
        {
            auto arr = SharedPtr!(long[]).make(6, -1);
            assert(arr.length == 6);
            assert(arr.get.length == 6);

            import std.algorithm : all;
            assert(arr.get.all!(x => x == -1));

            for(long i = 0; i < 6; ++i)
                arr.get[i] = i;

            assert(arr.get == [0, 1, 2, 3, 4, 5]);
        }

        {
            static struct Struct{
                int i;
                double d;
            }

            {
                auto a = SharedPtr!(Struct[]).make(6, 42, 3.14);
                assert(a.length == 6);
                assert(a.get.length == 6);

                import std.algorithm : all;
                assert(a.get[].all!(x => (x.i == 42 && x.d == 3.14)));
            }

            {
                auto a = SharedPtr!(Struct[]).make(6);
                assert(a.length == 6);

                import std.algorithm : all;
                assert(a.get[].all!(x => (x.i == int.init)));
            }
        }

        {
            static class Class{
                int i;
                double d;

                this(int i, double d){
                    this.i = i;
                    this.d = d;
                }
            }

            {
                auto a = SharedPtr!(Class[]).make(6, null);
                assert(a.length == 6);

                import std.algorithm : all;
                assert(a.get[].all!(x => x is null));
            }

            {
                auto a = SharedPtr!(Class[]).make(6);
                assert(a.length == 6);

                import std.algorithm : all;
                assert(a.get[].all!(x => x is null));
            }


        }
    }

    //make static array
    pure nothrow @nogc unittest{
        import std.algorithm : all;
        {
            SharedPtr!(long[6]) a = SharedPtr!(long[6]).make();
            assert(a.get.length == 6);
            assert(a.get[].all!(x => x == long.init));
        }
        {
            SharedPtr!(long[6]) a = SharedPtr!(long[6]).make(-1);
            assert(a.get.length == 6);
            assert(a.get[].all!(x => x == -1));
        }
        {
            long[6] tmp = [1, 2, 3, 4, 5, 6];

            SharedPtr!(const(long)[6]) a = SharedPtr!(long[6]).make(tmp);
            assert(a.get.length == 6);
            assert(a.get[]== tmp);
        }
        {
            static struct Struct{
                int i;
                double d;
            }

            auto a = SharedPtr!(Struct[6]).make(42, 3.14);
            assert(a.get.length == 6);

            import std.algorithm : all;
            assert(a.get[].all!(x => (x.i == 42 && x.d == 3.14)));


        }
    }

    //make deleter
    pure nothrow unittest{
        {
            long deleted = -1;
            long tmp = 123;
            auto x = SharedPtr!long.make(&tmp, (long* data){
                deleted = *data;
            });
            assert(deleted == -1);
            assert(*x == 123);

            x = null;
            assert(deleted == 123);
        }
    }

    //alloc
    pure nothrow @nogc unittest{
        {
            TestAllocator allocator;

            {
                SharedPtr!long a = SharedPtr!long.alloc(&allocator);
                assert(a.get == 0);

                SharedPtr!(const long) b = SharedPtr!long.alloc(&allocator, 2);
                assert(b.get == 2);
            }

            {
                static struct Struct{
                    int i = 7;

                    this(int i)pure nothrow @safe @nogc{
                        this.i = i;
                    }
                }

                SharedPtr!Struct s1 = SharedPtr!Struct.alloc(allocator);
                assert(s1.get.i == 7);

                SharedPtr!Struct s2 = SharedPtr!Struct.alloc(allocator, 123);
                assert(s2.get.i == 123);
            }

            static interface Interface{
            }
            static class Class : Interface{
                int i;

                this(int i)pure nothrow @safe @nogc{
                    this.i = i;
                }
            }


            debug assert(_conter_gc_ranges == 0);

            {


                SharedPtr!Interface x = SharedPtr!Class.alloc(&allocator, 3);
                assert(x.useCount == 1);
                //assert(x.dynTo!Class.get.i == 3);
            }

            debug assert(_conter_gc_ranges == 0);

        }
    }

    //alloc
    unittest{

        {
            import std.experimental.allocator : allocatorObject;

            auto a = allocatorObject(Mallocator.instance);
            {
                SharedPtr!long x = SharedPtr!long.alloc(a);
                assert(x.get == 0);

                SharedPtr!(const long) y = SharedPtr!long.alloc(a, 2);
                assert(y.get == 2);
            }

            {
                static struct Struct{
                    int i = 7;

                    this(int i)pure nothrow @safe @nogc{
                        this.i = i;
                    }
                }

                SharedPtr!Struct s1 = SharedPtr!Struct.alloc(a);
                assert(s1.get.i == 7);

                SharedPtr!Struct s2 = SharedPtr!Struct.alloc(a, 123);
                assert(s2.get.i == 123);
            }

            {
                static interface Interface{
                }
                static class Class : Interface{
                    int i;

                    this(int i)pure nothrow @safe @nogc{
                        this.i = i;
                    }
                }

                SharedPtr!Interface x = SharedPtr!Class.alloc(a, 3);
                //assert(x.dynTo!Class.get.i == 3);
            }

        }
    }

    //alloc array
    nothrow unittest{
        {
            import std.experimental.allocator : allocatorObject;

            auto a = allocatorObject(Mallocator.instance);
            auto arr = SharedPtr!(long[], DestructorType!(typeof(a))).alloc(a, 6, -1);
            assert(arr.length == 6);
            assert(arr.get.length == 6);

            import std.algorithm : all;
            assert(arr.get.all!(x => x == -1));

            for(long i = 0; i < 6; ++i)
                arr.get[i] = i;

            assert(arr.get == [0, 1, 2, 3, 4, 5]);
        }
    }

    //alloc deleter
    nothrow unittest{
        import std.experimental.allocator : make, dispose, allocatorObject;

        auto a = allocatorObject(Mallocator.instance);

        long deleted = -1;
        auto x = SharedPtr!long.alloc(a, a.make!long(123), (long* data){
            deleted = *data;
            a.dispose(data);
        });
        assert(deleted == -1);
        assert(*x == 123);

        x = null;
        assert(deleted == 123);
    }

    //ctor
    pure nothrow @nogc @safe unittest{

        {
            SharedPtr!long x = SharedPtr!long.make(123);
            assert(x.useCount == 1);

            SharedPtr!long a = x;         //lvalue copy ctor
            assert(a == x);

            const SharedPtr!long b = x;   //lvalue copy ctor
            assert(b == x);

            SharedPtr!(const long) c = x; //lvalue ctor
            assert(c == x);

            const SharedPtr!long d = b;   //lvalue ctor
            assert(d == x);

            assert(x.useCount == 5);
        }

        {
            import core.lifetime : move;
            SharedPtr!long x = SharedPtr!long.make(123);
            assert(x.useCount == 1);

            SharedPtr!long a = move(x);        //rvalue copy ctor
            assert(a.useCount == 1);

            const SharedPtr!long b = move(a);  //rvalue copy ctor
            assert(b.useCount == 1);

            SharedPtr!(const long) c = b.load;  //rvalue ctor
            assert(c.useCount == 2);

            const SharedPtr!long d = move(c);  //rvalue ctor
            assert(d.useCount == 2);
        }

        {
            import core.lifetime : move;
            auto u = UniquePtr!(long, DefaultSharedControlBlock).make(123);

            SharedPtr!long s = move(u);        //rvalue copy ctor
            assert(s != null);
            assert(s.useCount == 1);

            SharedPtr!long s2 = UniquePtr!(long, DefaultSharedControlBlock).init;
            assert(s2 == null);

        }

        {
            import core.lifetime : move;
            auto rc = RcPtr!(long).make(123);
            assert(rc.useCount == 1);

            SharedPtr!long s = rc;
            assert(s != null);
            assert(s.useCount == 2);
            assert(rc.useCount == 2);

            SharedPtr!long s2 = RcPtr!(long).init;
            assert(s2 == null);
        }

    }

    //weak
    pure nothrow @nogc unittest{
        SharedPtr!long x = SharedPtr!long.make(123);
        assert(x.useCount == 1);
        auto wx = x.weak;   //weak pointer
        assert(wx.expired == false);
        assert(wx.lock.get == 123);
        assert(wx.useCount == 1);
        x = null;
        assert(wx.expired == true);
        assert(wx.useCount == 0);

    }

    //operator *
    pure nothrow @nogc unittest{

        SharedPtr!long x = SharedPtr!long.make(123);
        assert(*x == 123);
        (*x = 321);
        assert(*x == 321);
        const y = x;
        assert(*y == 321);
        assert(*x == 321);
        static assert(is(typeof(*y) == const long));
    }

    //get
    pure nothrow @nogc unittest{
        SharedPtr!long x = SharedPtr!long.make(123);
        assert(x.get == 123);
        x.get = 321;
        assert(x.get == 321);
        const y = x;
        assert(y.get == 321);
        assert(x.get == 321);
        static assert(is(typeof(y.get) == const long));
    }

    //element
    pure nothrow @nogc unittest{
        SharedPtr!long x = SharedPtr!long.make(123);
        assert(*x.element == 123);
        x.get = 321;
        assert(*x.element == 321);
        const y = x;
        assert(*y.element == 321);
        assert(*x.element == 321);
        static assert(is(typeof(y.element) == const(long)*));
    }

    //opCast bool
    @safe pure nothrow @nogc unittest{
        SharedPtr!long x = SharedPtr!long.make(123);
        assert(cast(bool)x);    //explicit cast
        assert(x);              //implicit cast
        x = null;
        assert(!cast(bool)x);   //explicit cast
        assert(!x);             //implicit cast
    }

    //opCast SharedPtr
    @safe pure nothrow @nogc unittest{
        SharedPtr!long x = SharedPtr!long.make(123);
        auto y = cast(SharedPtr!(const long))x;
        auto z = cast(const SharedPtr!long)x;
        auto u = cast(const SharedPtr!(const long))x;
        assert(x.useCount == 4);
    }

    //opEquals SharedPtr
    pure @safe nothrow @nogc unittest{
        {
            SharedPtr!long x = SharedPtr!long.make(0);
            assert(x != null);
            x = null;
            assert(x == null);
        }

        {
            SharedPtr!long x = SharedPtr!long.make(123);
            SharedPtr!long y = SharedPtr!long.make(123);
            assert(x == x);
            assert(y == y);
            assert(x != y);
        }

        {
            SharedPtr!long x;
            SharedPtr!(const long) y;
            assert(x == x);
            assert(y == y);
            assert(x == y);
        }
    }

    //opEquals SharedPtr
    pure nothrow @nogc unittest{
        {
            SharedPtr!long x = SharedPtr!long.make(123);
            SharedPtr!long y = SharedPtr!long.make(123);
            assert(x == x.element);
            assert(y.element == y);
            assert(x != y.element);
        }
    }

    //opCmp
    pure nothrow @safe @nogc unittest{ 
        {
            const a = SharedPtr!long.make(42);
            const b = SharedPtr!long.make(123);
            const n = SharedPtr!long.init;

            assert(a <= a);
            assert(a >= a);

            assert((a < b) == !(a >= b));
            assert((a > b) == !(a <= b));

            assert(a > n);
            assert(a > null);
            
            assert(n < a);
            assert(null < a);
        }
    }

    //opCmp
    pure nothrow @nogc unittest{
        {
            const a = SharedPtr!long.make(42);
            const b = SharedPtr!long.make(123);

            assert(a <= a.element);
            assert(a.element >= a);

            assert((a < b.element) == !(a.element >= b));
            assert((a > b.element) == !(a.element <= b));
        }
    }

    //toHash
    pure nothrow @safe @nogc unittest{
        {
            SharedPtr!long x = SharedPtr!long.make(123);
            SharedPtr!long y = SharedPtr!long.make(123);
            assert(x.toHash == x.toHash);
            assert(y.toHash == y.toHash);
            assert(x.toHash != y.toHash);
            SharedPtr!(const long) z = x;
            assert(x.toHash == z.toHash);
        }
        {
            SharedPtr!long x;
            SharedPtr!(const long) y;
            assert(x.toHash == x.toHash);
            assert(y.toHash == y.toHash);
            assert(x.toHash == y.toHash);
        }
    }

    //proxySwap
    pure nothrow @nogc unittest{
        {
            SharedPtr!long a = SharedPtr!long.make(1);
            SharedPtr!long b = SharedPtr!long.make(2);
            a.proxySwap(b);
            assert(*a == 2);
            assert(*b == 1);
            import std.algorithm : swap;
            swap(a, b);
            assert(*a == 1);
            assert(*b == 2);
            assert(a.useCount == 1);
            assert(b.useCount == 1);
        }
    }

    //length
    pure nothrow @nogc unittest{
        auto x = SharedPtr!(int[]).make(10, -1);
        assert(x.length == 10);
        assert(x.get.length == 10);

        import std.algorithm : all;
        assert(x.get.all!(i => i == -1));
    }

}

pure nothrow @safe @nogc unittest{
    SharedPtr!void u = SharedPtr!void.make();
}
