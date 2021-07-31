/**
    Implementation of reference counted pointer `IntrusivePtr` (similar to `RcPtr`).

    License:   $(HTTP www.boost.org/LICENSE_1_0.txt, Boost License 1.0).
    Authors:   $(HTTP github.com/submada/basic_string, Adam Búš)
*/
module autoptr.intrusive_ptr;

import autoptr.internal.mallocator : Mallocator;
import autoptr.internal.traits;

import autoptr.common;
import autoptr.unique_ptr : isUniquePtr, UniquePtr;




/**
    Check if type `T` is `IntrusivePtr` and has valid type qualifiers.
*/
public template isValidIntrusivePtr(T){
    import std.traits : Unqual;

    static if(is(Unqual!T == IntrusivePtr!Args, Args...)){
        enum bool impl = true
            && (!is(T == shared) || is(T.ControlType == shared));
    }
    else{
        enum bool impl = false;
    }

    enum bool isValidIntrusivePtr = impl;
}

///
unittest{
     static class Foo{
        ControlBlock!(int, int) control;
    }

    static assert(isIntrusive!Foo);

    static assert(isValidIntrusivePtr!(IntrusivePtr!Foo));

    static assert(isValidIntrusivePtr!(IntrusivePtr!Foo));
    static assert(isValidIntrusivePtr!(IntrusivePtr!(const Foo)));
    static assert(isValidIntrusivePtr!(IntrusivePtr!(shared Foo)));
    static assert(isValidIntrusivePtr!(IntrusivePtr!(const shared Foo)));


    static assert(isValidIntrusivePtr!(immutable IntrusivePtr!Foo));
    static assert(isValidIntrusivePtr!(immutable IntrusivePtr!(const Foo)));
    static assert(isValidIntrusivePtr!(immutable IntrusivePtr!(shared Foo)));
    static assert(isValidIntrusivePtr!(immutable IntrusivePtr!(const shared Foo)));

}


/**
    Check if type `T` is `IntrusivePtr`.
*/
public template isIntrusivePtr(T){
    import std.traits : Unqual;

    enum bool isIntrusivePtr = is(Unqual!T == IntrusivePtr!Args, Args...);
}

///
unittest{
    static assert(!isIntrusivePtr!long);
    static assert(!isIntrusivePtr!(void*));

    static struct Foo{
        ControlBlock!(int, int) control;
    }
    static assert(isIntrusivePtr!(IntrusivePtr!Foo));
    static assert(isIntrusivePtr!(IntrusivePtr!Foo.WeakType));
}



/**
    `IntrusivePtr` is a smart pointer that retains shared ownership of an object through a pointer.

    Several `IntrusivePtr` objects may own the same object.

    The object is destroyed and its memory deallocated when either of the following happens:

        1. the last remaining `IntrusivePtr` owning the object is destroyed.

        2. the last remaining `IntrusivePtr` owning the object is assigned another pointer via various methods like `opAssign` and `store`.

    The object is destroyed using destructor of type `_Type`.

    A `IntrusivePtr` can not share ownership of an object while storing a pointer to another object (use `SharedPtr` for that).

    A `IntrusivePtr` may also own no objects, in which case it is called empty.

    `_Type` must contain one property of type `ControlBlock` or `MutableControlBlock` (this property contains ref counting). If this property is `shared` then ref counting is atomic.

    If `_Type` is const/immutable then ControlBlock cannot be modified => ref counting doesn't work and `IntrusivePtr` can be only moved.

    If multiple threads of execution access the same `IntrusivePtr` (`shared IntrusivePtr`) then only some methods can be called (`load`, `store`, `exchange`, `compareExchange`, `useCount`).

    Template parameters:

        `_Type` type of managed object

        `_DestructorType` function pointer with attributes of destructor, to get attributes of destructor from type use `autoptr.common.DestructorType!T`. Destructor of type `_Type` must be compatible with `_DestructorType`

        `_weakPtr` if `true` then `IntrusivePtr` represent weak ptr

*/
public template IntrusivePtr(
    _Type,
    _DestructorType = DestructorType!_Type,
    bool _weakPtr = false
)
if(isIntrusive!_Type && isDestructorType!_DestructorType){
    static assert(is(_Type == struct) || is(_Type == class));
    static assert(isIntrusive!_Type == 1);

    alias _ControlType = IntrusivControlBlock!_Type;

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
        static assert(!__traits(isNested, _Type), "IntrusivePtr does not support nested types.");


    import std.experimental.allocator : stateSize;
    import std.meta : AliasSeq;
    import std.range : ElementEncodingType;
    import std.traits: Unqual, Unconst, CopyTypeQualifiers, CopyConstness, PointerTarget,
        hasIndirections, hasElaborateDestructor,
        isMutable, isAbstractClass, isDynamicArray, isStaticArray, isCallable, Select, isArray;

    import core.atomic : MemoryOrder;
    import core.lifetime : forward;

    enum bool hasWeakCounter = _ControlType.hasWeakCounter;

    enum bool hasSharedCounter = _ControlType.hasSharedCounter;

    
    alias MakeIntrusive(AllocatorType, bool supportGC) = .MakeIntrusive!(
        _Type,
        _DestructorType,
        AllocatorType,
        supportGC
    );

    enum bool _isLockFree = true;

    struct IntrusivePtr{
        /**
            Type of element managed by `IntrusivePtr`.
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
            `true` if `ElementType` has mutable intrusive control block even if `ElementType` is `const`/`immutable`.
        */
        public enum bool mutableControl = isMutable!(IntrusivControlBlock!(const ElementType));


        /**
            `true` if `ControlBlock` is shared
        */
        public enum bool sharedControl = is(IntrusivControlBlock!(ElementType, true) == shared);


        /**
            `true` if `IntrusivePtr` is weak ptr.
        */
        public enum bool weakPtr = _weakPtr;


        /**
            Same as `ElementType*` or `ElementType` if is class/interface/slice.
        */
        public alias ElementReferenceType = ElementReferenceTypeImpl!ElementType;


        /**
            Weak pointer

            `IntrusivePtr.WeakType` is a smart pointer that holds a non-owning ("weak") reference to an object that is managed by `IntrusivePtr`.
            It must be converted to `IntrusivePtr` in order to access the referenced object.

            `IntrusivePtr.WeakType` models temporary ownership: when an object needs to be accessed only if it exists, and it may be deleted at any time by someone else,
            `IntrusivePtr.WeakType` is used to track the object, and it is converted to `IntrusivePtr` to assume temporary ownership.
            If the original `IntrusivePtr` is destroyed at this time, the object's lifetime is extended until the temporary `IntrusivePtr` is destroyed as well.

            Another use for `IntrusivePtr.WeakType` is to break reference cycles formed by objects managed by `IntrusivePtr`.
            If such cycle is orphaned (i,e. there are no outside shared pointers into the cycle), the `IntrusivePtr` reference counts cannot reach zero and the memory is leaked.
            To prevent this, one of the pointers in the cycle can be made weak.
        */
        static if(hasWeakCounter && !weakPtr)
        public alias WeakType = IntrusivePtr!(
            _Type,
            _DestructorType,
            true
        );


        /**
            Type of non weak ptr (must have weak counter).
        */
        static if(weakPtr)
        public alias SharedType = IntrusivePtr!(
            _Type,
            _DestructorType,
            false
        );



        /**
            `true` if shared `IntrusivePtr` has lock free operations `store`, `load`, `exchange`, `compareExchange`, otherwise 'false'
        */
        public alias isLockFree = _isLockFree;

        static if(isLockFree)
        static assert(ElementReferenceType.sizeof == size_t.sizeof);



        /**
            Destructor

            If `this` owns an object and it is the last `IntrusivePtr` owning it, the object is destroyed.
            After the destruction, the smart pointers that shared ownership with `this`, if any, will report a `useCount()` that is one less than its previous value.
        */
        public ~this(){
            this._release();
        }


        //necesary for autoptr.unique_ptr.sharedPtr
        package this(Elm, this This)(Elm element)pure nothrow @safe @nogc
        if(true
            && is(Elm : GetElementReferenceType!This)
            && !is(Unqual!Elm == typeof(null))
        ){
            this._element = element;
        }

        //copy ctor
        package this(Rhs, this This)(ref scope Rhs rhs, Evoid ctor)@trusted
        if(true
            && isIntrusivePtr!Rhs
            && isCopyable!(Rhs, This)
            && !needLock!(Rhs, This)
            && !is(Rhs == shared)
        ){
            static assert(isValidIntrusivePtr!This, "`This` is invalid `IntrusivePtr`");
            static assert(isValidIntrusivePtr!Rhs, "`Rhs` is invalid `IntrusivePtr`");

            if(rhs._element is null){
                this(null);
            }
            else{
                this(rhs._element);
                rhs._control.add!weakPtr;
            }
        }


        /**
            Constructs a `IntrusivePtr` without managed object. Same as `IntrusivePtr.init`

            Examples:
                --------------------
                static struct Foo{
                    ControlBlock!(int, int) c;
                }

                {
                    IntrusivePtr!Foo x = null;

                    assert(x == null);
                    assert(x == IntrusivePtr!Foo.init);
                }
                --------------------
        */
        public this(this This)(typeof(null) nil)pure nothrow @safe @nogc{
            static assert(isValidIntrusivePtr!This, "`This` is invalid `IntrusivePtr`");
        }



        /**
            Constructs a `IntrusivePtr` which shares ownership of the object managed by `rhs`.

            If rhs manages no object, this manages no object too.
            If rhs if rvalue then ownership is moved.
            The template overload doesn't participate in overload resolution if ElementType of `typeof(rhs)` is not implicitly convertible to `ElementType`.
            If rhs if `WeakType` then this ctor is equivalent to `this(rhs.lock())`.

            Examples:
                --------------------
                static struct Foo{
                    MutableControlBlock!(int, int) c;
                    int i;

                    this(int i)pure nothrow @safe @nogc{
                        this.i = i;
                    }
                }

                {
                    IntrusivePtr!Foo x = IntrusivePtr!Foo.make(123);
                    assert(x.useCount == 1);

                    IntrusivePtr!Foo a = x;         //lvalue copy ctor
                    assert(a == x);

                    const IntrusivePtr!Foo b = x;   //lvalue copy ctor
                    assert(b == x);

                    IntrusivePtr!Foo c = x; //lvalue ctor
                    assert(c == x);

                    const IntrusivePtr!Foo d = b;   //lvalue ctor
                    assert(d == x);

                    assert(x.useCount == 5);
                }

                {
                    import core.lifetime : move;
                    IntrusivePtr!Foo x = IntrusivePtr!Foo.make(123);
                    assert(x.useCount == 1);

                    IntrusivePtr!Foo a = move(x);        //rvalue copy ctor
                    assert(a.useCount == 1);

                    const IntrusivePtr!Foo b = move(a);  //rvalue copy ctor
                    assert(b.useCount == 1);

                    IntrusivePtr!(const Foo) c = b.load;  //rvalue ctor
                    assert(c.useCount == 2);

                    const IntrusivePtr!Foo d = move(c);  //rvalue ctor
                    assert(d.useCount == 2);
                }
                --------------------
        */
        public this(Rhs, this This)(ref scope Rhs rhs)@safe
        if(true
            && isIntrusivePtr!Rhs
            && !is(Unqual!This == Unqual!Rhs)   ///copy ctors
            && isCopyable!(Rhs, This)
            && !needLock!(Rhs, This)
            && !is(Rhs == shared)
        ){
            static assert(isValidIntrusivePtr!This, "`This` is invalid `IntrusivePtr`");
            static assert(isValidIntrusivePtr!Rhs, "`Rhs` is invalid `IntrusivePtr`");

            this(rhs, Evoid.init);
        }

        /// ditto
        public this(Rhs, this This)(scope Rhs rhs)@trusted
        if(true
            && isIntrusivePtr!Rhs
            //&& !is(Unqual!This == Unqual!Rhs) //TODO move ctors need this
            && isMovable!(Rhs, This)
            && !needLock!(Rhs, This)
            && !is(Rhs == shared)
        ){
            static assert(isValidIntrusivePtr!This, "`This` is invalid `IntrusivePtr`");
            static assert(isValidIntrusivePtr!Rhs, "`Rhs` is invalid `IntrusivePtr`");

            this._element = rhs._element;
            rhs._const_reset();
        }

        /// ditto
        public this(Rhs, this This)(auto ref scope Rhs rhs)@trusted
        if(true
            && isIntrusivePtr!Rhs
            && isCopyable!(Rhs, This)   ///lock robi vzdy copiu
            && needLock!(Rhs, This)
            && !is(Rhs == shared)
        ){
            static assert(isValidIntrusivePtr!This, "`This` is invalid `IntrusivePtr`");
            static assert(isValidIntrusivePtr!Rhs, "`Rhs` is invalid `IntrusivePtr`");

            if(rhs._element !is null && rhs._control.add_shared_if_exists())
                this._element = rhs._element;
            else
                this._element = null;
        }


        //copy ctors:
        //mutable:
        static if(is(Unqual!ElementType == ElementType)){
            //mutable rhs:
            static if(isMutable!ControlType || mutableControl){
                this(ref scope typeof(this) rhs)@safe{this(rhs, Evoid.init);}
                this(ref scope typeof(this) rhs)const @safe{this(rhs, Evoid.init);}
            }
            else{
                @disable this(ref scope typeof(this) rhs)@safe;
                @disable this(ref scope typeof(this) rhs)const @safe;
            }
            @disable this(ref scope typeof(this) rhs)immutable @safe;
            @disable this(ref scope typeof(this) rhs)shared @safe;
            @disable this(ref scope typeof(this) rhs)const shared @safe;

            //const rhs:
            @disable this(ref scope const typeof(this) rhs)@safe;
            static if(mutableControl)
                this(ref scope const typeof(this) rhs)const @safe{this(rhs, Evoid.init);}
            else
                @disable this(ref scope const typeof(this) rhs)const @safe;
            @disable this(ref scope const typeof(this) rhs)immutable @safe;
            @disable this(ref scope const typeof(this) rhs)shared @safe;
            @disable this(ref scope const typeof(this) rhs)const shared @safe;

            //immutable(Ptr) iptr;
            @disable this(ref scope immutable typeof(this) rhs)@safe;
            static if(mutableControl){
                this(ref scope immutable typeof(this) rhs)const @safe{this(rhs, Evoid.init);}
                this(ref scope immutable typeof(this) rhs)immutable @safe{this(rhs, Evoid.init);}
            }
            else{
                @disable this(ref scope immutable typeof(this) rhs)const @safe;
                @disable this(ref scope immutable typeof(this) rhs)immutable @safe;
            }
            @disable this(ref scope immutable typeof(this) rhs)shared @safe;
            static if(is(ControlType == shared) && (isMutable!ControlType || mutableControl))
                this(ref scope immutable typeof(this) rhs)const shared @safe{this(rhs, Evoid.init);}
            else
                @disable this(ref scope immutable typeof(this) rhs)const shared @safe;

        }
        //const:
        else static if(is(const Unqual!ElementType == ElementType)){
            //mutable rhs:
            static if(mutableControl){
                this(ref scope typeof(this) rhs)@safe{this(rhs, Evoid.init);}
                this(ref scope typeof(this) rhs)const @safe{this(rhs, Evoid.init);}
            }
            else{
                @disable this(ref scope typeof(this) rhs)@safe;
                @disable this(ref scope typeof(this) rhs)const @safe;
            }
            @disable this(ref scope typeof(this) rhs)immutable @safe;
            @disable this(ref scope typeof(this) rhs)shared @safe;
            @disable this(ref scope typeof(this) rhs)const shared @safe;

            //const rhs:
            static if(mutableControl){
                this(ref scope const typeof(this) rhs)@safe{this(rhs, Evoid.init);}
                this(ref scope const typeof(this) rhs)const @safe{this(rhs, Evoid.init);}
            }
            else{
                @disable this(ref scope const typeof(this) rhs)@safe;
                @disable this(ref scope const typeof(this) rhs)const @safe;
            }
            @disable this(ref scope const typeof(this) rhs)immutable @safe;
            @disable this(ref scope const typeof(this) rhs)shared @safe;
            @disable this(ref scope const typeof(this) rhs)const shared @safe;

            //immutable rhs:
            static if(mutableControl){
                this(ref scope immutable typeof(this) rhs)@safe{this(rhs, Evoid.init);}
                this(ref scope immutable typeof(this) rhs)const @safe{this(rhs, Evoid.init);}
                this(ref scope immutable typeof(this) rhs)immutable @safe{this(rhs, Evoid.init);}
            }
            else{
                @disable this(ref scope immutable typeof(this) rhs)@safe;
                @disable this(ref scope immutable typeof(this) rhs)const @safe;
                @disable this(ref scope immutable typeof(this) rhs)immutable @safe;
            }
            static if(is(ControlType == shared) && mutableControl){
                this(ref scope immutable typeof(this) rhs)shared @safe{this(rhs, Evoid.init);}
                this(ref scope immutable typeof(this) rhs)const shared @safe{this(rhs, Evoid.init);}
            }
            else{
                @disable this(ref scope immutable typeof(this) rhs)shared @safe;
                @disable this(ref scope immutable typeof(this) rhs)const shared @safe;
            }
        }
        //immutable:
        else static if(is(immutable Unqual!ElementType == ElementType)){
            //mutable rhs:
            static if(mutableControl){
                this(ref scope typeof(this) rhs)@safe{this(rhs, Evoid.init);}
                this(ref scope typeof(this) rhs)const @safe{this(rhs, Evoid.init);}
                this(ref scope typeof(this) rhs)immutable @safe{this(rhs, Evoid.init);}
            }
            else{
                @disable this(ref scope typeof(this) rhs)@safe;
                @disable this(ref scope typeof(this) rhs)const @safe;
                @disable this(ref scope typeof(this) rhs)immutable @safe;
            }
            static if(is(ControlType == shared) && mutableControl){
                this(ref scope typeof(this) rhs)shared @safe{this(rhs, Evoid.init);}
                this(ref scope typeof(this) rhs)const shared @safe{this(rhs, Evoid.init);}
            }
            else{
                @disable this(ref scope typeof(this) rhs)shared @safe;
                @disable this(ref scope typeof(this) rhs)const shared @safe;
            }

            //const rhs:
            static if(mutableControl){
                this(ref scope const typeof(this) rhs)@safe{this(rhs, Evoid.init);}
                this(ref scope const typeof(this) rhs)const @safe{this(rhs, Evoid.init);}
                this(ref scope const typeof(this) rhs)immutable @safe{this(rhs, Evoid.init);}	//??
            }
            else{
                @disable this(ref scope const typeof(this) rhs)@safe;
                @disable this(ref scope const typeof(this) rhs)const @safe;
                @disable this(ref scope const typeof(this) rhs)immutable @safe;
            }
            static if(is(ControlType == shared) && mutableControl){
                this(ref scope const typeof(this) rhs)shared @safe{this(rhs, Evoid.init);}
                this(ref scope const typeof(this) rhs)const shared @safe{this(rhs, Evoid.init);}
            }
            else{
                @disable this(ref scope const typeof(this) rhs)shared @safe;
                @disable this(ref scope const typeof(this) rhs)const shared @safe;
            }

            //immutable rhs:
            static if(mutableControl){
                this(ref scope immutable typeof(this) rhs)@safe{this(rhs, Evoid.init);}	//??
                this(ref scope immutable typeof(this) rhs)const @safe{this(rhs, Evoid.init);}
                this(ref scope immutable typeof(this) rhs)immutable @safe{this(rhs, Evoid.init);}
            }
            else{
                @disable this(ref scope immutable typeof(this) rhs)@safe;
                @disable this(ref scope immutable typeof(this) rhs)const @safe;
                @disable this(ref scope immutable typeof(this) rhs)immutable @safe;
            }
            static if(is(ControlType == shared) && mutableControl){
                this(ref scope immutable typeof(this) rhs)shared @safe{this(rhs, Evoid.init);}
                this(ref scope immutable typeof(this) rhs)const shared @safe{this(rhs, Evoid.init);}
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
            static if(isMutable!ControlType || mutableControl){
                this(ref scope typeof(this) rhs)@safe{this(rhs, Evoid.init);}
                this(ref scope typeof(this) rhs)const @safe{this(rhs, Evoid.init);}
            }
            else{
                @disable this(ref scope typeof(this) rhs)@safe;
                @disable this(ref scope typeof(this) rhs)const @safe;
            }
            @disable this(ref scope typeof(this) rhs)immutable @safe;
            static if(is(ControlType == shared) && (isMutable!ControlType || mutableControl)){
                this(ref scope typeof(this) rhs)shared @safe{this(rhs, Evoid.init);}
                this(ref scope typeof(this) rhs)const shared @safe{this(rhs, Evoid.init);}
            }
            else{
                @disable this(ref scope typeof(this) rhs)shared @safe;
                @disable this(ref scope typeof(this) rhs)const shared @safe;
            }

            //const rhs:
            @disable this(ref scope const typeof(this) rhs)@safe;
            static if(mutableControl)
                this(ref scope const typeof(this) rhs)const @safe{this(rhs, Evoid.init);}
            else
                @disable this(ref scope const typeof(this) rhs)const @safe;
            @disable this(ref scope const typeof(this) rhs)immutable @safe;
            @disable this(ref scope const typeof(this) rhs)shared @safe;
            static if(is(ControlType == shared) && mutableControl)
                this(ref scope const typeof(this) rhs)const shared @safe{this(rhs, Evoid.init);}
            else
                @disable this(ref scope const typeof(this) rhs)const shared @safe;

            //immutable rhs:
            @disable this(ref scope immutable typeof(this) rhs)@safe;
            static if(mutableControl){
                this(ref scope immutable typeof(this) rhs)const @safe{this(rhs, Evoid.init);}
                this(ref scope immutable typeof(this) rhs)immutable @safe{this(rhs, Evoid.init);}
            }
            else{
                @disable this(ref scope immutable typeof(this) rhs)const @safe;
                @disable this(ref scope immutable typeof(this) rhs)immutable @safe;
            }
            @disable this(ref scope immutable typeof(this) rhs)shared @safe;
            static if(is(ControlType == shared) && mutableControl)
                this(ref scope immutable typeof(this) rhs)const shared @safe{this(rhs, Evoid.init);}
            else
                @disable this(ref scope immutable typeof(this) rhs)const shared @safe;
        }
        //shared const:
        else static if(is(const shared Unqual!ElementType == ElementType)){
            //static assert(!threadLocal);

            //mutable rhs:
            static if(mutableControl){
                this(ref scope typeof(this) rhs)@safe{this(rhs, Evoid.init);}
                this(ref scope typeof(this) rhs)const @safe{this(rhs, Evoid.init);}
            }
            else{
                @disable this(ref scope typeof(this) rhs)@safe;
                @disable this(ref scope typeof(this) rhs)const @safe;
            }
            @disable this(ref scope typeof(this) rhs)immutable @safe;
            static if(is(ControlType == shared) && mutableControl){
                this(ref scope typeof(this) rhs)shared @safe{this(rhs, Evoid.init);}
                this(ref scope typeof(this) rhs)const shared @safe{this(rhs, Evoid.init);}
            }
            else{
                @disable this(ref scope typeof(this) rhs)shared @safe;
                @disable this(ref scope typeof(this) rhs)const shared @safe;
            }

            //const rhs:
            static if(mutableControl){
                this(ref scope const typeof(this) rhs)@safe{this(rhs, Evoid.init);}
                this(ref scope const typeof(this) rhs)const @safe{this(rhs, Evoid.init);}
            }
            else{
                @disable this(ref scope const typeof(this) rhs)@safe;
                @disable this(ref scope const typeof(this) rhs)const @safe;
            }
            @disable this(ref scope const typeof(this) rhs)immutable @safe;
            static if(is(ControlType == shared) && mutableControl){
                this(ref scope const typeof(this) rhs)shared @safe{this(rhs, Evoid.init);}
                this(ref scope const typeof(this) rhs)const shared @safe{this(rhs, Evoid.init);}
            }
            else{
                @disable this(ref scope const typeof(this) rhs)shared @safe;
                @disable this(ref scope const typeof(this) rhs)const shared @safe;
            }

            //immutable rhs:
            static if(mutableControl){
                this(ref scope immutable typeof(this) rhs)@safe{this(rhs, Evoid.init);}	//??
                this(ref scope immutable typeof(this) rhs)const @safe{this(rhs, Evoid.init);}
                this(ref scope immutable typeof(this) rhs)immutable @safe{this(rhs, Evoid.init);}
            }
            else{
                @disable this(ref scope immutable typeof(this) rhs)@safe;
                @disable this(ref scope immutable typeof(this) rhs)const @safe;
                @disable this(ref scope immutable typeof(this) rhs)immutable @safe;
            }
            static if(is(ControlType == shared) && mutableControl){
                this(ref scope immutable typeof(this) rhs)shared @safe{this(rhs, Evoid.init);}
                this(ref scope immutable typeof(this) rhs)const shared @safe{this(rhs, Evoid.init);}
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
                static struct Foo{
                    ControlBlock!(int, int) c;
                    int i;

                    this(int i)pure nothrow @safe @nogc{
                        this.i = i;
                    }
                }

                {
                    IntrusivePtr!Foo x = IntrusivePtr!Foo.make(1);

                    assert(x.useCount == 1);
                    x = null;
                    assert(x.useCount == 0);
                    assert(x == null);
                }

                {
                    IntrusivePtr!(shared Foo) x = IntrusivePtr!(shared Foo).make(1);

                    assert(x.useCount == 1);
                    x = null;
                    assert(x.useCount == 0);
                    assert(x == null);
                }

                {
                    shared IntrusivePtr!(shared Foo) x = IntrusivePtr!(shared Foo).make(1);

                    assert(x.useCount == 1);
                    x = null;
                    assert(x.useCount == 0);
                    assert(x.load == null);

                }
                --------------------
        */
        public void opAssign(MemoryOrder order = MemoryOrder.seq, this This)(typeof(null) nil)scope
        if(isMutable!This){
            static assert(isValidIntrusivePtr!This, "`This` is invalid `IntrusivePtr`");

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
                    return this.lockIntrusivePtr!(
                        (ref scope self) => self.opAssign!order(null)
                    )();
                }
            }
            else{
                this._release();
                ()@trusted{
                    this._reset();
                }();
            }
        }

        /**
            Shares ownership of the object managed by `rhs`.

            If `rhs` manages no object, `this` manages no object too.
            If `rhs` is rvalue then move-assigns a `IntrusivePtr` from `rhs`

            Examples:
                --------------------
                static struct Foo{
                    MutableControlBlock!(int, int) c;
                    int i;

                    this(int i)pure nothrow @safe @nogc{
                        this.i = i;
                    }
                }

                {
                    IntrusivePtr!Foo px1 = IntrusivePtr!Foo.make(1);
                    IntrusivePtr!Foo px2 = IntrusivePtr!Foo.make(2);

                    assert(px2.useCount == 1);
                    px1 = px2;
                    assert(px1.get.i == 2);
                    assert(px2.useCount == 2);
                }


                {
                    IntrusivePtr!(Foo) px = IntrusivePtr!(Foo).make(1);
                    IntrusivePtr!(const Foo) pcx = IntrusivePtr!(Foo).make(2);

                    assert(px.useCount == 1);
                    pcx = px;
                    assert(pcx.get.i == 1);
                    assert(pcx.useCount == 2);
                }


                {
                    const IntrusivePtr!(Foo) cpx = IntrusivePtr!(Foo).make(1);
                    IntrusivePtr!(const Foo) pcx = IntrusivePtr!(Foo).make(2);

                    assert(pcx.useCount == 1);
                    pcx = cpx;
                    assert(pcx.get.i == 1);
                    assert(pcx.useCount == 2);
                }

                {
                    IntrusivePtr!(immutable Foo) pix = IntrusivePtr!(immutable Foo).make(123);
                    IntrusivePtr!(const Foo) pcx = IntrusivePtr!(Foo).make(2);

                    assert(pix.useCount == 1);
                    pcx = pix;
                    assert(pcx.get.i == 123);
                    assert(pcx.useCount == 2);
                }
                --------------------
        */
        public void opAssign(MemoryOrder order = MemoryOrder.seq, Rhs, this This)(ref scope Rhs desired)scope
        if(true
            && isIntrusivePtr!Rhs
            && isMutable!This
            && isCopyable!(Rhs, This)
            && !needLock!(Rhs, This)
            && !is(Rhs == shared)
        ){
            static assert(isValidIntrusivePtr!This, "`This` is invalid `IntrusivePtr`");
            static assert(isValidIntrusivePtr!Rhs, "`Rhs` is invalid `IntrusivePtr`");

            if((()@trusted => cast(const void*)&desired is cast(const void*)&this)())
                return;

            static if(is(This == shared)){

                static if(isLockFree){
                    import core.atomic : atomicExchange;

                    alias Result = ChangeElementType!(This, ElementType);
                    ()@trusted{
                        desired._control.add!(This.weakPtr);

                        Result tmp;
                        GetElementReferenceType!This source = desired._element;    //interface/class cast

                        tmp._set_element(cast(typeof(this._element))atomicExchange!order(
                            cast(Unqual!(This.ElementReferenceType)*)&this._element,
                            cast(Unqual!(This.ElementReferenceType))source
                        ));
                    }();
                }
                else{
                    this.lockIntrusivePtr!(
                        (ref scope self, ref scope Rhs x) => self.opAssign!order(x)
                    )(desired);
                }
            }
            else{
                this._release();
                ()@trusted{
                    auto control = desired._control;
                    this._set_element(desired._element);

                    if(control !is null)
                        control.add!weakPtr;

                }();
            }
        }

        ///ditto
        public void opAssign(MemoryOrder order = MemoryOrder.seq, Rhs, this This)(scope Rhs desired)scope
        if(true
            && isIntrusivePtr!Rhs
            && isMutable!This
            && isMovable!(Rhs, This)
            && !needLock!(Rhs, This)
            && !is(Rhs == shared)
        ){
            static assert(isValidIntrusivePtr!This, "`This` is invalid `IntrusivePtr`");
            static assert(isValidIntrusivePtr!Rhs, "`Rhs` is invalid `IntrusivePtr`");

            static if(is(This == shared)){
                static if(isLockFree){
                    import core.atomic : atomicExchange;

                    alias Result = ChangeElementType!(This, ElementType);
                    ()@trusted{
                        Result tmp;
                        GetElementReferenceType!This source = desired._element;    //interface/class cast

                        tmp._set_element(cast(typeof(this._element))atomicExchange!order(
                            cast(Unqual!(This.ElementReferenceType)*)&this._element,
                            cast(Unqual!(This.ElementReferenceType))source
                        ));

                        desired._const_reset();
                    }();
                }
                else{
                    return this.lockIntrusivePtr!(
                        (ref scope self, Rhs x) => self.opAssign!order(x.move)
                    )(desired.move);
                }
            }
            else{

                this._release();

                ()@trusted{
                    this._set_element(desired._element);
                    desired._const_reset();
                }();

            }
        }



        /**
            Constructs an object of type `ElementType` and wraps it in a `IntrusivePtr` using args as the parameter list for the constructor of `ElementType`.

            The object is constructed as if by the expression `emplace!ElementType(_payload, forward!args)`, where _payload is an internal pointer to storage suitable to hold an object of type `ElementType`.
            The storage is typically larger than `ElementType.sizeof` in order to use one allocation for both the control block and the `ElementType` object.

            Examples:
                --------------------
                static struct Foo{
                    ControlBlock!(int, int) c;
                    int i;

                    this(int i)pure nothrow @safe @nogc{
                        this.i = i;
                    }
                }

                {
                    IntrusivePtr!Foo a = IntrusivePtr!Foo.make();
                    assert(a.get.i == 0);

                    IntrusivePtr!(const Foo) b = IntrusivePtr!Foo.make(2);
                    assert(b.get.i == 2);
                }

                {
                    static struct Struct{
                        ControlBlock!int c;
                        int i = 7;

                        this(int i)pure nothrow @safe @nogc{
                            this.i = i;
                        }
                    }

                    IntrusivePtr!Struct s1 = IntrusivePtr!Struct.make();
                    assert(s1.get.i == 7);

                    IntrusivePtr!Struct s2 = IntrusivePtr!Struct.make(123);
                    assert(s2.get.i == 123);
                }
                --------------------
        */
        static if(!weakPtr)
        public static IntrusivePtr make
            (AllocatorType = DefaultAllocator, bool supportGC = platformSupportGC, Args...)
            (auto ref Args args)
        if(stateSize!AllocatorType == 0 && !isDynamicArray!ElementType){
            static assert(!weakPtr);

            auto m = MakeIntrusive!(AllocatorType, supportGC).make(forward!(args));

            return (m is null)
                ? IntrusivePtr.init
                : IntrusivePtr(m.get);
        }



        /**
            Constructs an object of type `ElementType` and wraps it in a `IntrusivePtr` using args as the parameter list for the constructor of `ElementType`.

            The object is constructed as if by the expression `emplace!ElementType(_payload, forward!args)`, where _payload is an internal pointer to storage suitable to hold an object of type `ElementType`.
            The storage is typically larger than `ElementType.sizeof` in order to use one allocation for both the control block and the `ElementType` object.

            Examples:
                --------------------
                static struct Foo{
                    ControlBlock!(int, int) c;
                    int i;

                    this(int i)pure nothrow @safe @nogc{
                        this.i = i;
                    }
                }

                {
                    import std.experimental.allocator : allocatorObject;

                    auto a = allocatorObject(Mallocator.instance);
                    {
                        IntrusivePtr!Foo x = IntrusivePtr!Foo.alloc(a);
                        assert(x.get.i == 0);

                        IntrusivePtr!(const Foo) y = IntrusivePtr!Foo.alloc(a, 2);
                        assert(y.get.i == 2);
                    }

                    {
                        static struct Struct{
                            ControlBlock!(int) c;
                            int i = 7;

                            this(int i)pure nothrow @safe @nogc{
                                this.i = i;
                            }
                        }

                        IntrusivePtr!Struct s1 = IntrusivePtr!Struct.alloc(a);
                        assert(s1.get.i == 7);

                        IntrusivePtr!Struct s2 = IntrusivePtr!Struct.alloc(a, 123);
                        assert(s2.get.i == 123);
                    }

                }
                --------------------
        */
        static if(!weakPtr)
        public static IntrusivePtr alloc
            (AllocatorType, bool supportGC = platformSupportGC, Args...)
            (AllocatorType a, auto ref Args args)
        if(stateSize!AllocatorType >= 0 && !isDynamicArray!ElementType){
            static assert(!weakPtr);

            auto m = MakeIntrusive!(AllocatorType, supportGC).make(forward!(a, args));

            return (m is null)
                ? IntrusivePtr.init
                : IntrusivePtr(m.get);
        }



        /**
            Returns the number of different `IntrusivePtr` instances

            Returns the number of different `IntrusivePtr` instances (`this` included) managing the current object or `0` if there is no managed object.

            Examples:
                --------------------
                static struct Foo{
                    ControlBlock!(int, int) c;
                    int i;

                    this(int i)pure nothrow @safe @nogc{
                        this.i = i;
                    }
                }


                IntrusivePtr!Foo x = null;

                assert(x.useCount == 0);

                x = IntrusivePtr!Foo.make(123);
                assert(x.useCount == 1);

                auto y = x;
                assert(x.useCount == 2);

                auto w1 = x.weak;    //weak ptr
                assert(x.useCount == 2);

                IntrusivePtr!Foo.WeakType w2 = x;   //weak ptr
                assert(x.useCount == 2);

                y = null;
                assert(x.useCount == 1);

                x = null;
                assert(x.useCount == 0);
                assert(w1.useCount == 0);
                --------------------
        */
        public @property ControlType.Shared useCount(this This)()const scope nothrow @safe @nogc{
            static assert(isValidIntrusivePtr!This, "`This` is invalid `IntrusivePtr`");

            static if(is(This == shared)){
                static assert(is(ControlType == shared));

                return this.lockIntrusivePtr!(
                    (ref scope return self) => self.useCount()
                )();
            }
            else{
                return (this._element is null)
                    ? 0
                    : this._control.count!false + 1;
            }

        }


        /**
            Returns the number of different `IntrusivePtr.WeakType` instances

            Returns the number of different `IntrusivePtr.WeakType` instances (`this` included) managing the current object or `0` if there is no managed object.

            Examples:
                --------------------
                static struct Foo{
                    ControlBlock!(int, int) c;
                    int i;

                    this(int i)pure nothrow @safe @nogc{
                        this.i = i;
                    }
                }

                IntrusivePtr!Foo x = null;
                assert(x.useCount == 0);
                assert(x.weakCount == 0);

                x = IntrusivePtr!Foo.make(123);
                assert(x.useCount == 1);
                assert(x.weakCount == 0);

                auto w = x.weak();
                assert(x.useCount == 1);
                assert(x.weakCount == 1);
                --------------------
        */
        public @property ControlType.Weak weakCount(this This)()const scope nothrow @safe @nogc{
            static assert(isValidIntrusivePtr!This, "`This` is invalid `IntrusivePtr`");

            static if(is(This == shared)){
                static assert(is(ControlType == shared));

                return this.lockSharedPtr!(
                    (ref scope return self) => self.weakCount()
                )();
            }
            else{
                return (this._element is null)
                    ? 0
                    : this._control.count!true;
            }

        }



        /**
            Swap `this` with `rhs`

            Examples:
                --------------------
                static struct Foo{
                    ControlBlock!(int, int) c;
                    int i;

                    this(int i)pure nothrow @safe @nogc{
                        this.i = i;
                    }
                }

                {
                    IntrusivePtr!Foo a = IntrusivePtr!Foo.make(1);
                    IntrusivePtr!Foo b = IntrusivePtr!Foo.make(2);
                    a.proxySwap(b);
                    assert(a != null);
                    assert(b != null);
                    assert(a.get.i == 2);
                    assert(b.get.i == 1);
                    import std.algorithm : swap;
                    swap(a, b);
                    assert(a.get.i == 1);
                    assert(b.get.i == 2);
                    assert(a.useCount == 1);
                    assert(b.useCount == 1);
                }
                --------------------
        */
        public void proxySwap(ref scope typeof(this) rhs)scope @trusted pure nothrow @nogc{
            auto element = this._element;
            this._set_element(rhs._element);
            rhs._set_element(element);
        }



        /**
            Returns the non `shared` `IntrusivePtr` pointer pointed-to by `shared` `this`.

            Examples:
                --------------------
                static struct Foo{
                    ControlBlock!(int, int) c;
                    int i;

                    this(int i)pure nothrow @safe @nogc{
                        this.i = i;
                    }
                }

                shared IntrusivePtr!(shared Foo) x = IntrusivePtr!(shared Foo).make(123);

                {
                    IntrusivePtr!(shared Foo) y = x.load();
                    assert(y.useCount == 2);

                    assert(y.get.i == 123);
                }
                --------------------
        */
        public ChangeElementType!(This, CopyTypeQualifiers!(This, ElementType))
        load(MemoryOrder order = MemoryOrder.seq, this This)()scope return{  //TODO remove return
            static assert(isCopyable!(Unshared!This, typeof(return)));
            static assert(isValidIntrusivePtr!This, "`This` is invalid `IntrusivePtr`");

            static if(is(This == shared)){
                static assert(is(ControlType == shared));

                return this.lockIntrusivePtr!(
                    (ref scope return self) => self.load!order()
                )();
            }
            else{
                return typeof(return)(this);
            }
        }



        /**
            Stores the non `shared` `IntrusivePtr` parameter `ptr` to `this`.

            If `this` is shared then operation is atomic or guarded by mutex.

            Template parameter `order` has type `core.atomic.MemoryOrder`.

            Examples:
                --------------------
                static struct Foo{
                    ControlBlock!(int, int) c;
                    int i;

                    this(int i)pure nothrow @safe @nogc{
                        this.i = i;
                    }
                }

                //null store:
                {
                    shared x = IntrusivePtr!(shared Foo).make(123);
                    assert(x.load.get.i == 123);

                    x.store(null);
                    assert(x.useCount == 0);
                    assert(x.load == null);
                }

                //rvalue store:
                {
                    shared x = IntrusivePtr!(shared Foo).make(123);
                    assert(x.load.get.i == 123);

                    x.store(IntrusivePtr!(shared Foo).make(42));
                    assert(x.load.get.i == 42);
                }

                //lvalue store:
                {
                    shared x = IntrusivePtr!(shared Foo).make(123);
                    auto y = IntrusivePtr!(shared Foo).make(42);

                    assert(x.load.get.i == 123);
                    assert(y.load.get.i == 42);

                    x.store(y);
                    assert(x.load.get.i == 42);
                    assert(x.useCount == 2);
                }
                --------------------
        */
        public void store(MemoryOrder order = MemoryOrder.seq, this This)(typeof(null) nil)scope
        if(isMutable!This){
            static assert(isValidIntrusivePtr!This, "`This` is invalid `IntrusivePtr`");

            this.opAssign!order(null);
        }

        /// ditto
        public void store(MemoryOrder order = MemoryOrder.seq, Rhs, this This)(ref scope Rhs desired)scope
        if(true
            && isIntrusivePtr!Rhs
            && !is(Rhs == shared)
            && !needLock!(Rhs, This)
            && (isCopyable!(Rhs, This) && isMutable!This)
        ){
            static assert(isValidIntrusivePtr!This, "`This` is invalid `IntrusivePtr`");
            static assert(isValidIntrusivePtr!Rhs, "`Rhs` is invalid `IntrusivePtr`");

            this.opAssign!order(forward!desired);
        }

        /// ditto
        public void store(MemoryOrder order = MemoryOrder.seq, Rhs, this This)(scope Rhs desired)scope
        if(true
            && isIntrusivePtr!Rhs
            && !is(Rhs == shared)
            && !needLock!(Rhs, This)
            && (isMovable!(Rhs, This) && isMutable!This)
        ){
            static assert(isValidIntrusivePtr!This, "`This` is invalid `IntrusivePtr`");
            static assert(isValidIntrusivePtr!Rhs, "`Rhs` is invalid `IntrusivePtr`");

            this.opAssign!order(forward!desired);
        }



        /**
            Stores the non `shared` `IntrusivePtr` pointer ptr in the `shared(IntrusivePtr)` pointed to by `this` and returns the value formerly pointed-to by this, atomically or with mutex.

            Examples:
                --------------------
                static struct Foo{
                    ControlBlock!(int, int) c;
                    int i;

                    this(int i)pure nothrow @safe @nogc{
                        this.i = i;
                    }
                }

                //lvalue exchange
                {
                    shared x = IntrusivePtr!(shared Foo).make(123);
                    auto y = IntrusivePtr!(shared Foo).make(42);

                    auto z = x.exchange(y);

                    assert(x.load.get.i == 42);
                    assert(y.get.i == 42);
                    assert(z.get.i == 123);
                }

                //rvalue exchange
                {
                    shared x = IntrusivePtr!(shared Foo).make(123);
                    auto y = IntrusivePtr!(shared Foo).make(42);

                    auto z = x.exchange(y.move);

                    assert(x.load.get.i == 42);
                    assert(y == null);
                    assert(z.get.i == 123);
                }

                //null exchange (same as move)
                {
                    shared x = IntrusivePtr!(shared Foo).make(123);

                    auto z = x.exchange(null);

                    assert(x.load == null);
                    assert(z.get.i == 123);
                }

                //swap:
                {
                    shared x = IntrusivePtr!(shared Foo).make(123);
                    auto y = IntrusivePtr!(shared Foo).make(42);

                    //opAssign is same as store
                    y = x.exchange(y.move);

                    assert(x.load.get.i == 42);
                    assert(y.get.i == 123);
                }
                --------------------
        */
        public IntrusivePtr exchange(MemoryOrder order = MemoryOrder.seq, this This)(typeof(null))scope
        if(isMutable!This){
            static assert(isValidIntrusivePtr!This, "`This` is invalid `IntrusivePtr`");

            static if(is(This == shared)){
                static if(isLockFree){
                    import core.atomic : atomicExchange;

                    return()@trusted{
                        alias Result = ChangeElementType!(This, ElementType);
                        Result result;
                        result._set_element(cast(typeof(this._element))atomicExchange!order(
                            cast(Unqual!(This.ElementReferenceType)*)&this._element,
                            null
                        ));

                        return result.move;
                    }();
                }
                else{
                    return this.lockIntrusivePtr!(
                        (ref scope self) => self.exchange!order(null)
                    )();
                }
            }
            else{
                return this.move;
            }
        }

        /// ditto
        public IntrusivePtr exchange(MemoryOrder order = MemoryOrder.seq, Rhs, this This)(scope Rhs ptr)scope
        if(true
            && isIntrusivePtr!Rhs 
            && !is(Rhs == shared) 
            && isMovable!(Rhs, This)
            && isMutable!This
        ){
            static assert(isValidIntrusivePtr!This, "`This` is invalid `IntrusivePtr`");
            static assert(isValidIntrusivePtr!Rhs, "`Rhs` is invalid `IntrusivePtr`");

            static if(is(This == shared)){

                static if(isLockFree){
                    import core.atomic : atomicExchange;

                    return()@trusted{
                        alias Result = ChangeElementType!(This, ElementType);
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
                    return this.lockIntrusivePtr!(
                        (ref scope self, Rhs x) => self.exchange!order(x.move)
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
            Compares the `IntrusivePtr` pointers pointed-to by `this` and `expected`.

            If they are equivalent (store the same pointer value, and either share ownership of the same object or are both empty), assigns `desired` into `this` using the memory ordering constraints specified by `success` and returns `true`.
            If they are not equivalent, assigns `this` into `expected` using the memory ordering constraints specified by `failure` and returns `false`.

            More info in c++ std::atomic<std::shared_ptr>.


            Examples:
                --------------------
                static class Foo{
                    long i;
                    MutableControlBlock!(int, int) c;

                    this(long i)pure nothrow @safe @nogc{
                        this.i = i;
                    }

                    bool opEquals(this This)(long i)const @trusted{
                        import std.traits : Unqual;
                        auto self = cast(Unqual!This)this;
                        return (self.i == i);
                    }
                }

                alias Type = const Foo;

                static foreach(enum bool weak; [true, false]){
                    //fail
                    {
                        IntrusivePtr!Type a = IntrusivePtr!Type.make(123);
                        IntrusivePtr!Type b = IntrusivePtr!Type.make(42);
                        IntrusivePtr!Type c = IntrusivePtr!Type.make(666);

                        static if(weak)a.compareExchangeWeak(b, c);
                        else a.compareExchangeStrong(b, c);

                        assert(*a == 123);
                        assert(*b == 123);
                        assert(*c == 666);

                    }

                    //success
                    {
                        IntrusivePtr!Type a = IntrusivePtr!Type.make(123);
                        IntrusivePtr!Type b = a;
                        IntrusivePtr!Type c = IntrusivePtr!Type.make(666);

                        static if(weak)a.compareExchangeWeak(b, c);
                        else a.compareExchangeStrong(b, c);

                        assert(*a == 666);
                        assert(*b == 123);
                        assert(*c == 666);
                    }

                    //shared fail
                    {
                        shared IntrusivePtr!(shared Type) a = IntrusivePtr!(shared Type).make(123);
                        IntrusivePtr!(shared Type) b = IntrusivePtr!(shared Type).make(42);
                        IntrusivePtr!(shared Type) c = IntrusivePtr!(shared Type).make(666);

                        static if(weak)a.compareExchangeWeak(b, c);
                        else a.compareExchangeStrong(b, c);

                        auto tmp = a.exchange(null);
                        assert(*tmp == 123);
                        assert(*b == 123);
                        assert(*c == 666);
                    }

                    //shared success
                    {
                        IntrusivePtr!(shared Type) b = IntrusivePtr!(shared Type).make(123);
                        shared IntrusivePtr!(shared Type) a = b;
                        IntrusivePtr!(shared Type) c = IntrusivePtr!(shared Type).make(666);

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
            && isIntrusivePtr!E && !is(E == shared)
            && isIntrusivePtr!D && !is(D == shared)
            && (isMovable!(D, This) && isMutable!This)
            && (isMovable!(This, E) && isMutable!E)
            && (This.weakPtr == D.weakPtr)
            && (This.weakPtr == E.weakPtr)
        ){
            static assert(isValidIntrusivePtr!This, "`This` is invalid `IntrusivePtr`");
            static assert(isValidIntrusivePtr!E, "`E expected` is invalid `IntrusivePtr`");
            static assert(isValidIntrusivePtr!D, "`D desired` is invalid `IntrusivePtr`");

            return this.compareExchangeImpl!(false, success, failure)(expected, desired.move);
        }



        /**
            Same as `compareExchangeStrong` but may fail spuriously.

            More info in c++ `std::atomic<std::shared_ptr>`.
        */
        public bool compareExchangeWeak
            (MemoryOrder success = MemoryOrder.seq, MemoryOrder failure = success, E, D, this This)
            (ref scope E expected, scope D desired)scope
        if(true
            && isIntrusivePtr!E && !is(E == shared)
            && isIntrusivePtr!D && !is(D == shared)
            && (isMovable!(D, This) && isMutable!This)
            && (isMovable!(This, E) && isMutable!E)
            && (This.weakPtr == D.weakPtr)
            && (This.weakPtr == E.weakPtr)
        ){
            static assert(isValidIntrusivePtr!This, "`This` is invalid `IntrusivePtr`");
            static assert(isValidIntrusivePtr!E, "`E expected` is invalid `IntrusivePtr`");
            static assert(isValidIntrusivePtr!D, "`D desired` is invalid `IntrusivePtr`");

            return this.compareExchangeImpl!(true, success, failure)(expected, desired.move);
        }


        private bool compareExchangeImpl
            (bool weak, MemoryOrder success, MemoryOrder failure, E, D, this This)
            (ref scope E expected, scope D desired)scope //@trusted pure @nogc
        if(true
            && isIntrusivePtr!E && !is(E == shared)
            && isIntrusivePtr!D && !is(D == shared)
            && (isMovable!(D, This) && isMutable!This)
            && (isMovable!(This, E) && isMutable!E)
            && (This.weakPtr == D.weakPtr)
            && (This.weakPtr == E.weakPtr)
        ){
            static assert(isValidIntrusivePtr!This, "`This` is invalid `IntrusivePtr`");
            static assert(isValidIntrusivePtr!E, "`E expected` is invalid `IntrusivePtr`");
            static assert(isValidIntrusivePtr!D, "`D desired` is invalid `IntrusivePtr`");

            static if(is(This == shared) && isLockFree){
                import core.atomic : cas, casWeak;
                static if(weak)
                    alias casImpl = casWeak;
                else
                    alias casImpl = cas;


                return ()@trusted{
                    GetElementReferenceType!This source_desired = desired._element;     //interface/class cast
                    GetElementReferenceType!This source_expected = expected._element;   //interface/class cast

                    const bool store_occurred = casImpl!(success, failure)(
                        cast(Unqual!(This.ElementReferenceType)*)&this._element,
                        cast(Unqual!(This.ElementReferenceType)*)&source_expected,
                        cast(Unqual!(This.ElementReferenceType))source_desired
                    );

                    if(store_occurred){
                        desired._const_reset();
                        if(expected._element !is null)
                            expected._control.release!(This.weakPtr);
                    }
                    else{
                        expected = null;
                        expected._set_element(source_expected);
                    }

                    return store_occurred;
                }();
            }
            else{
                return this.compareExchange!(success, failure)(expected, desired.move);
            }
        }


        /*
            implementation of `compareExchangeWeak` and `compareExchangeStrong`
        */
        private bool compareExchange
            (MemoryOrder success = MemoryOrder.seq, MemoryOrder failure = success, E, D, this This)
            (ref scope E expected, scope D desired)scope //@trusted pure @nogc
        if(true
            && isIntrusivePtr!E && !is(E == shared)
            && isIntrusivePtr!D && !is(D == shared)
            && (isMovable!(D, This) && isMutable!This)
            && (isMovable!(This, E) && isMutable!E)
            && (This.weakPtr == D.weakPtr)
            && (This.weakPtr == E.weakPtr)
        ){
            static assert(isValidIntrusivePtr!This, "`This` is invalid `IntrusivePtr`");
            static assert(isValidIntrusivePtr!E, "`E expected` is invalid `IntrusivePtr`");
            static assert(isValidIntrusivePtr!D, "`D desired` is invalid `IntrusivePtr`");

            static if(is(This == shared)){
                import core.atomic : cas;


                static assert(!isLockFree);
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
            Creates a new non weak `IntrusivePtr` that shares ownership of the managed object (must be `IntrusivePtr.WeakType`).

            If there is no managed object, i.e. this is empty or this is `expired`, then the returned `IntrusivePtr` is empty.
            Method exists only if `IntrusivePtr` is `weakPtr`

            Examples:
                --------------------
                static struct Foo{
                    ControlBlock!(int, int) c;
                    int i;

                    this(int i)pure nothrow @safe @nogc{
                        this.i = i;
                    }
                }

                {
                    IntrusivePtr!Foo x = IntrusivePtr!Foo.make(123);

                    auto w = x.weak;    //weak ptr

                    IntrusivePtr!Foo y = w.lock;

                    assert(x == y);
                    assert(x.useCount == 2);
                    assert(y.get.i == 123);
                }

                {
                    IntrusivePtr!Foo x = IntrusivePtr!Foo.make(123);

                    auto w = x.weak;    //weak ptr

                    assert(w.expired == false);

                    x = IntrusivePtr!Foo.make(321);

                    assert(w.expired == true);

                    IntrusivePtr!Foo y = w.lock;

                    assert(y == null);
                }

                {
                    shared IntrusivePtr!(shared Foo) x = IntrusivePtr!(shared Foo).make(123);

                    shared IntrusivePtr!(shared Foo).WeakType w = x.load.weak;    //weak ptr

                    assert(w.expired == false);

                    x = IntrusivePtr!(shared Foo).make(321);

                    assert(w.expired == true);

                    IntrusivePtr!(shared Foo) y = w.load.lock;

                    assert(y == null);
                }
                --------------------
        */
        static if(weakPtr)
        public CopyConstness!(This, SharedType) lock(this This)()scope @safe
        if(!is(This == shared)){
            static assert(isCopyable!(This, typeof(return)));
            static assert(isValidIntrusivePtr!This, "`This` is invalid `IntrusivePtr`");

            static assert(needLock!(This, typeof(return)));

            return typeof(return)(this);
        }



        /**
            Equivalent to `useCount() == 0` (must be `IntrusivePtr.WeakType`).

            Method exists only if `IntrusivePtr` is `weakPtr`

            Examples:
                --------------------
                static struct Foo{
                    ControlBlock!(int, int) c;
                    int i;

                    this(int i)pure nothrow @safe @nogc{
                        this.i = i;
                    }
                }

                {
                    IntrusivePtr!Foo x = IntrusivePtr!Foo.make(123);

                    auto wx = x.weak;   //weak pointer

                    assert(wx.expired == false);

                    x = null;

                    assert(wx.expired == true);
                }
                --------------------
        */
        static if(weakPtr)
        public @property bool expired(this This)()scope const{
            static assert(isValidIntrusivePtr!This, "`This` is invalid `IntrusivePtr`");

            return (this.useCount == 0);
        }


        static if(!weakPtr){
            /**
                Operator *, same as method 'get'.

                Examples:
                    --------------------
                    static struct Foo{
                        ControlBlock!(int, int) c;
                        int i;
                        alias i this;

                        this(int i)pure nothrow @safe @nogc{
                            this.i = i;
                        }
                    }

                    IntrusivePtr!Foo x = IntrusivePtr!Foo.make(123);
                    assert(*x == 123);
                    ((*x).i = 321);
                    assert(*x == 321);
                    const y = x;
                    assert(*y == 321);
                    assert(*x == 321);
                    static assert(is(typeof(*y) == const Foo));
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
                    static struct Foo{
                        ControlBlock!(int, int) c;
                        int i;

                        this(int i)pure nothrow @safe @nogc{
                            this.i = i;
                        }
                    }

                    IntrusivePtr!Foo x = IntrusivePtr!Foo.make(123);
                    assert(x.get.i == 123);
                    x.get.i = 321;
                    assert(x.get.i == 321);
                    const y = x;
                    assert(y.get.i == 321);
                    assert(x.get.i == 321);
                    static assert(is(typeof(y.get) == const Foo));
                    --------------------
            */
            static if(is(ElementType == class))
                public @property inout(ElementType) get()inout scope return pure nothrow @system @nogc{
                    return this._element;
                }
            else static if(is(ElementType == struct))
                /// ditto
                public @property ref inout(ElementType) get()inout scope return pure nothrow @system @nogc{
                    return *cast(inout ElementType*)this._element;
                }
            else static assert(0, "no impl");



            /**
                Get pointer to managed object of `ElementType` or reference if `ElementType` is reference type (class or interface) or dynamic array

                Examples:
                    --------------------
                    static struct Foo{
                        ControlBlock!(int, int) c;
                        int i;

                        this(int i)pure nothrow @safe @nogc{
                            this.i = i;
                        }
                    }

                    IntrusivePtr!Foo x = IntrusivePtr!Foo.make(123);
                    assert(x.element.i == 123);
                    x.get.i = 321;
                    assert(x.element.i == 321);
                    const y = x;
                    assert(y.element.i == 321);
                    assert(x.element.i == 321);
                    static assert(is(typeof(y.element) == const(Foo)*));
                    --------------------
            */
            public @property ElementReferenceTypeImpl!(inout ElementType)
            element()inout scope return pure nothrow @system @nogc{
                return this._element;
            }

        }


        /**
            Returns weak pointer (must have weak counter).

            Examples:
                --------------------
                static struct Foo{
                    ControlBlock!(int, int) c;
                    int i;

                    this(int i)pure nothrow @safe @nogc{
                        this.i = i;
                    }
                }

                IntrusivePtr!Foo x = IntrusivePtr!Foo.make(123);
                assert(x.useCount == 1);
                auto wx = x.weak;   //weak pointer
                assert(wx.expired == false);
                assert(wx.lock.get.i == 123);
                assert(wx.useCount == 1);
                x = null;
                assert(wx.expired == true);
                assert(wx.useCount == 0);
                --------------------
        */
        static if(hasWeakCounter)
        public CopyTypeQualifiers!(This, WeakType) weak(this This)()scope @safe
        if(!is(This == shared)){
            static assert(isCopyable!(This, typeof(return)));
            static assert(isValidIntrusivePtr!This, "`This` is invalid `IntrusivePtr`");

            return typeof(return)(this);
        }



        /**
            Checks if `this` stores a non-null pointer, i.e. whether `this != null`.

            Examples:
                --------------------
                static struct Foo{
                    ControlBlock!(int, int) c;
                    int i;

                    this(int i)pure nothrow @safe @nogc{
                        this.i = i;
                    }
                }

                IntrusivePtr!Foo x = IntrusivePtr!Foo.make(123);
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
            Cast `this` to different type `To` when `isIntrusivePtr!To`.

            Examples:
                --------------------
                static struct Foo{
                    ControlBlock!(int, int) c;
                    int i;
                    alias i this;

                    this(int i)pure nothrow @safe @nogc{
                        this.i = i;
                    }
                }

                import std.conv;

                IntrusivePtr!Foo x = IntrusivePtr!Foo.make(123);
                assert(x.useCount == 1
                );
                auto y = cast(IntrusivePtr!(const Foo))x;
                //debug assert(x.useCount == 2, x.useCount.to!string);
                assert(x.useCount == 2);


                auto z = cast(const IntrusivePtr!Foo)x;
                assert(x.useCount == 3);

                auto u = cast(const IntrusivePtr!(const Foo))x;
                assert(x.useCount == 4);
                --------------------
        */
        public To opCast(To, this This)()scope
        if(isIntrusivePtr!To && !is(This == shared)){
            ///copy this -> return
            static assert(isValidIntrusivePtr!This, "`This` is invalid `IntrusivePtr`");

            return To(this);
        }


        /**
            Operator == and != .
            Compare pointers.

            Examples:
                --------------------
                static struct Foo{
                    ControlBlock!(int, int) c;
                    int i;

                    this(int i)pure nothrow @safe @nogc{
                        this.i = i;
                    }
                }

                {
                    IntrusivePtr!Foo x = IntrusivePtr!Foo.make(0);
                    assert(x != null);
                    x = null;
                    assert(x == null);
                }

                {
                    IntrusivePtr!Foo x = IntrusivePtr!Foo.make(123);
                    IntrusivePtr!Foo y = IntrusivePtr!Foo.make(123);
                    assert(x == x);
                    assert(y == y);
                    assert(x != y);
                }

                {
                    IntrusivePtr!Foo x;
                    IntrusivePtr!(const Foo) y;
                    assert(x == x);
                    assert(y == y);
                    assert(x == y);
                }

                {
                    IntrusivePtr!Foo x = IntrusivePtr!Foo.make(123);
                    IntrusivePtr!Foo y = IntrusivePtr!Foo.make(123);
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
        if(isIntrusivePtr!Rhs && !is(Rhs == shared)){
            static assert(isValidIntrusivePtr!Rhs, "`Rhs` is invalid `IntrusivePtr`");

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
            Operators <, <=, >, >= for `IntrusivePtr`.

            Compare address of payload.

            Examples:
                --------------------
                static struct Foo{
                    ControlBlock!(int, int) c;
                    int i;

                    this(int i)pure nothrow @safe @nogc{
                        this.i = i;
                    }
                }

                {
                    const a = IntrusivePtr!Foo.make(42);
                    const b = IntrusivePtr!Foo.make(123);
                    const n = IntrusivePtr!Foo.init;

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
                    const a = IntrusivePtr!Foo.make(42);
                    const b = IntrusivePtr!Foo.make(123);

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
        if(isIntrusivePtr!Rhs && !is(Rhs == shared)){
            static assert(isValidIntrusivePtr!Rhs, "`Rhs` is invalid `IntrusivePtr`");

            return this.opCmp(rhs._element);
        }



        /**
            Generate hash

            Return:
                Address of payload as `size_t`

            Examples:
                --------------------
                static struct Foo{
                    ControlBlock!(int, int) c;
                    int i;

                    this(int i)pure nothrow @safe @nogc{
                        this.i = i;
                    }
                }

                {
                    IntrusivePtr!Foo x = IntrusivePtr!Foo.make(123);
                    IntrusivePtr!Foo y = IntrusivePtr!Foo.make(123);
                    assert(x.toHash == x.toHash);
                    assert(y.toHash == y.toHash);
                    assert(x.toHash != y.toHash);
                    IntrusivePtr!(const Foo) z = x;
                    assert(x.toHash == z.toHash);
                }
                {
                    IntrusivePtr!Foo x;
                    IntrusivePtr!(const Foo) y;
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
            Move `IntrusivePtr`
        */
        public IntrusivePtr move()()scope{
            import core.lifetime : move_impl = move;

            return move_impl(this);
        }

        private ElementReferenceType _element;


        package auto _control(this This)()scope return pure nothrow @trusted @nogc
        in(this._element !is null){
            static assert(isValidIntrusivePtr!This, "`This` is invalid `IntrusivePtr`");

            static if(is(ElementType == class))
                auto control = intrusivControlBlock(this._element);
            else static if(is(ElementType == struct))
                auto control = intrusivControlBlock(*this._element);
            else static assert(0, "no impl");
                
            alias ControlPtr = typeof(control);

            static if(mutableControl){
                alias MutableControl = CopyTypeQualifiers!(
                    Unconst!ControlPtr, 
                    Unconst!(PointerTarget!ControlPtr)
                );
                return cast(MutableControl*)control;
            }
            else
                return control;
        }

        private void _set_element(ElementReferenceType e)pure nothrow @system @nogc{
            static if(isMutable!ElementReferenceType)
                this._element = e;
            else
                (*cast(Unqual!ElementReferenceType*)&this._element) = cast(Unqual!ElementReferenceType)e;
        }

        private void _const_set_element(ElementReferenceType e)const pure nothrow @system @nogc{
            auto self = cast(Unqual!(typeof(this))*)&this;

            static if(isMutable!ElementReferenceType)
                self._element = e;
            else
                (*cast(Unqual!ElementReferenceType*)&self._element) = cast(Unqual!ElementReferenceType)e;
        }

        private void _release()scope /*pure nothrow @safe @nogc*/ {
            if(false){
                DestructorType dt;
                dt(null);
            }

            import std.traits : hasIndirections;
            import core.memory : GC;

            if(this._element is null)
                return;

            auto control = ()@trusted{
                static if(is(ControlType == immutable))
                    return cast(shared(Unconst!ControlType)*)this._control;
                else
                    return cast(Unconst!ControlType*)this._control;
            }();
            control.release!weakPtr;
        }

        private void _reset()scope pure nothrow @system @nogc{
            this._set_element(null);
        }

        package void _const_reset()scope const pure nothrow @system @nogc{
            auto self = cast(Unqual!(typeof(this))*)&this;

            self._reset();
        }
    }

}


///
pure nothrow @nogc unittest{

    static class Foo{
        MutableControlBlock!(int, int) c;   //or MutableControlBlock!(ControlBlock!(int, int)) c;
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
        IntrusivePtr!(const Foo) foo =  IntrusivePtr!Foo.make(42);
        assert(foo.get.i == 42);
        assert(foo.useCount == 1);

        const IntrusivePtr!Foo foo2 = foo;
        assert(foo2.get.i == 42);
        assert(foo.useCount == 2);

    }

    //polymorphic classes:
    {
        IntrusivePtr!Foo foo = IntrusivePtr!Bar.make(42, 3.14);
        assert(foo != null);
        assert(foo.useCount == 1);
        assert(foo.get.i == 42);

        //dynamic cast:
        {
            IntrusivePtr!Bar bar = dynCast!Bar(foo);
            assert(foo.useCount == 2);

            assert(bar.get.i == 42);
            assert(bar.get.d == 3.14);
        }

    }

    //weak references:
    {
        auto x = IntrusivePtr!Foo.make(314);
        assert(x.useCount == 1);
        assert(x.weakCount == 0);

        auto w = x.weak();  //weak pointer
        assert(x.useCount == 1);
        assert(x.weakCount == 1);
        assert(w.lock.get.i == 314);

        IntrusivePtr!Foo.WeakType w2 = x;
        assert(x.useCount == 1);
        assert(x.weakCount == 2);

        assert(w2.expired == false);
        x = null;
        assert(w2.expired == true);
    }
}

///
pure nothrow @safe @nogc unittest{
    //make IntrusivePtr object
    static struct Foo{
        ControlBlock!(int, int) c;
        int i;

        this(int i)pure nothrow @safe @nogc{
            this.i = i;
        }
    }

    {
        auto foo = IntrusivePtr!Foo.make(42);
        auto foo2 = IntrusivePtr!Foo.make!Mallocator(42);  //explicit stateless allocator
    }
}

///
nothrow unittest{

    static struct Foo{
        ControlBlock!(int, int) c;
        int i;

        this(int i)pure nothrow @safe @nogc{
            this.i = i;
        }
    }

    //alloc IntrusivePtr object
    import std.experimental.allocator : make, dispose, allocatorObject;

    auto allocator = allocatorObject(Mallocator.instance);

    {
        auto x = IntrusivePtr!Foo.alloc(allocator, 42);
    }

}



/**
    Dynamic cast for shared pointers if `ElementType` is class with D linkage.

    Creates a new instance of `IntrusivePtr` whose stored pointer is obtained from `ptr`'s stored pointer using a dynaic cast expression.

    If `ptr` is null or dynamic cast fail then result `IntrusivePtr` is null.
    Otherwise, the new `IntrusivePtr` will share ownership with the initial value of `ptr`.
*/
public ChangeElementType!(Ptr, T) dynCast(T, Ptr)(ref scope Ptr ptr)
if(true
    && isIntrusive!T
    && isIntrusivePtr!Ptr && !is(Ptr == shared) && !Ptr.weakPtr
    && isReferenceType!T && __traits(getLinkage, T) == "D"
    && isReferenceType!(Ptr.ElementType) && __traits(getLinkage, Ptr.ElementType) == "D"
){
    static assert(isCopyable!(Ptr, ChangeElementType!(Ptr, Ptr.ElementType)));
    static assert(isValidIntrusivePtr!Ptr, "`Ptr` is invalid `IntrusivePtr`");

    if(auto element = dynCastElement!T(ptr._element)){
        ptr._control.add!false;
        return typeof(return)(element);
    }

    return typeof(return).init;
}

/// ditto
public ChangeElementType!(Ptr, T) dynCast(T, Ptr)(scope Ptr ptr)
if(true
    && isIntrusive!T
    && isIntrusivePtr!Ptr && !is(Ptr == shared) && !Ptr.weakPtr
    && isReferenceType!T && __traits(getLinkage, T) == "D"
    && isReferenceType!(Ptr.ElementType) && __traits(getLinkage, Ptr.ElementType) == "D"
){
    static assert(isMovable!(Ptr, ChangeElementType!(Ptr, Ptr.ElementType)));
    static assert(isValidIntrusivePtr!Ptr, "`Ptr` is invalid `IntrusivePtr`");

    return dynCastMove(ptr);
}

/// ditto
public ChangeElementType!(Ptr, T) dynCastMove(T, Ptr)(auto ref scope Ptr ptr)
if(true
    && isIntrusive!T
    && isIntrusivePtr!Ptr && !is(Ptr == shared) && !Ptr.weakPtr
    && isReferenceType!T && __traits(getLinkage, T) == "D"
    && isReferenceType!(Ptr.ElementType) && __traits(getLinkage, Ptr.ElementType) == "D"
){
    static assert(isMovable!(Ptr, ChangeElementType!(Ptr, Ptr.ElementType)));
    static assert(isValidIntrusivePtr!Ptr, "`Ptr` is invalid `IntrusivePtr`");

    if(auto element = dynCastElement!T(ptr._element)){
        ()@trusted{
            ptr._const_reset();
        }();
        return typeof(return)(element);
    }

    return typeof(return).init;
}


///
pure nothrow @safe @nogc unittest{
    static class Base{
        MutableControlBlock!(int, int) c;
    }
    static class Foo : Base{
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

    static class Zee : Base{
    }

    {
        IntrusivePtr!(const Foo) foo = IntrusivePtr!Bar.make(42, 3.14);
        //assert(foo.get.i == 42);

        auto bar = dynCast!Bar(foo);
        assert(bar != null);
        //assert(bar.get.d == 3.14);
        static assert(is(typeof(bar) == IntrusivePtr!(const Bar)));

        auto zee = dynCast!Zee(foo);
        assert(zee == null);
        static assert(is(typeof(zee) == IntrusivePtr!(const Zee)));
    }

    {
        IntrusivePtr!(const Foo) foo = IntrusivePtr!Bar.make(42, 3.14);
        //assert(foo.get.i == 42);

        auto bar = dynCastMove!Bar(foo);
        assert(bar != null);
        assert(foo == null);
        //assert(bar.get.d == 3.14);
        static assert(is(typeof(bar) == IntrusivePtr!(const Bar)));

        auto zee = dynCast!Zee(bar);
        assert(bar != null);
        assert(zee == null);
        static assert(is(typeof(zee) == IntrusivePtr!(const Zee)));
    }
}



/**
    Create `SharedPtr` from parameter `ptr` of type `IntrusivePtr`.

    `Ptr` must have `mutableControl == true`.
*/
auto sharedPtr(Ptr)(auto ref scope Ptr ptr)@trusted
if(isIntrusivePtr!Ptr && !is(Ptr == shared)){
    static assert(Ptr.mutableControl);

    import std.traits : CopyTypeQualifiers;
    import core.lifetime : forward;
    import autoptr.shared_ptr : SharedPtr;

    return SharedPtr!(
        CopyTypeQualifiers!(Ptr, Ptr.ElementType),
        Ptr.DestructorType,
        Ptr.ControlType,
        Ptr.weakPtr
    )(forward!ptr);
}


///
pure nothrow @safe @nogc unittest{
    static class Foo{
        MutableControlBlock!(int, int) c;
        int i;

        this(int i)pure nothrow @safe @nogc{
            this.i = i;
        }
    }

    auto x = IntrusivePtr!Foo.make(42);
    //assert(x.get.i == 42);
    assert(x.useCount == 1);

    auto s = sharedPtr(x);
    assert(x.useCount == 2);

    import autoptr.shared_ptr : isSharedPtr;
    static assert(isSharedPtr!(typeof(s)));

    auto s2 = sharedPtr(x.move);
    assert(s.useCount == 2);

    auto y = sharedPtr(IntrusivePtr!Foo.init);
    assert(y == null);
}



/**
    Return `shared IntrusivePtr` pointing to same managed object like parameter `ptr`.

    Type of parameter `ptr` must be `IntrusivePtr` with `shared(ControlType)` and `shared`/`immutable` `ElementType` .
*/
public shared(Ptr) share(Ptr)(auto ref scope Ptr ptr)
if(isIntrusivePtr!Ptr){
    static assert(isValidIntrusivePtr!Ptr, "`Ptr` is invalid `IntrusivePtr`");

    import core.lifetime : forward;
    static if(is(Ptr == shared)){
        return forward!ptr;
    }
    else{
        static assert(is(Ptr.ControlType == shared),
            "`IntrusivePtr` has not shared ref counter `ControlType`."
        );

        static assert(is(Ptr.ElementType == shared) || is(Ptr.ElementType == immutable),
            "`IntrusivePtr` has not shared/immutable `ElementType`."
        );

        static assert(isValidIntrusivePtr!(typeof(return)),
            "`shared(Ptr)` is invalid `IntrusivePtr`"
        );

        return typeof(return)(forward!ptr);
    }
}

///
nothrow @nogc unittest{
    static struct Foo{
        ControlBlock!(int, int) c;
        int i;

        this(int i)pure nothrow @safe @nogc{
            this.i = i;
        }
    }

    {
        auto x = IntrusivePtr!(shared Foo).make(123);
        assert(x.useCount == 1);

        shared s1 = share(x);
        assert(x.useCount == 2);


        shared s2 = share(x.move);
        assert(x == null);
        assert(s2.useCount == 2);
        assert(s2.load.get.i == 123);

    }

    {
        auto x = IntrusivePtr!(Foo).make(123);
        assert(x.useCount == 1);

        ///error `shared IntrusivePtr` need shared `ControlType` and shared `ElementType`.
        //shared s1 = share(x);

    }

}



//local traits:
private{

    template needLock(From, To)
    if(isIntrusivePtr!From && isIntrusivePtr!To){
        enum needLock = (From.weakPtr && !To.weakPtr);
    }

    template isMovable(From, To)
    if(isIntrusivePtr!From && isIntrusivePtr!To){
        import std.traits : Unqual, CopyTypeQualifiers;

        alias FromPtr = CopyTypeQualifiers!(From, From.ElementReferenceType);
        alias ToPtr = CopyTypeQualifiers!(To, To.ElementReferenceType);

        alias FromElm = CopyTypeQualifiers!(From, From.ElementType);
        alias ToElm = CopyTypeQualifiers!(To, To.ElementType);

        static if(is(Unqual!FromElm == Unqual!ToElm))
            enum bool aliasable = is(FromPtr : ToPtr);

        else static if(is(FromElm == class) && is(ToElm == class))
            enum bool aliasable = true
                && is(FromElm : ToElm);
                //&& isIntrusive!FromElm;

        else static if(is(FromElm == struct) && is(ToElm == struct))
            enum bool aliasable = false;

        else
            enum bool aliasable = false;
        

        alias FromControlType = IntrusivControlBlock!(
            CopyTypeQualifiers!(From, From.ElementType), //GetElementReferenceType!From,
            //From.mutableControl
        );

        alias ToControlType = IntrusivControlBlock!(
            CopyTypeQualifiers!(To, To.ElementType),    //GetElementReferenceType!To,
            //To.mutableControl
        );

        enum bool isMovable = true
            && aliasable
            //&& isOverlapable!(From.ElementType, To.ElementType) //&& is(Unqual!(From.ElementType) == Unqual!(To.ElementType))
            //&& is(FromPtr : ToPtr)
            && is(From.DestructorType : To.DestructorType)
            && is(FromControlType : ToControlType)
            && (From.mutableControl == To.mutableControl);
    }

    template isCopyable(From, To)
    if(isIntrusivePtr!From && isIntrusivePtr!To){
        import std.traits : isMutable, CopyTypeQualifiers;

        static if(isMovable!(From, To)){
            enum bool isCopyable = isMutable!(IntrusivControlBlock!(
                CopyTypeQualifiers!(From, From.ElementType)
            ));
        }
        else{
            enum bool isCopyable = false;
        }
    }

    template ChangeElementType(Ptr, T)
    if(isIntrusivePtr!Ptr){
        import std.traits : CopyTypeQualifiers;

        alias FromType = CopyTypeQualifiers!(Ptr, Ptr.ElementType);
        alias ResultType = CopyTypeQualifiers!(FromType, T);

        alias ResultPtr = IntrusivePtr!(
            ResultType,

            Ptr.DestructorType,
            Ptr.weakPtr
        );

        alias ChangeElementType = ResultPtr;
    }

    template GetElementReferenceType(Ptr)
    if(isIntrusivePtr!Ptr){
        import std.traits : CopyTypeQualifiers, isDynamicArray;
        import std.range : ElementEncodingType;

        alias ElementType = CopyTypeQualifiers!(Ptr, Ptr.ElementType);

        alias GetElementReferenceType = ElementReferenceTypeImpl!ElementType;
    }
}

//mutex:
private static auto lockIntrusivePtr
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

    //copy ctor
    pure nothrow @nogc unittest{


        static struct Foo{
            MutableControlBlock!(int, int) c;
            int i;

            this(int i)pure nothrow @safe @nogc{
                this.i = i;
            }
        }

        import std.meta : AliasSeq;
        static foreach(alias ControlType; AliasSeq!(SharedControlType, shared SharedControlType)){{
            alias SPtr(T) = IntrusivePtr!(T, DestructorType!T);

            //mutable:
            {
                alias Ptr = SPtr!(Foo);
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
                static assert(__traits(compiles, const(shared(Ptr))(iptr)) == Ptr.sharedControl);

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
                alias Ptr = SPtr!(const Foo);
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
                static assert(__traits(compiles, shared(Ptr)(iptr)) == Ptr.sharedControl);
                static assert(__traits(compiles, const(shared(Ptr))(iptr)) == Ptr.sharedControl);

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
                alias Ptr = SPtr!(immutable Foo);
                Ptr ptr;
                static assert(__traits(compiles, Ptr(ptr)));
                static assert(__traits(compiles, const(Ptr)(ptr)));
                static assert(__traits(compiles, immutable(Ptr)(ptr)));
                static assert(__traits(compiles, shared(Ptr)(ptr)) == Ptr.sharedControl);
                static assert(__traits(compiles, const(shared(Ptr))(ptr)) == Ptr.sharedControl);

                const(Ptr) cptr;
                static assert(__traits(compiles, Ptr(cptr)));
                static assert(__traits(compiles, const(Ptr)(cptr)));
                static assert(__traits(compiles, immutable(Ptr)(cptr)));
                static assert(__traits(compiles, shared(Ptr)(cptr)) == Ptr.sharedControl);
                static assert(__traits(compiles, const(shared(Ptr))(cptr)) == Ptr.sharedControl);

                immutable(Ptr) iptr;
                static assert(__traits(compiles, Ptr(iptr)));
                static assert(__traits(compiles, const(Ptr)(iptr)));
                static assert(__traits(compiles, immutable(Ptr)(iptr)));
                static assert(__traits(compiles, shared(Ptr)(iptr)) == Ptr.sharedControl);
                static assert(__traits(compiles, const(shared(Ptr))(iptr)) == Ptr.sharedControl);

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
                alias Ptr = SPtr!(shared Foo);
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
                alias Ptr = SPtr!(const shared Foo);
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
        static struct Foo{
            ControlBlock!(int, int) c;
        }

        {
            IntrusivePtr!Foo x = null;

            assert(x == null);
            assert(x == IntrusivePtr!Foo.init);

        }

    }


    //opAssign(IntrusivePtr)
    pure nothrow @nogc unittest{
        static struct Foo{
            MutableControlBlock!(int, int) c;
            int i;

            this(int i)pure nothrow @safe @nogc{
                this.i = i;
            }
        }

        {
            IntrusivePtr!Foo px1 = IntrusivePtr!Foo.make(1);
            IntrusivePtr!Foo px2 = IntrusivePtr!Foo.make(2);

            assert(px2.useCount == 1);
            px1 = px2;
            assert(px1.get.i == 2);
            assert(px2.useCount == 2);
        }



        {
            IntrusivePtr!(Foo) px = IntrusivePtr!(Foo).make(1);
            IntrusivePtr!(const Foo) pcx = IntrusivePtr!(Foo).make(2);

            assert(px.useCount == 1);
            pcx = px;
            assert(pcx.get.i == 1);
            assert(pcx.useCount == 2);

        }


        {
            const IntrusivePtr!(Foo) cpx = IntrusivePtr!(Foo).make(1);
            IntrusivePtr!(const Foo) pcx = IntrusivePtr!(Foo).make(2);

            assert(pcx.useCount == 1);
            pcx = cpx;
            assert(pcx.get.i == 1);
            assert(pcx.useCount == 2);

        }

        {
            IntrusivePtr!(immutable Foo) pix = IntrusivePtr!(immutable Foo).make(123);
            IntrusivePtr!(const Foo) pcx = IntrusivePtr!(Foo).make(2);

            assert(pix.useCount == 1);
            pcx = pix;
            assert(pcx.get.i == 123);
            assert(pcx.useCount == 2);

        }
    }

    //opAssign(null)
    nothrow @safe @nogc unittest{
        static struct Foo{
            ControlBlock!(int, int) c;
            int i;

            this(int i)pure nothrow @safe @nogc{
                this.i = i;
            }
        }

        {
            IntrusivePtr!Foo x = IntrusivePtr!Foo.make(1);

            assert(x.useCount == 1);
            x = null;
            assert(x.useCount == 0);
            assert(x == null);
        }

        {
            IntrusivePtr!(shared Foo) x = IntrusivePtr!(shared Foo).make(1);

            assert(x.useCount == 1);
            x = null;
            assert(x.useCount == 0);
            assert(x == null);
        }

        import autoptr.internal.mutex : supportMutex;
        static if(supportMutex){
            shared IntrusivePtr!(shared Foo) x = IntrusivePtr!(shared Foo).make(1);

            assert(x.useCount == 1);
            x = null;
            assert(x.useCount == 0);
            assert(x.load == null);
        }
    }

    //useCount
    pure nothrow @safe @nogc unittest{
        static struct Foo{
            ControlBlock!(int, int) c;
            int i;

            this(int i)pure nothrow @safe @nogc{
                this.i = i;
            }
        }


        IntrusivePtr!Foo x = null;

        assert(x.useCount == 0);

        x = IntrusivePtr!Foo.make(123);
        assert(x.useCount == 1);

        auto y = x;
        assert(x.useCount == 2);

        auto w1 = x.weak;    //weak ptr
        assert(x.useCount == 2);

        IntrusivePtr!Foo.WeakType w2 = x;   //weak ptr
        assert(x.useCount == 2);

        y = null;
        assert(x.useCount == 1);

        x = null;
        assert(x.useCount == 0);
        assert(w1.useCount == 0);
    }

    //weakCount
    pure nothrow @safe @nogc unittest{
        static struct Foo{
            ControlBlock!(int, int) c;
            int i;

            this(int i)pure nothrow @safe @nogc{
                this.i = i;
            }
        }

        IntrusivePtr!Foo x = null;
        assert(x.useCount == 0);
        assert(x.weakCount == 0);

        x = IntrusivePtr!Foo.make(123);
        assert(x.useCount == 1);
        assert(x.weakCount == 0);

        auto w = x.weak();
        assert(x.useCount == 1);
        assert(x.weakCount == 1);
    }

    // store:
    nothrow @nogc unittest{
        static struct Foo{
            ControlBlock!(int, int) c;
            int i;

            this(int i)pure nothrow @safe @nogc{
                this.i = i;
            }
        }

        //null store:
        {
            shared x = IntrusivePtr!(shared Foo).make(123);
            assert(x.load.get.i == 123);

            x.store(null);
            assert(x.useCount == 0);
            assert(x.load == null);
        }

        //rvalue store:
        {
            shared x = IntrusivePtr!(shared Foo).make(123);
            assert(x.load.get.i == 123);

            x.store(IntrusivePtr!(shared Foo).make(42));
            assert(x.load.get.i == 42);
        }

        //lvalue store:
        {
            shared x = IntrusivePtr!(shared Foo).make(123);
            auto y = IntrusivePtr!(shared Foo).make(42);

            assert(x.load.get.i == 123);
            assert(y.load.get.i == 42);

            x.store(y);
            assert(x.load.get.i == 42);
            assert(x.useCount == 2);
        }
    }

    //load:
    nothrow @nogc unittest{
        static struct Foo{
            ControlBlock!(int, int) c;
            int i;

            this(int i)pure nothrow @safe @nogc{
                this.i = i;
            }
        }

        shared IntrusivePtr!(shared Foo) x = IntrusivePtr!(shared Foo).make(123);

        import autoptr.internal.mutex : supportMutex;
        static if(supportMutex){
            IntrusivePtr!(shared Foo) y = x.load();
            assert(y.useCount == 2);

            assert(y.get.i == 123);
        }

    }

    //exchange
    nothrow @nogc unittest{
        static struct Foo{
            ControlBlock!(int, int) c;
            int i;

            this(int i)pure nothrow @safe @nogc{
                this.i = i;
            }
        }

        //lvalue exchange
        {
            shared x = IntrusivePtr!(shared Foo).make(123);
            auto y = IntrusivePtr!(shared Foo).make(42);

            auto z = x.exchange(y);

            assert(x.load.get.i == 42);
            assert(y.get.i == 42);
            assert(z.get.i == 123);
        }

        //rvalue exchange
        {
            shared x = IntrusivePtr!(shared Foo).make(123);
            auto y = IntrusivePtr!(shared Foo).make(42);

            auto z = x.exchange(y.move);

            assert(x.load.get.i == 42);
            assert(y == null);
            assert(z.get.i == 123);
        }

        //null exchange (same as move)
        {
            shared x = IntrusivePtr!(shared Foo).make(123);

            auto z = x.exchange(null);

            assert(x.load == null);
            assert(z.get.i == 123);
        }

        //swap:
        {
            shared x = IntrusivePtr!(shared Foo).make(123);
            auto y = IntrusivePtr!(shared Foo).make(42);

            //opAssign is same as store
            y = x.exchange(y.move);

            assert(x.load.get.i == 42);
            assert(y.get.i == 123);
        }

    }


    //compareExchange
    pure nothrow @nogc unittest{
        static class Foo{
            long i;
            MutableControlBlock!(int, int) c;

            this(long i)pure nothrow @safe @nogc{
                this.i = i;
            }

            bool opEquals(this This)(long i)const @trusted{
                import std.traits : Unqual;
                auto self = cast(Unqual!This)this;
                return (self.i == i);
            }


        }
        alias Type = const Foo;
        static foreach(enum bool weak; [true, false]){
            //fail
            {
                IntrusivePtr!Type a = IntrusivePtr!Type.make(123);
                IntrusivePtr!Type b = IntrusivePtr!Type.make(42);
                IntrusivePtr!Type c = IntrusivePtr!Type.make(666);

                static if(weak)a.compareExchangeWeak(b, c);
                else a.compareExchangeStrong(b, c);

                assert(*a == 123);
                assert(*b == 123);
                assert(*c == 666);

            }

            //success
            {
                IntrusivePtr!Type a = IntrusivePtr!Type.make(123);
                IntrusivePtr!Type b = a;
                IntrusivePtr!Type c = IntrusivePtr!Type.make(666);

                static if(weak)a.compareExchangeWeak(b, c);
                else a.compareExchangeStrong(b, c);

                assert(*a == 666);
                assert(*b == 123);
                assert(*c == 666);
            }

            //shared fail
            {
                shared IntrusivePtr!(shared Type) a = IntrusivePtr!(shared Type).make(123);
                IntrusivePtr!(shared Type) b = IntrusivePtr!(shared Type).make(42);
                IntrusivePtr!(shared Type) c = IntrusivePtr!(shared Type).make(666);

                static if(weak)a.compareExchangeWeak(b, c);
                else a.compareExchangeStrong(b, c);

                auto tmp = a.exchange(null);
                assert(*tmp == 123);
                assert(*b == 123);
                assert(*c == 666);
            }

            //shared success
            {
                IntrusivePtr!(shared Type) b = IntrusivePtr!(shared Type).make(123);
                shared IntrusivePtr!(shared Type) a = b;
                IntrusivePtr!(shared Type) c = IntrusivePtr!(shared Type).make(666);

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
        static struct Foo{
            ControlBlock!(int, int) c;
            int i;

            this(int i)pure nothrow @safe @nogc{
                this.i = i;
            }
        }

        {
            IntrusivePtr!Foo x = IntrusivePtr!Foo.make(123);

            auto w = x.weak;    //weak ptr

            IntrusivePtr!Foo y = w.lock;

            assert(x == y);
            assert(x.useCount == 2);
            assert(y.get.i == 123);
        }

        {
            IntrusivePtr!Foo x = IntrusivePtr!Foo.make(123);

            auto w = x.weak;    //weak ptr

            assert(w.expired == false);

            x = IntrusivePtr!Foo.make(321);

            assert(w.expired == true);

            IntrusivePtr!Foo y = w.lock;

            assert(y == null);
        }
        {
            shared IntrusivePtr!(shared Foo) x = IntrusivePtr!(shared Foo).make(123);

            shared IntrusivePtr!(shared Foo).WeakType w = x.load.weak;    //weak ptr

            assert(w.expired == false);

            x = IntrusivePtr!(shared Foo).make(321);

            assert(w.expired == true);

            IntrusivePtr!(shared Foo) y = w.load.lock;

            assert(y == null);
        }
    }

    //expired
    nothrow @nogc unittest{
        static struct Foo{
            ControlBlock!(int, int) c;
            int i;

            this(int i)pure nothrow @safe @nogc{
                this.i = i;
            }
        }

        {
            IntrusivePtr!Foo x = IntrusivePtr!Foo.make(123);

            auto wx = x.weak;   //weak pointer

            assert(wx.expired == false);

            x = null;

            assert(wx.expired == true);
        }
    }

    //make
    pure nothrow @nogc unittest{
        static struct Foo{
            ControlBlock!(int, int) c;
            int i;

            this(int i)pure nothrow @safe @nogc{
                this.i = i;
            }
        }

        {
            IntrusivePtr!Foo a = IntrusivePtr!Foo.make();
            assert(a.get.i == 0);

            IntrusivePtr!(const Foo) b = IntrusivePtr!Foo.make(2);
            assert(b.get.i == 2);
        }

        {
            static struct Struct{
                ControlBlock!int c;
                int i = 7;

                this(int i)pure nothrow @safe @nogc{
                    this.i = i;
                }
            }

            IntrusivePtr!Struct s1 = IntrusivePtr!Struct.make();
            assert(s1.get.i == 7);

            IntrusivePtr!Struct s2 = IntrusivePtr!Struct.make(123);
            assert(s2.get.i == 123);
        }
    }

    //alloc
    pure nothrow @nogc unittest{
        static struct Foo{
            ControlBlock!(int, int) c;
            int i;

            this(int i)pure nothrow @safe @nogc{
                this.i = i;
            }
        }

        {
            TestAllocator allocator;

            {
                IntrusivePtr!Foo a = IntrusivePtr!Foo.alloc(&allocator);
                assert(a.get.i == 0);

                IntrusivePtr!(const Foo) b = IntrusivePtr!Foo.alloc(&allocator, 2);
                assert(b.get.i == 2);
            }

            {
                static struct Struct{
                    ControlBlock!(int) c;
                    int i = 7;

                    this(int i)pure nothrow @safe @nogc{
                        this.i = i;
                    }
                }

                IntrusivePtr!Struct s1 = IntrusivePtr!Struct.alloc(allocator);
                assert(s1.get.i == 7);

                IntrusivePtr!Struct s2 = IntrusivePtr!Struct.alloc(allocator, 123);
                assert(s2.get.i == 123);
            }

        }
    }

    //alloc
    unittest{
        static struct Foo{
            ControlBlock!(int, int) c;
            int i;

            this(int i)pure nothrow @safe @nogc{
                this.i = i;
            }
        }

        {
            import std.experimental.allocator : allocatorObject;

            auto a = allocatorObject(Mallocator.instance);
            {
                IntrusivePtr!Foo x = IntrusivePtr!Foo.alloc(a);
                assert(x.get.i == 0);

                IntrusivePtr!(const Foo) y = IntrusivePtr!Foo.alloc(a, 2);
                assert(y.get.i == 2);
            }

            {
                static struct Struct{
                    ControlBlock!(int) c;
                    int i = 7;

                    this(int i)pure nothrow @safe @nogc{
                        this.i = i;
                    }
                }

                IntrusivePtr!Struct s1 = IntrusivePtr!Struct.alloc(a);
                assert(s1.get.i == 7);

                IntrusivePtr!Struct s2 = IntrusivePtr!Struct.alloc(a, 123);
                assert(s2.get.i == 123);
            }

        }
    }

    //ctor
    pure nothrow @nogc @safe unittest{
        static struct Foo{
            MutableControlBlock!(int, int) c;
            int i;

            this(int i)pure nothrow @safe @nogc{
                this.i = i;
            }
        }

        {
            IntrusivePtr!Foo x = IntrusivePtr!Foo.make(123);
            assert(x.useCount == 1);

            IntrusivePtr!Foo a = x;         //lvalue copy ctor
            assert(a == x);

            const IntrusivePtr!Foo b = x;   //lvalue copy ctor
            assert(b == x);

            IntrusivePtr!Foo c = x; //lvalue ctor
            assert(c == x);

            const IntrusivePtr!Foo d = b;   //lvalue ctor
            assert(d == x);

            assert(x.useCount == 5);
        }

        {
            import core.lifetime : move;
            IntrusivePtr!Foo x = IntrusivePtr!Foo.make(123);
            assert(x.useCount == 1);

            IntrusivePtr!Foo a = move(x);        //rvalue copy ctor
            assert(a.useCount == 1);

            const IntrusivePtr!Foo b = move(a);  //rvalue copy ctor
            assert(b.useCount == 1);

            IntrusivePtr!(const Foo) c = b.load;  //rvalue ctor
            assert(c.useCount == 2);

            const IntrusivePtr!Foo d = move(c);  //rvalue ctor
            assert(d.useCount == 2);
        }

    }

    //weak
    pure nothrow @nogc unittest{
        static struct Foo{
            ControlBlock!(int, int) c;
            int i;

            this(int i)pure nothrow @safe @nogc{
                this.i = i;
            }
        }

        IntrusivePtr!Foo x = IntrusivePtr!Foo.make(123);
        assert(x.useCount == 1);
        auto wx = x.weak;   //weak pointer
        assert(wx.expired == false);
        assert(wx.lock.get.i == 123);
        assert(wx.useCount == 1);
        x = null;
        assert(wx.expired == true);
        assert(wx.useCount == 0);

    }

    //operator *
    pure nothrow @nogc unittest{
        static struct Foo{
            ControlBlock!(int, int) c;
            int i;
            alias i this;

            this(int i)pure nothrow @safe @nogc{
                this.i = i;
            }
        }

        IntrusivePtr!Foo x = IntrusivePtr!Foo.make(123);
        assert(*x == 123);
        ((*x).i = 321);
        assert(*x == 321);
        const y = x;
        assert(*y == 321);
        assert(*x == 321);
        static assert(is(typeof(*y) == const Foo));
    }

    //get
    pure nothrow @nogc unittest{
        static struct Foo{
            ControlBlock!(int, int) c;
            int i;

            this(int i)pure nothrow @safe @nogc{
                this.i = i;
            }
        }

        IntrusivePtr!Foo x = IntrusivePtr!Foo.make(123);
        assert(x.get.i == 123);
        x.get.i = 321;
        assert(x.get.i == 321);
        const y = x;
        assert(y.get.i == 321);
        assert(x.get.i == 321);
        static assert(is(typeof(y.get) == const Foo));
    }

    //element
    pure nothrow @nogc unittest{
        static struct Foo{
            ControlBlock!(int, int) c;
            int i;

            this(int i)pure nothrow @safe @nogc{
                this.i = i;
            }
        }

        IntrusivePtr!Foo x = IntrusivePtr!Foo.make(123);
        assert(x.element.i == 123);
        x.get.i = 321;
        assert(x.element.i == 321);
        const y = x;
        assert(y.element.i == 321);
        assert(x.element.i == 321);
        static assert(is(typeof(y.element) == const(Foo)*));
    }

    //opCast bool
    @safe pure nothrow @nogc unittest{
        static struct Foo{
            ControlBlock!(int, int) c;
            int i;

            this(int i)pure nothrow @safe @nogc{
                this.i = i;
            }
        }

        IntrusivePtr!Foo x = IntrusivePtr!Foo.make(123);
        assert(cast(bool)x);    //explicit cast
        assert(x);              //implicit cast
        x = null;
        assert(!cast(bool)x);   //explicit cast
        assert(!x);             //implicit cast
    }

    //opCast IntrusivePtr
    @safe pure nothrow @nogc unittest{
        static struct Foo{
            ControlBlock!(int, int) c;
            int i;
            alias i this;

            this(int i)pure nothrow @safe @nogc{
                this.i = i;
            }
        }

        import std.conv;

        IntrusivePtr!Foo x = IntrusivePtr!Foo.make(123);
        assert(x.useCount == 1
        );
        auto y = cast(IntrusivePtr!(const Foo))x;
        //debug assert(x.useCount == 2, x.useCount.to!string);
        assert(x.useCount == 2);


        auto z = cast(const IntrusivePtr!Foo)x;
        assert(x.useCount == 3);

        auto u = cast(const IntrusivePtr!(const Foo))x;
        assert(x.useCount == 4);
    }

    //opEquals IntrusivePtr
    pure @safe nothrow @nogc unittest{
        static struct Foo{
            ControlBlock!(int, int) c;
            int i;

            this(int i)pure nothrow @safe @nogc{
                this.i = i;
            }
        }

        {
            IntrusivePtr!Foo x = IntrusivePtr!Foo.make(0);
            assert(x != null);
            x = null;
            assert(x == null);
        }

        {
            IntrusivePtr!Foo x = IntrusivePtr!Foo.make(123);
            IntrusivePtr!Foo y = IntrusivePtr!Foo.make(123);
            assert(x == x);
            assert(y == y);
            assert(x != y);
        }

        {
            IntrusivePtr!Foo x;
            IntrusivePtr!(const Foo) y;
            assert(x == x);
            assert(y == y);
            assert(x == y);
        }
    }

    //opEquals IntrusivePtr
    pure nothrow @nogc unittest{
        static struct Foo{
            ControlBlock!(int, int) c;
            int i;

            this(int i)pure nothrow @safe @nogc{
                this.i = i;
            }
        }

        {
            IntrusivePtr!Foo x = IntrusivePtr!Foo.make(123);
            IntrusivePtr!Foo y = IntrusivePtr!Foo.make(123);
            assert(x == x.element);
            assert(y.element == y);
            assert(x != y.element);
        }
    }

    //opCmp
    pure nothrow @safe @nogc unittest{
        static struct Foo{
            ControlBlock!(int, int) c;
            int i;

            this(int i)pure nothrow @safe @nogc{
                this.i = i;
            }
        }

        {
            const a = IntrusivePtr!Foo.make(42);
            const b = IntrusivePtr!Foo.make(123);
            const n = IntrusivePtr!Foo.init;

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
        static struct Foo{
            ControlBlock!(int, int) c;
            int i;

            this(int i)pure nothrow @safe @nogc{
                this.i = i;
            }
        }

        {
            const a = IntrusivePtr!Foo.make(42);
            const b = IntrusivePtr!Foo.make(123);

            assert(a <= a.element);
            assert(a.element >= a);

            assert((a < b.element) == !(a.element >= b));
            assert((a > b.element) == !(a.element <= b));
        }
    }

    //toHash
    pure nothrow @safe @nogc unittest{
        static struct Foo{
            ControlBlock!(int, int) c;
            int i;

            this(int i)pure nothrow @safe @nogc{
                this.i = i;
            }
        }

        {
            IntrusivePtr!Foo x = IntrusivePtr!Foo.make(123);
            IntrusivePtr!Foo y = IntrusivePtr!Foo.make(123);
            assert(x.toHash == x.toHash);
            assert(y.toHash == y.toHash);
            assert(x.toHash != y.toHash);
            IntrusivePtr!(const Foo) z = x;
            assert(x.toHash == z.toHash);
        }
        {
            IntrusivePtr!Foo x;
            IntrusivePtr!(const Foo) y;
            assert(x.toHash == x.toHash);
            assert(y.toHash == y.toHash);
            assert(x.toHash == y.toHash);
        }
    }

    //proxySwap
    pure nothrow @nogc unittest{
        static struct Foo{
            ControlBlock!(int, int) c;
            int i;

            this(int i)pure nothrow @safe @nogc{
                this.i = i;
            }
        }

        {
            IntrusivePtr!Foo a = IntrusivePtr!Foo.make(1);
            IntrusivePtr!Foo b = IntrusivePtr!Foo.make(2);
            a.proxySwap(b);
            assert(a != null);
            assert(b != null);
            assert(a.get.i == 2);
            assert(b.get.i == 1);
            import std.algorithm : swap;
            swap(a, b);
            assert(a.get.i == 1);
            assert(b.get.i == 2);
            assert(a.useCount == 1);
            assert(b.useCount == 1);
        }
    }
}

