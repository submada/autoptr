/**
    Common code shared with other modules.

	License:   $(HTTP www.boost.org/LICENSE_1_0.txt, Boost License 1.0).
	Authors:   $(HTTP github.com/submada/basic_string, Adam Búš)
*/
module autoptr.common;

import std.meta : AliasSeq;
import std.stdio;
import std.traits : isFunctionPointer, isDelegate,
    functionAttributes, FunctionAttribute, SetFunctionAttributes, functionLinkage;


version(D_BetterC)
    package enum bool betterC = true;
else
    package enum bool betterC = false;



//generate `DestructorTypes` alias
version(D_BetterC){}else
private string genDestructorTypes(){
    string result;
    result.reserve(16*40);

    import std.range : empty;
    foreach(string _pure; ["pure", ""])
    foreach(string _nothrow; ["nothrow", ""])
    foreach(string _safe; ["@safe", "@system"])
    foreach(string _nogc; ["@nogc", ""])
        result ~= "void function(void* )" ~ _pure
            ~ (_pure.empty?"":" ") ~ _nothrow
            ~ ((_pure.empty && _nothrow.empty)?"":" ") ~ _safe
            ~ ((_pure.empty && _nothrow.empty && _safe.empty)?"":" ") ~ _nogc
            ~ ",\n";

    return result;
}


//create all possible DestructorType types, DestructorType can return type with some hidden information and comparsion with it can fail (bug in D compiler).
//If type is created before calling DestructorType then DestructorType return existing type free of hidden informations and comparsion is ok.
private alias DestructorTypes = AliasSeq!(
    void function(void* )pure nothrow @safe @nogc,
    void function(void* )pure nothrow @safe,
    void function(void* )pure nothrow @system @nogc,
    void function(void* )pure nothrow @system,
    void function(void* )pure @safe @nogc,
    void function(void* )pure @safe,
    void function(void* )pure @system @nogc,
    void function(void* )pure @system,
    void function(void* )nothrow @safe @nogc,
    void function(void* )nothrow @safe,
    void function(void* )nothrow @system @nogc,
    void function(void* )nothrow @system,
    void function(void* )@safe @nogc,
    void function(void* )@safe,
    void function(void* )@system @nogc,
    void function(void* )@system,
);


/**
    Check if type `Type` is of type destructor type (is(void function(void* )pure nothrow @safe @nogc : Type))
*/
public template isDestructorType(Type){
    import std.traits : Unqual;

    enum bool isDestructorType = true
        && is(void function(void* )pure nothrow @safe @nogc : Type);
}

///
unittest{
    static assert(isDestructorType!(void function(void* )pure));
    static assert(isDestructorType!(DestructorType!long));
    static assert(!isDestructorType!(long));
}



/**
    Type of destructor of `Type` ( void function(void*)@destructor_attributes ).
*/
public template DestructorType(Types...){

    import std.traits : Unqual;

    alias Get(T) = T;
    alias DestructorType = Get!(typeof(function void(void*){

        import autoptr.internal.destruct;
        static foreach(alias Type; Types){
            static if(is(Unqual!Type == void)){
            }
            else static if(is(Type == class)){

                _finalizeType!(Unqual!Type).init(null, true);
            }
            else{
                {
                    Unqual!Type tmp;

                    static if(is(Unqual!Type : void function(void*)pure nothrow @safe @nogc))
                        tmp(null);
                }
            }
        }
    }));

}


///
unittest{
    static assert(is(DestructorType!long == void function(void*)pure nothrow @safe @nogc));


    static struct Struct{
        ~this()nothrow @system{
        }
    }
    static assert(is(DestructorType!Struct == void function(void*)nothrow @system));


    static class Class{
        ~this()pure @trusted{

        }
    }
    static assert(is(DestructorType!Class == void function(void*)pure @safe));

    //multiple types:
    static assert(is(DestructorType!(Class, Struct, long) == void function(void*)@system));

    /+static assert(is(
        DestructorType!(Class, DestructorType!long, DestructorType!Struct) == DestructorType!(Class, Struct, long)
    ));+/
}



/**
    This template deduce `ControlType` shared qualifier in `SharedPtr` and `UniquePtr`.

    If `Type` is shared then `ControlType` is shared too (atomic counting).
*/
public template ControlTypeDeduction(Type, ControlType){
    import std.traits : Select;

    alias ControlTypeDeduction = Select!(
        is(Type == shared), /+|| is(Type == immutable)+/
        shared(ControlType),
        ControlType
    );
}

///
unittest{
    alias ControlType = ControlBlock!(int, int);
    
    static assert(is(ControlTypeDeduction!(long, ControlType) == ControlType));
    static assert(is(ControlTypeDeduction!(void, ControlType) == ControlType));
    static assert(is(ControlTypeDeduction!(shared double, ControlType) == shared ControlType));
    static assert(is(ControlTypeDeduction!(const int, ControlType) == ControlType));
    static assert(is(ControlTypeDeduction!(shared const int, ControlType) == shared ControlType));

    static assert(is(ControlTypeDeduction!(immutable int, ControlType) == ControlType));    

    static assert(is(ControlTypeDeduction!(shared int[], ControlType) == shared ControlType));
    static assert(is(ControlTypeDeduction!(shared(int)[], ControlType) == ControlType));
}


/**
    Check if type `T` is of type `ControlBlock!(...)`.
*/
public template isControlBlock(T...)
if(T.length == 1){
    import std.traits : Unqual, isMutable;

    enum bool isControlBlock = true
        && isMutable!(T[0])
        && is(Unqual!(T[0]) == ControlBlock!Args, Args...)
        ;
}

///
unittest{
    static assert(!isControlBlock!long);
    static assert(!isControlBlock!(void*));
    static assert(isControlBlock!(ControlBlock!long));  
    static assert(isControlBlock!(ControlBlock!(int, int)));
}


/**
    Control block for `SharedPtr` and `UniquePtr`.

    Contains ref counting and dynamic dispatching for destruction and dealocation of managed object for `SharedPtr` and `UniquePtr`.

    Template parameters:

        `_Shared` signed integer for ref counting of `SharedPtr` or void if ref counting is not necessary (`UniquePtr` doesn't need counting).

        `_Weak` signed integer for weak ref counting of `SharedPtr` or void if weak pointer is not necessary.

*/
public template ControlBlock(_Shared, _Weak = void){
    import std.traits : Unqual, isUnsigned, isIntegral, isMutable;
    import core.atomic;

    static assert((isIntegral!_Shared && !isUnsigned!_Shared) || is(_Shared == void));
    static assert(is(Unqual!_Shared == _Shared));

    static assert((isIntegral!_Weak && !isUnsigned!_Weak) || is(_Weak == void));
    static assert(is(Unqual!_Weak == _Weak));

    struct ControlBlock{
        /**
            Signed integer for ref counting of `SharedPtr` or void if ref counting is not necessary (`UniquePtr`). 
        */
        public alias Shared = _Shared;

        /**
            Signed integer for weak ref counting of `SharedPtr` or void if weak counting is not necessary (`UniquePtr` or `SharedPtr` without weak ptr).
        */
        public alias Weak = _Weak;

        /**
            `true` if `ControlBlock` has ref counting (`Shared != void`).
        */
        public enum bool hasSharedCounter = !is(Shared == void);

        /**
            `true` if `ControlBlock` has weak ref counting (`Weak != void`).
        */
        public enum bool hasWeakCounter = !is(Weak == void);
        

        static assert(hasSharedCounter >= hasWeakCounter);

        package static struct Vtable{

            static if(hasSharedCounter)
            void function(ControlBlock*)pure nothrow @safe @nogc on_zero_shared;

            static if(hasWeakCounter)
            void function(ControlBlock*)pure nothrow @safe @nogc on_zero_weak;

            void function(ControlBlock*, bool)pure nothrow @safe @nogc manual_destroy;

            bool initialized()const pure nothrow @safe @nogc{
                return manual_destroy !is null;
            } 

            bool valid()const pure nothrow @safe @nogc{
                bool result = true;
                static if(hasSharedCounter){
                    if(on_zero_shared is null)
                        return false;
                }
                static if(hasWeakCounter){
                    if(on_zero_weak is null)
                        return false;
                }

                return manual_destroy !is null;
            }
        }

        private immutable Vtable* vptr;

        static if(hasSharedCounter)
            private Shared shared_count = 0;

        static if(hasWeakCounter)
            private Weak weak_count = 0;

        package this(this This)(immutable Vtable* vptr)pure nothrow @safe @nogc
        if(isMutable!This){
            assert(vptr !is null);
            this.vptr = vptr;
        }

        package final auto count(bool weak)()const pure nothrow @safe @nogc{
            static if(weak){
                static if(hasWeakCounter)
                    return this.weak_count;
                else
                    return int.init;
            }
            else{
                static if(hasSharedCounter)
                    return this.shared_count;
                else
                    return int.max;
            }

        }
        package final auto count(bool weak)()shared const pure nothrow @safe @nogc{
            static if(weak){
                static if(hasWeakCounter)
                    return atomicLoad(this.weak_count);
                else
                    return int.init;
            }
            else{
                static if(hasSharedCounter)
                    return atomicLoad(this.shared_count);
                else
                    return int.max;
            }

        }

        package final void add(bool weak, this This)()@trusted pure nothrow @nogc
        if(isMutable!This){
            enum bool atomic = is(This == shared);

            static if(weak){
                static if(hasWeakCounter){
                    rc_increment!atomic(this.weak_count);
                }
            }
            else{
                static if(hasSharedCounter){
                    rc_increment!atomic(this.shared_count);
                }
            }
        }

        package final void release(bool weak, this This)()@trusted pure nothrow @nogc
        if(isMutable!This){
            enum bool atomic = is(This == shared);

            static if(weak){
                static if(hasWeakCounter){
                    static if(atomic){
                        if(atomicLoad!(MemoryOrder.acq)(this.weak_count) == 0)
                            this.on_zero_weak();

                        else if(rc_decrement!atomic(this.weak_count) == -1)
                            this.on_zero_weak();
                    }
                    else{
                        if(this.weak_count == 0)
                            this.on_zero_weak();
                        else if(rc_decrement!atomic(this.weak_count) == -1)
                            this.on_zero_weak();
                    }
                }
            }
            else{
                static if(hasSharedCounter){
                    if(rc_decrement!atomic(this.shared_count) == -1){
                        this.on_zero_shared();
                        this.release!true;
                    }
                }
            }
        }

        static if(hasSharedCounter){
            package final bool add_shared_if_exists()@trusted pure nothrow @nogc{

                if(this.shared_count == -1){
                    return false;
                }
                this.shared_count += 1;
                return true;
            }

            package final bool add_shared_if_exists()shared @trusted pure nothrow @nogc{
                auto owners = atomicLoad(this.shared_count);

                while(owners != -1){
                    import core.atomic;
                    if(casWeak(&this.shared_count,
                        &owners,
                        cast(Shared)(owners + 1)
                    )){
                        return true;
                    }
                }

                return false;
            }
        }

        static if(hasSharedCounter)
        package void on_zero_shared(this This)()pure nothrow @nogc @trusted{
            this.vptr.on_zero_shared(cast(ControlBlock*)&this);
        }

        static if(hasWeakCounter)
        package void on_zero_weak(this This)()pure nothrow @nogc @trusted{
            this.vptr.on_zero_weak(cast(ControlBlock*)&this);
        }

        package void manual_destroy(this This)(bool dealocate)pure nothrow @nogc @trusted{
            this.vptr.manual_destroy(cast(ControlBlock*)&this, dealocate);
        }
    }
}


///
unittest{
    static assert(is(ControlBlock!(int, long).Shared == int));
    static assert(is(ControlBlock!(int, long).Weak == long));
    static assert(is(ControlBlock!int.Shared == int));
    static assert(is(ControlBlock!int.Weak == void));

    static assert(ControlBlock!(int, int).hasSharedCounter);
    static assert(ControlBlock!(int, int).hasWeakCounter);

    static assert(is(ControlBlock!int == ControlBlock!(int, void)));  
    static assert(ControlBlock!int.hasSharedCounter);   
    static assert(ControlBlock!int.hasWeakCounter == false);

    static assert(ControlBlock!void.hasSharedCounter == false);
    static assert(ControlBlock!void.hasWeakCounter == false);
}


package template MakeEmplace(_Type, _DestructorType, _ControlType, AllocatorType, bool supportGC){

    alias AllocatorWithState = .AllocatorWithState!AllocatorType;

    enum bool hasStatelessAllocator = (AllocatorWithState.length == 0);

    static assert(!isAbstractClass!_Type,
        "cannot create object of abstract class" ~ Unqual!_Type.stringof
    );
    static assert(!is(_Type == interface),
        "cannot create object of interface type " ~ Unqual!_Type.stringof
    );

    static assert(false
        || hasStatelessAllocator 
        || isReferenceType!AllocatorType 
        || is(.DestructorType!AllocatorType : _DestructorType),
            "destructor of type '" ~ AllocatorType.stringof ~ 
            "' doesn't support specified finalizer " ~ _DestructorType.stringof
    );

    import core.lifetime : emplace;
    import std.traits: hasIndirections, isAbstractClass, Select, isMutable, CopyTypeQualifiers, Unqual;

    enum bool hasWeakCounter = _ControlType.hasWeakCounter;

    enum bool hasSharedCounter = _ControlType.hasSharedCounter;

    //enum bool referenceElementType = isReferenceType!_Type;

    enum bool allocatorGCRange = supportGC
        && !hasStatelessAllocator
        && hasIndirections!AllocatorType;

    enum bool dataGCRange = supportGC
        && (false
            || classHasIndirections!_Type
            || hasIndirections!_Type
            || (is(_Type == class) && is(Unqual!_Type : Object))
        );

    alias Vtable = _ControlType.Vtable;


    struct MakeEmplace{
        private static immutable Vtable vtable;
        private _ControlType control;
        private void[instanceSize!_Type] data;

        static if(!hasStatelessAllocator)
            private AllocatorType allocator;

        static assert(control.offsetof + typeof(control).sizeof == data.offsetof);

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


        public @property _ControlType* base()pure nothrow @safe @nogc{
            static assert(this.control.offsetof == 0);
            return &this.control;
        }

        public @property PtrOrRef!_Type get()pure nothrow @trusted @nogc{
            return cast(PtrOrRef!_Type)this.data.ptr;
        }




        public static MakeEmplace* make(Args...)(AllocatorWithState[0 .. $] a, auto ref Args args){
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

            MakeEmplace* result = (()@trusted => cast(MakeEmplace*)raw.ptr)();

            static if(dataGCRange){
                static assert(supportGC);
                static if(!hasStatelessAllocator)
                static assert(typeof(this).data.offsetof < typeof(this).allocator.offsetof);

                static if(allocatorGCRange)
                    enum size_t gc_range_size = typeof(this).allocator.offsetof
                        - typeof(this).data.offsetof
                        + typeof(this.allocator).sizeof;
                else
                    enum size_t gc_range_size = data.length;

                gc_add_range(
                    (()@trusted => cast(void*)result.data.ptr)(),
                    gc_range_size
                );
            }
            else static if(allocatorGCRange){
                static assert(supportGC);
                static assert(!dataGCRange);

                gc_add_range(
                    cast(void*)&result.allocator,
                    AllocatorType.sizeof
                );
            }

            return emplace(result, null, forward!(a, args));
        }


        public this(this This, Args...)(typeof(null) nil, AllocatorWithState[0 .. $] a, auto ref Args args)
        if(isMutable!This){
            version(D_BetterC){
                if(!vtable.initialized())
                    shared_static_this();
            }
            else
                assert(vtable.initialized());

            this.control = _ControlType(&vtable);
            assert(vtable.valid, "vtables are not initialized");

            import core.lifetime : forward, emplace;

            static if(!hasStatelessAllocator)
                this.allocator = forward!(a[0]);

            import std.traits : isStaticArray;
            import std.range : ElementEncodingType;

            static if(is(Unqual!_Type == void)){
                //nothing
            }
            else static if(isStaticArray!_Type){
                static if(args.length == 1 && is(Args[0] : _Type)){
                    //cast(void)emplace!(_Type)(this.data, forward!args);
                    cast(void)emplace(
                        ((ref data)@trusted => cast(_Type*)data.ptr)(this.data),
                        forward!args
                    );
                }
                else{
                    _Type* data = cast(_Type*)this.data.ptr;

                    foreach(ref ElementEncodingType!_Type d; (*data)[]){

                        static if(isReferenceType!(ElementEncodingType!_Type)){
                            static if(args.length == 0)
                                d = null;
                            else static if(args.length == 1)
                                d = args[0];
                            else static assert(0, "no impl");

                        }
                        else{
                            cast(void)emplace(&d, args);
                        }
                    }
                }
            }
            else{
                static if(isReferenceType!_Type)
                    auto data = ((ref data)@trusted => cast(_Type)data.ptr)(this.data);
                else
                    auto data = ((ref data)@trusted => cast(_Type*)data.ptr)(this.data);

                cast(void)emplace(
                    data,
                    forward!args
                );
            }

            debug _log_ptr_construct();
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

        private static inout(MakeEmplace)* get_offset_this(inout(Unqual!_ControlType)* control)pure nothrow @trusted @nogc{
            assert(control !is null);
            return cast(typeof(return))((cast(void*)control) - MakeEmplace.control.offsetof);
        }


        private void destruct()pure nothrow @trusted @nogc{

            static if(is(_Type == struct) || is(_Type == class)){
                _destruct!(_Type, DestructorType!void)(this.data.ptr);

                static if(!allocatorGCRange && dataGCRange){
                    gc_remove_range(this.data.ptr);
                }

            }
            else static if(is(_Type == interface)){
                assert(0, "no impl");
            }
            else{
                // nothing
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
                static if(dataGCRange)
                    gc_remove_range(this.data.ptr);
                else
                    gc_remove_range(&this.allocator);
            }

            debug _log_ptr_deallocate();
        }

    }
}

package template MakeDynamicArray(_Type, _DestructorType, _ControlType, AllocatorType, bool supportGC){
    static assert(isDynamicArray!_Type);

    import std.range : ElementEncodingType;

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
        || isReferenceType!(ElementEncodingType!_Type) 
        || is(.DestructorType!(ElementEncodingType!_Type) : _DestructorType),
            "destructor of type '" ~ ElementEncodingType!_Type.stringof ~ 
            " (" ~ .DestructorType!(ElementEncodingType!_Type).stringof ~ ")" ~ 
            "' doesn't support specified finalizer " ~ _DestructorType.stringof
    );

    import std.traits: hasIndirections, isAbstractClass, isDynamicArray, Unqual;

    enum bool hasWeakCounter = _ControlType.hasWeakCounter;

    enum bool hasSharedCounter = _ControlType.hasSharedCounter;

    //enum bool referenceElementType = isReferenceType!_Type;

    enum bool allocatorGCRange = supportGC
        && !hasStatelessAllocator
        && hasIndirections!AllocatorType;

    enum bool dataGCRange = supportGC
        && hasIndirections!(ElementEncodingType!_Type);

    alias Vtable = _ControlType.Vtable;

    struct MakeDynamicArray{
        static if(!hasStatelessAllocator)
            private AllocatorType allocator;

        private size_t length;
        private _ControlType control;
        private ElementEncodingType!_Type[0] data_impl;

        static assert(control.offsetof + typeof(control).sizeof == data_impl.offsetof);

        @property inout(ElementEncodingType!_Type)[] data()inout pure nothrow @trusted @nogc{
            return data_impl.ptr[0 .. this.length];
        }

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

        public @property _ControlType* base()pure nothrow @safe @nogc{
            return &this.control;
        }

        public @property auto get()pure nothrow @trusted @nogc{
            return this.data;
        }




        public static MakeDynamicArray* make(Args...)(AllocatorWithState[0 .. $] a, const size_t n, auto ref Args args){
            import std.traits: hasIndirections;
            import core.lifetime : forward, emplace;

            const size_t arraySize = (ElementEncodingType!_Type.sizeof * n);

            static if(hasStatelessAllocator)
                void[] raw = statelessAllcoator!AllocatorType.allocate(typeof(this).sizeof + arraySize);
            else
                void[] raw = a[0].allocate(typeof(this).sizeof + arraySize);

            if(raw.length == 0)
                return null;

            debug _log_ptr_allocate();

            MakeDynamicArray* result = (()@trusted => cast(MakeDynamicArray*)raw.ptr)();


            static if(allocatorGCRange){
                static assert(supportGC);
                static assert(typeof(this).length.offsetof >= typeof(this).allocator.offsetof);

                static if(dataGCRange)
                    const size_t gc_range_size = typeof(this).sizeof
                        - typeof(this).allocator.offsetof
                        + arraySize;
                else
                    enum size_t gc_range_size = AllocatorType.sizeof;

                gc_add_range(
                    cast(void*)&result.allocator,
                    gc_range_size
                );
            }
            else static if(dataGCRange){
                static assert(supportGC);
                static assert(!allocatorGCRange);

                gc_add_range(
                    (()@trusted => result.data.ptr)(),
                    arraySize   //result.data.length * _Type.sizeof
                );
            }

            return emplace!MakeDynamicArray(result, forward!(a, n, args));
        }


        public this(Args...)(AllocatorWithState[0 .. $] a, const size_t n, auto ref Args args){
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

            this.length = n;

            import core.lifetime : emplace;

            foreach(ref d; this.data[])
                emplace((()@trusted => &d)(), args);

            debug _log_ptr_construct();
        }


        static if(hasSharedCounter)
        private static void virtual_on_zero_shared(Unqual!_ControlType* control)pure nothrow @nogc @safe{
            auto self = get_offset_this(control);
            self.destruct();

            static if(!hasWeakCounter)
                self.deallocate();
        }

        static if(hasWeakCounter)
        private static void virtual_on_zero_weak(Unqual!_ControlType* control)pure nothrow @nogc @safe{
            auto self = get_offset_this(control);
            self.deallocate();
        }

        private static void virtual_manual_destroy(Unqual!_ControlType* control, bool deallocate)pure nothrow @trusted @nogc{
            auto self = get_offset_this(control);
            self.destruct();

            if(deallocate)
                self.deallocate();
        }

        private static inout(MakeDynamicArray)* get_offset_this(inout(Unqual!_ControlType)* control)pure nothrow @trusted @nogc{
            assert(control !is null);
            return cast(typeof(return))((cast(void*)control) - MakeDynamicArray.control.offsetof);
        }

        private void destruct()pure nothrow @trusted @nogc{

            static if(is(ElementEncodingType!_Type == struct)){
                foreach(ref elm; this.data)
                    _destruct!(ElementEncodingType!_Type, DestructorType!void)(&elm);
            }

            static if(!allocatorGCRange && dataGCRange){
                gc_remove_range(this.data.ptr);
            }

            debug _log_ptr_destruct();
        }

        private void deallocate()pure nothrow @trusted @nogc{
            const size_t data_length = ElementEncodingType!_Type.sizeof * this.data.length;

            void* self = cast(void*)&this;
            _destruct!(typeof(this), DestructorType!void)(self);


            void[] raw = self[0 .. typeof(this).sizeof + data_length];



            static if(hasStatelessAllocator)
                assumePureNoGcNothrow(function(void[] raw)@trusted => statelessAllcoator!AllocatorType.deallocate(raw))(raw);
            else
                assumePureNoGcNothrow(function(void[] raw, ref typeof(this.allocator) allo)@trusted => allo.deallocate(raw))(raw, this.allocator);


            static if(allocatorGCRange){
                gc_remove_range(&this.allocator);
            }

            debug _log_ptr_deallocate();
        }

    }
}



package const(void)* elementAddress(Elm)(const Elm elm)pure nothrow @trusted @nogc{
    if(this == null)
        return null;

    static if(is(Unqual!Elm == typeof(null))){
        return null;
    }
    else static if(isDynamicArray!Elm){
        return cast(const void*)elm.ptr;
    }
    else static if(isReferenceType!Elm){
        return cast(const void*)cast(const Object)cast(const Unqual!Elm)elm;
    }
    else static if(isPointer!Elm){
        return cast(const void*)elm;
    }
    else static assert(0, "no impl " ~ Elm.stringof);
}


version(D_BetterC){
    package enum bool platformSupportGC = false;
}
else{
    package enum bool platformSupportGC = true;
}


import autoptr.internal.mallocator;

/**
    Default allcoator for `SharedPtr.make` and `UniquePtr.make`.
*/
public alias DefaultAllocator = Mallocator;


package auto assumeNoGC(T)(T t)@trusted
in(isFunctionPointer!T || isDelegate!T){

    enum attrs = functionAttributes!T | FunctionAttribute.nogc;
    return cast(SetFunctionAttributes!(T, functionLinkage!T, attrs)) t;
}

package auto assumePure(T)(T t)@trusted
in(isFunctionPointer!T || isDelegate!T){
    import std.traits;

    enum attrs = functionAttributes!T | FunctionAttribute.pure_;
    return cast(SetFunctionAttributes!(T, functionLinkage!T, attrs)) t;
}

package auto assumePureNoGc(T)(T t)@trusted
in(isFunctionPointer!T || isDelegate!T){
    import std.traits;

    enum attrs = functionAttributes!T | FunctionAttribute.pure_ | FunctionAttribute.nogc;
    return cast(SetFunctionAttributes!(T, functionLinkage!T, attrs)) t;
}

package auto assumePureNoGcNothrow(T)(T t)@trusted
in(isFunctionPointer!T || isDelegate!T){
    import std.traits;

    enum attrs = functionAttributes!T | FunctionAttribute.pure_ | FunctionAttribute.nogc | FunctionAttribute.nothrow_;
    return cast(SetFunctionAttributes!(T, functionLinkage!T, attrs)) t;
}

version(D_BetterC){}else
@nogc unittest{
    int *i = assumeNoGC({return new int;})();

}

//Same as `std.traits.hasIndirections` but for classes.
package template classHasIndirections(T){
    import std.traits : hasIndirections;

    static if(is(T == class)){
        enum bool classHasIndirections = (){

            import std.traits : BaseClassesTuple;
            import std.meta : AliasSeq;

            bool has_indirection = false;

            TOP:foreach (B; AliasSeq!(T, BaseClassesTuple!T)) {
                static foreach(alias var; B.tupleof){
                    if(hasIndirections!(typeof(var))){
                        has_indirection = true;
                        break TOP;
                    }
                }
            }

            return has_indirection;
        }();
    }
    else{
        enum bool classHasIndirections = false;
    }
}

//alias to `T` if `T` is class or interface, otherwise `T*`.
package template PtrOrRef(T){
    static if(is(T == class) || is(T == interface))
        alias PtrOrRef = T;
    else
        alias PtrOrRef = T*;
}

package enum bool isReferenceType(T) = is(T == class) || is(T == interface);



package template ElementReferenceTypeImpl(Type){
    import std.traits : Select, isDynamicArray;
    import std.range : ElementEncodingType;

    static if(isDynamicArray!Type)
        alias ElementReferenceTypeImpl = ElementEncodingType!Type[];
    else
        alias ElementReferenceTypeImpl = PtrOrRef!Type;

}

//alias to `AliasSeq` containing `T` if `T` has state, otherwise a empty tuple.
package template AllocatorWithState(T){
    import std.experimental.allocator.common : stateSize;
    import std.meta : AliasSeq;

    enum bool hasStatelessAllocator = (stateSize!T == 0);

    static if(stateSize!T == 0)
        alias AllocatorWithState = AliasSeq!();
    else
        alias AllocatorWithState = AliasSeq!T;
}

//alias to stateless allocator instance
package template statelessAllcoator(T){
    import std.experimental.allocator.common : stateSize;
    import std.traits : hasStaticMember;

    static assert(stateSize!T == 0);

    static if(hasStaticMember!(T, "instance"))
        alias statelessAllcoator = T.instance;
    else 
        enum T statelessAllcoator = T.init;   
}

//Size of instance, if `T` is class then `__traits(classInstanceSize, T)`, otherwise `T.sizeof`
package template instanceSize(T){
    static if(is(T == class))
        enum size_t instanceSize = __traits(classInstanceSize, T);
    else
        enum size_t instanceSize = T.sizeof;

}

//Destruct _payload as if is type of `Type` and destructor has type qualifiers as `DestructorType`
package void _destruct(Type, DestructorType)(void* _payload)
if(!is(Type == interface) && isDestructorType!DestructorType){
    import std.traits : Unqual;
    import autoptr.internal.destruct;

    alias Get(T) = T;

    static if(is(Type == class)){
        template finalizer(F){
            static extern(C) alias finalizer = typeof(function void(void* p, bool det = true) {
                F fn;
                fn(p);
            });
        }

        alias FinalizeType = finalizer!DestructorType;


        auto obj = (()@trusted => cast(Unqual!Type)_payload )();

        static assert(is(.DestructorType!(typeof(obj)) : DestructorType));
        /+static assert(is(Get!(_finalizeType!(typeof(obj))) : Get!FinalizeType),
            Get!(_finalizeType!(typeof(obj))).stringof ~ " : " ~ Get!FinalizeType.stringof
        );+/

        static if(__traits(getLinkage, Type) == "D"){
            //destruct(obj);
            FinalizeType finalize = ()@trusted{
                return cast(FinalizeType) &rt_finalize;
            }();

            finalize(() @trusted { return cast(void*) obj; }(), true);
        }
        else static if (__traits(getLinkage, Type) == "C++"){
            static if (__traits(hasMember, Type, "__xdtor")){
                obj.__xdtor();
                if(obj is null){
                    FinalizeType f;
                    f(null);
                }
            }

            /+static if (initialize)
            {
                enum classSize = __traits(classInstanceSize, T);
                (cast(void*)obj)[0 .. classSize] = typeid(T).initializer[];
            }+/
        }
        else static assert(0, "no impl");
    }

    else{
        auto obj = (()@trusted => cast(Unqual!Type*)_payload )();

        if(false){
            DestructorType f;
            f(null);
        }
        assumePureNoGcNothrow((typeof(obj) o)@trusted{
            destruct(*o);
        })(obj);

        //destruct(*obj);
    }
}


debug{
    package __gshared long _conter_constructs = 0;
    package __gshared long _conter_allocations = 0;

    package void _log_ptr_allocate()pure nothrow @safe @nogc{
        import core.atomic;

        assumePure(function void()@trusted{
            atomicFetchAdd!(MemoryOrder.raw)(_conter_allocations, 1);
        })();
    }
    package void _log_ptr_construct()pure nothrow @safe @nogc{
        import core.atomic;

        assumePure(function void()@trusted{
            atomicFetchAdd!(MemoryOrder.raw)(_conter_constructs, 1);
        })();

    }
    package void _log_ptr_deallocate()pure nothrow @safe @nogc{
        import core.atomic;

        assumePure(function void()@trusted{
            atomicFetchSub!(MemoryOrder.raw)(_conter_allocations, 1);
        })();
    }
    package void _log_ptr_destruct()pure nothrow @safe @nogc{
        import core.atomic;

        assumePure(function void()@trusted{
            atomicFetchSub!(MemoryOrder.raw)(_conter_constructs, 1);
        })();
    }

    shared static ~this(){
        import std.conv;
        if(_conter_allocations != 0)
            assert(0, "_conter_allocations: " ~ _conter_allocations.to!string);

        if(_conter_constructs != 0)
            assert(0, "_conter_constructs: " ~ _conter_constructs.to!string);


    }
}

//increment counter and return new value, if counter is shared then atomic increment is used.
private static T rc_increment(bool atomic, T)(ref T counter){
    static if(atomic || is(T == shared)){
        import core.atomic;

        debug{
            import std.traits : Unqual;

            auto tmp1 = cast(Unqual!T)counter;
            auto result1 = (tmp1 += 1);

            auto tmp2 = cast(Unqual!T)counter;
            auto result2 = atomicFetchAdd!(MemoryOrder.raw)(tmp2, 1) + 1;

            assert(result1 == result2);
        }

        return atomicFetchAdd!(MemoryOrder.raw)(counter, 1) + 1;
    }
    else{
        return counter += 1;
    }
}

unittest{
    import core.atomic;

    const int counter = 0;
    int tmp1 = counter;
    int result1 = (tmp1 += 1);
    assert(result1 == 1);

    int tmp2 = counter;
    int result2 = atomicFetchAdd!(MemoryOrder.raw)(tmp2, 1) + 1;
    assert(result2 == 1);

    assert(result1 == result2);
}

//decrement counter and return new value, if counter is shared then atomic increment is used.
private static T rc_decrement(bool atomic, T)(ref T counter){
    static if(atomic || is(T == shared)){
        import core.atomic;

        debug{
            import std.traits : Unqual;

            auto tmp1 = cast(Unqual!T)counter;
            auto result1 = (tmp1 -= 1);

            auto tmp2 = cast(Unqual!T)counter;
            auto result2 = atomicFetchSub!(MemoryOrder.acq_rel)(tmp2, 1) - 1;

            assert(result1 == result2);

        }

        //return atomicFetchAdd!(MemoryOrder.acq_rel)(counter, -1);
        return atomicFetchSub!(MemoryOrder.acq_rel)(counter, 1) - 1;
    }
    else{
        return counter -= 1;
    }
}

unittest{
    import core.atomic;

    const int counter = 0;
    int tmp1 = counter;
    int result1 = (tmp1 -= 1);
    assert(result1 == -1);

    int tmp2 = counter;
    int result2 = atomicFetchSub!(MemoryOrder.acq_rel)(tmp2, 1) - 1;
    assert(result2 == -1);

    assert(result1 == result2);
}


debug{
    package __gshared long _conter_gc_ranges = 0;

    version(D_BetterC){}else
    package __gshared const(void)[][] _gc_ranges = null;

    shared static ~this(){
        import std.conv;
        if(_conter_gc_ranges != 0)
            assert(0, "_conter_gc_ranges: " ~ _conter_gc_ranges.to!string);


        version(D_BetterC){}else
            foreach(const(void)[] gcr; _gc_ranges){
                assert(gcr.length == 0);
            }
    }
}

//same as GC.addRange but `pure nothrow @trusted @nogc` and with debug testing
package void gc_add_range(const void* data, const size_t length)pure nothrow @trusted @nogc{
    assumePure(function void(const void* ptr, const size_t len){
        import core.memory: GC;
        GC.addRange(ptr, len);
    })(data, length);

    assert(data !is null);
    assert(length > 0);

    debug{
        assumePureNoGc(function void(const void* data, const size_t length)@trusted{
            import core.atomic;
            atomicFetchAdd!(MemoryOrder.raw)(_conter_gc_ranges, 1);



            version(D_BetterC){}else{
                foreach(const void[] gcr; _gc_ranges){
                    if(gcr.length == 0)
                        continue;

                    const void* gcr_end = (gcr.ptr + gcr.length);
                    assert(!(data <= gcr.ptr && gcr.ptr < (data + length)));
                    assert(!(data < gcr_end && gcr_end <= (data + length)));
                    assert(!(gcr.ptr <= data && (data + length) <= gcr_end));
                }

                foreach(ref const(void)[] gcr; _gc_ranges){
                    if(gcr.length == 0){
                        gcr = data[0 .. length];
                        return;
                    }
                }

                _gc_ranges ~= data[0 .. length];

            }

        })(data, length);

    }

}

//same as GC.removeRange but `pure nothrow @trusted @nogc` and with debug testing
package void gc_remove_range(const void* data)pure nothrow @trusted @nogc{
    assumePure(function void(const void* ptr){
        import core.memory: GC;
        GC.removeRange(ptr);
    })(data);

    assert(data !is null);

    debug{
        assumePure(function void()@trusted{
            import core.atomic;
            atomicFetchSub!(MemoryOrder.raw)(_conter_gc_ranges, 1);
        })();

        version(D_BetterC){}else{
            foreach(ref const(void)[] gcr; _gc_ranges){
                if(gcr.ptr is data){
                    gcr = null;
                    return;
                }
                const void* gcr_end = (gcr.ptr + gcr.length);
                assert(!(gcr.ptr <= data && data < gcr_end));
            }

            assert(0, "missing gc range");
        }

    }

}
