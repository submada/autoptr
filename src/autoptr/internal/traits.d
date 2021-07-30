module autoptr.internal.traits;



import std.traits : isFunctionPointer, isDelegate;

public auto assumeNoGC(T)(T t)@trusted
in(isFunctionPointer!T || isDelegate!T){
    import std.traits : functionAttributes, FunctionAttribute, SetFunctionAttributes, functionLinkage;

    enum attrs = functionAttributes!T | FunctionAttribute.nogc;
    return cast(SetFunctionAttributes!(T, functionLinkage!T, attrs)) t;
}

public auto assumePure(T)(T t)@trusted
in(isFunctionPointer!T || isDelegate!T){
    import std.traits : functionAttributes, FunctionAttribute, SetFunctionAttributes, functionLinkage;

    enum attrs = functionAttributes!T | FunctionAttribute.pure_;
    return cast(SetFunctionAttributes!(T, functionLinkage!T, attrs)) t;
}

public auto assumePureNoGc(T)(T t)@trusted
in(isFunctionPointer!T || isDelegate!T){
    import std.traits : functionAttributes, FunctionAttribute, SetFunctionAttributes, functionLinkage;

    enum attrs = functionAttributes!T | FunctionAttribute.pure_ | FunctionAttribute.nogc;
    return cast(SetFunctionAttributes!(T, functionLinkage!T, attrs)) t;
}

public auto assumePureNoGcNothrow(T)(T t)@trusted
in(isFunctionPointer!T || isDelegate!T){
    import std.traits : functionAttributes, FunctionAttribute, SetFunctionAttributes, functionLinkage;

    enum attrs = functionAttributes!T | FunctionAttribute.pure_ | FunctionAttribute.nogc | FunctionAttribute.nothrow_;
    return cast(SetFunctionAttributes!(T, functionLinkage!T, attrs)) t;
}

public alias Unshared(T) = T;
public alias Unshared(T: shared U, U) = U;

//Same as `std.traits.hasIndirections` but for classes.
public template classHasIndirections(T){
    import std.traits : hasIndirections;

    static if(is(T == class)){
        enum bool classHasIndirections = (){

            import std.traits : BaseClassesTuple;
            import std.meta : AliasSeq;

            bool has_indirection = false;

            static foreach (alias B; AliasSeq!(T, BaseClassesTuple!T)) {
                static foreach(alias Var; typeof(B.init.tupleof)){
                    static if(hasIndirections!Var){
                        has_indirection = true;
                        //has_indirection = true;
                        //break TOP;
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
public template PtrOrRef(T){
    static if(is(T == class) || is(T == interface))
        alias PtrOrRef = T;
    else
        alias PtrOrRef = T*;
}

public enum bool isReferenceType(T) = is(T == class) || is(T == interface);



public template ElementReferenceTypeImpl(Type){
    import std.traits : Select, isDynamicArray;
    import std.range : ElementEncodingType;

    static if(isDynamicArray!Type)
        alias ElementReferenceTypeImpl = ElementEncodingType!Type[];
    else
        alias ElementReferenceTypeImpl = PtrOrRef!Type;

}

//alias to `AliasSeq` containing `T` if `T` has state, otherwise a empty tuple.
public template AllocatorWithState(T){
    import std.experimental.allocator.common : stateSize;
    import std.meta : AliasSeq;

    enum bool hasStatelessAllocator = (stateSize!T == 0);

    static if(stateSize!T == 0)
        alias AllocatorWithState = AliasSeq!();
    else
        alias AllocatorWithState = AliasSeq!T;
}

//alias to stateless allocator instance
public template statelessAllcoator(T){
    import std.experimental.allocator.common : stateSize;
    import std.traits : hasStaticMember;

    static assert(stateSize!T == 0);

    static if(hasStaticMember!(T, "instance"))
        alias statelessAllcoator = T.instance;
    else 
        enum T statelessAllcoator = T.init;   
}

//Size of instance, if `T` is class then `__traits(classInstanceSize, T)`, otherwise `T.sizeof`
public template instanceSize(T){
    static if(is(T == class))
        enum size_t instanceSize = __traits(classInstanceSize, T);
    else
        enum size_t instanceSize = T.sizeof;

}