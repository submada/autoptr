module autoptr.internal.test_allocator;

public struct TestAllocator{
    import std.experimental.allocator.common : platformAlignment, stateSize;
    static assert(stateSize!TestAllocator > 0);
    private int x;

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
