# Autoptr
## C++-style smart pointers for D using `std.experimental.allocator`.

This library contains:
* `SharedPtr` is a smart pointer that retains shared ownership of an object through a pointer. Support weak pointers and aliasing like C++ std::shared_ptr. Pointer to managed object is separated from pointer to control block conataining reference counter. `SharedPtr` contains 2 pointers or 2 pointers + length if managed object is slice). 
* `RcPtr`     is a smart pointer that retains shared ownership of an object through a pointer. Support weak pointers and only limited aliasing unlike `SharedPtr`. Managed object must be allcoated with control block (reference counter) in one continuous memory block. `RcPtr` contains only 1 pointer or 1 pointer + length if managed object is slice.
* `UniquePtr` is a smart pointer that owns and manages object through a pointer and disposes of that object when the `UniquePtr` goes out of scope.

`SharedPtr`, `RcPtr` and `UniquePtr` contains 3 template parameters:
* `_Type` type of managed object.
* `_DestructorType` type reprezenting attributes of destructor for managed object. 
  * This parameter is inferred from parameter `_Type` like this: `autoptr.common.DestructorType!_Type`.
* `_ControlType` type reprezenting control block. This parameter specify reference counting for smart pointer. 
  * Default value for `UniquePtr` is `autoptr.common.ControlBlock!void` which mean that there is no reference counting.
  * Default value for `SharedPtr` and `RefPtr` is `autoptr.common.ControlBlock!(int, int)` which mean that type of reference counter is `int` and  weak reference counter type is `int`. `autoptr.common.ControlBlock!(int, void)` disable weak reference counting.
  * If control block is `shared` then reference counting is atomic. Qualiffier `shared` is inferred from `_Type` for `_ControlType`. If `_Type` is `shared` then ControlBlock is `shared` too.
  
Smart pointers can be created with static methods `make` and `alloc`.
* `make` create smart pointer with stateless allocator (default `Mallocator`)
* `alloc` create smart pointer using allcoator with state. Allcoator is saved in control block.

Constructors of smart pointers never allcoate memory, only static methods `make` and `alloc` allcoate.
 
## Documentation
https://submada.github.io/autoptr

## Examples
```d

class Foo{
    int i;

    this(int i)pure nothrow @safe @nogc{
        this.i = i;
    }
}

class Bar : Foo{
    double d;

    this(int i, double d)pure nothrow @safe @nogc{
        super(i);
        this.d = d;
    }
}

class Zee : Bar{
    bool b;

    this(int i, double d, bool b)pure nothrow @safe @nogc{
        super(i, d);
        this.b = b;
    }

    ~this()nothrow @system{
    }
}

///`SharedPtr`:
unittest{
    ///simple:
    {
        SharedPtr!long a = SharedPtr!long.make(42);
        assert(a.useCount == 1);

        SharedPtr!(const long) b = a;
        assert(a.useCount == 2);

        SharedPtr!long.WeakType w = a.weak; //or WeakPtr!long
        assert(a.useCount == 2);
        assert(a.weakCount == 1);

        SharedPtr!long c = w.lock;
        assert(a.useCount == 3);
        assert(a.weakCount == 1);

        assert(*c == 42);
        assert(c.get == 42);
    }

    ///polymorphism and aliasing:
    {
        ///create SharedPtr
        SharedPtr!Foo foo = SharedPtr!Bar.make(42, 3.14);
        SharedPtr!Zee zee = SharedPtr!Zee.make(42, 3.14, false);

        ///dynamic cast:
        SharedPtr!Bar bar = dynCast!Bar(foo);
        assert(bar != null);
        assert(foo.useCount == 2);

        ///this doesnt work because Foo destructor attributes are more restrictive then Zee's:
        //SharedPtr!Foo x = zee;

        ///this does work:
        SharedPtr!(Foo, DestructorType!(Foo, Zee)) x = zee;
        assert(zee.useCount == 2);

        ///aliasing (shared ptr `d` share ref counting with `bar`):
        SharedPtr!double d = SharedPtr!double(bar, &bar.get.d);
        assert(d != null);
        assert(*d == 3.14);
        assert(foo.useCount == 3);
    }


    ///multi threading:
    {
        ///create SharedPtr with atomic ref counting
        SharedPtr!(shared Foo) foo = SharedPtr!(shared Bar).make(42, 3.14);

        ///this doesnt work:
        //foo.get.i += 1;

        import core.atomic : atomicFetchAdd;
        atomicFetchAdd(foo.get.i, 1);
        assert(foo.get.i == 43);


        ///creating `shared(SharedPtr)`:
        shared SharedPtr!(shared Bar) bar = share(dynCast!Bar(foo));

        ///`shared(SharedPtr)` is not lock free but `RcPtr` is lock free.
        static assert(typeof(bar).isLockFree == false);

        ///multi thread operations (`load`, `store`, `exchange` and `compareExchange`):
        SharedPtr!(shared Bar) bar2 = bar.load();
        assert(bar2 != null);
        assert(bar2.useCount == 3);

        SharedPtr!(shared Bar) bar3 = bar.exchange(null);
        assert(bar3 != null);
        assert(bar3.useCount == 3);
    }

    ///dynamic array:
    {
        import std.algorithm : all, equal;

        SharedPtr!(long[]) a = SharedPtr!(long[]).make(10, -1);
        assert(a.length == 10);
        assert(a.get.length == 10);
        assert(a.get.all!(x => x == -1));

        for(long i = 0; i < a.length; ++i){
            a.get[i] = i;
        }
        assert(a.get[] == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);

        ///aliasing:
        SharedPtr!long a6 = SharedPtr!long(a, &a.get[6]);
        assert(*a6 == a.get[6]);
    }
}

///`UniquePtr`:
unittest{
    ///simple:
    {
        SharedPtr!long a = SharedPtr!long.make(42);
        SharedPtr!(const long) b = a.move;
        assert(a == null);

        assert(*b == 42);
        assert(b.get == 42);
    }

    ///polymorphism:
    {
        ///create UniquePtr
        UniquePtr!Foo foo = UniquePtr!Bar.make(42, 3.14);
        UniquePtr!Zee zee = UniquePtr!Zee.make(42, 3.14, false);

        ///dynamic cast:
        UniquePtr!Bar bar = dynCastMove!Bar(foo);
        assert(foo == null);
        assert(bar != null);

        ///this doesnt work because Foo destructor attributes are more restrictive then Zee's:
        //UniquePtr!Foo x = zee.move;

        ///this does work:
        UniquePtr!(Foo, DestructorType!(Foo, Zee)) x = zee.move;
        assert(zee == null);
    }


    ///multi threading:
    {
        ///create SharedPtr with atomic ref counting
        UniquePtr!(shared Foo) foo = UniquePtr!(shared Bar).make(42, 3.14);

        ///this doesnt work:
        //foo.get.i += 1;

        import core.atomic : atomicFetchAdd;
        atomicFetchAdd(foo.get.i, 1);
        assert(foo.get.i == 43);


        ///creating `shared(UniquePtr)`:
        shared UniquePtr!(shared Bar) bar = share(dynCastMove!Bar(foo));

        ///`shared(UniquePtr)` is lock free.
        static assert(typeof(bar).isLockFree == true);

        ///multi thread operations (`store`, `exchange`):
        UniquePtr!(shared Bar) bar2 = bar.exchange(null);
    }

    ///dynamic array:
    {
        import std.algorithm : all, equal;

        UniquePtr!(long[]) a = UniquePtr!(long[]).make(10, -1);
        assert(a.length == 10);
        assert(a.get.length == 10);
        assert(a.get.all!(x => x == -1));

        for(long i = 0; i < a.length; ++i){
            a.get[i] = i;
        }
        assert(a.get[] == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
    }
}



///`RcPtr`:
unittest{
    ///simple:
    {
        RcPtr!long a = RcPtr!long.make(42);
        assert(a.useCount == 1);

        RcPtr!(const long) b = a;
        assert(a.useCount == 2);

        RcPtr!long.WeakType w = a.weak; //or WeakRcPtr!long
        assert(a.useCount == 2);
        assert(a.weakCount == 1);

        RcPtr!long c = w.lock;
        assert(a.useCount == 3);
        assert(a.weakCount == 1);

        assert(*c == 42);
        assert(c.get == 42);
    }

    ///polymorphism and aliasing:
    {
        ///create RcPtr
        RcPtr!Foo foo = RcPtr!Bar.make(42, 3.14);
        RcPtr!Zee zee = RcPtr!Zee.make(42, 3.14, false);

        ///dynamic cast:
        RcPtr!Bar bar = dynCast!Bar(foo);
        assert(bar != null);
        assert(foo.useCount == 2);

        ///this doesnt work because Foo destructor attributes are more restrictive then Zee's:
        //RcPtr!Foo x = zee;

        ///this does work:
        RcPtr!(Foo, DestructorType!(Foo, Zee)) x = zee;
        assert(zee.useCount == 2);
    }


    ///multi threading:
    {
        ///create RcPtr with atomic ref counting
        RcPtr!(shared Foo) foo = RcPtr!(shared Bar).make(42, 3.14);

        ///this doesnt work:
        //foo.get.i += 1;

        import core.atomic : atomicFetchAdd;
        atomicFetchAdd(foo.get.i, 1);
        assert(foo.get.i == 43);


        ///creating `shared(RcPtr)`:
        shared RcPtr!(shared Bar) bar = share(dynCast!Bar(foo));

        ///`shared(RcPtr)` is lock free (except `load` and `useCount`/`weakCount`).
        static assert(typeof(bar).isLockFree == true);

        ///multi thread operations (`load`, `store`, `exchange` and `compareExchange`):
        RcPtr!(shared Bar) bar2 = bar.load();
        assert(bar2 != null);
        assert(bar2.useCount == 3);

        RcPtr!(shared Bar) bar3 = bar.exchange(null);
        assert(bar3 != null);
        assert(bar3.useCount == 3);
    }

    ///dynamic array:
    {
        import std.algorithm : all, equal;

        RcPtr!(long[]) a = RcPtr!(long[]).make(10, -1);
        assert(a.length == 10);
        assert(a.get.length == 10);
        assert(a.get.all!(x => x == -1));

        for(long i = 0; i < a.length; ++i){
            a.get[i] = i;
        }
        assert(a.get[] == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
    }
}
```
