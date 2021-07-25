# Autoptr
## C++-style smart pointers for D using `std.experimental.allocator`.
This library contains:
* `SharedPtr` is a smart pointer that retains shared ownership of an object through a pointer. Support aliasing like C++ std::shared_ptr. Pointer to managed object is separated from pointer to control block conataining reference counter. `SharedPtr` contains 2 pointers or 2 pointers + length if managed object is slice). 
* `RcPtr`     is a smart pointer that retains shared ownership of an object through a pointer. Support only limited aliasing unlike `SharedPtr`. Managed object must be allcoated with control block (reference counter) in one continuous memory block. `RcPtr` contains only 1 pointer or 1 pointer + length if managed object is slice.
* `UniquePtr` is a smart pointer that owns and manages object through a pointer and disposes of that object when the `UniquePtr` goes out of scope.

`SharedPtr`, `RcPtr` and 'UniquePtr' contains 3 template parameters:
* `_Type` type of managed object.
* `_DestructorType` type reprezenting attributes of destructor for managed object. 
  * This parameter is inferred from parameter `_Type` like this: `autoptr.common.DestructorType!_Type`.
* `_ControlType` type reprezenting control block. This parameter specify reference counting for smart pointer. 
  * Default value for `UniquePtr` is `ControlBlock!void` which mean that there is no reference counting.
  * Default value for `SharedPtr` and `RefPtr` is `ControlBlock!(int, int)` which mean that type of reference counter has type `int` and  weak reference counter has `int`. `ControlBlock!(int, void)` disable weak reference counting.
  * If control block is `shared` then reference counting is atomic. Qualiffier `shared` is inferred from `_Type` for `_ControlType`. If `_Type` is `shared` then ControlBlock is `shared` too.
## Documentation
https://submada.github.io/autoptr

## Example
```d

```
