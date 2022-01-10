/**
    Imports all modules.

    `autoptr.shared_ptr` : `autoptr.shared_ptr.SharedPtr`

    `autoptr.rc_ptr` : `autoptr.rc_ptr.RcPtr`

    `autoptr.intrusive_ptr` : `autoptr.intrusive_ptr.IntrusivePtr`

    `autoptr.unique_ptr` : `autoptr.unique_ptr.UniquePtr`

    `autoptr.common`
*/
module autoptr;

public{
    import autoptr.common;
    import autoptr.shared_ptr;
    import autoptr.intrusive_ptr;
    import autoptr.rc_ptr;
    import autoptr.unique_ptr;
}
