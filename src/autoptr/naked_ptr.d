module autoptr.naked_ptr;



import autoptr.common;



template NakedPtr(
    _Type,
    _DestructorType = DestructorType!_Type,
    _ControlType = ControlTypeDeduction!(_Type, DefaultSharedControlBlock)
){


}
