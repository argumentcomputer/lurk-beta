use indexmap::IndexSet;

use crate::field::LurkField;

use super::ptr::Ptr;

pub struct Store<F: LurkField> {
    pub f_ptr_store: IndexSet<(F, Ptr)>,
    pub ptr2_store: IndexSet<(Ptr, Ptr)>,
    pub ptr3_store: IndexSet<(Ptr, Ptr, Ptr)>,
    pub ptr4_store: IndexSet<(Ptr, Ptr, Ptr, Ptr)>,
}
