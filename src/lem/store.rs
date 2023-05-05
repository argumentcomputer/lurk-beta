use indexmap::IndexSet;

use super::ptr::Ptr;

pub struct Store {
    pub ptr2_store: IndexSet<(Ptr, Ptr)>,
    pub ptr3_store: IndexSet<(Ptr, Ptr, Ptr)>,
    pub ptr4_store: IndexSet<(Ptr, Ptr, Ptr, Ptr)>,
}
