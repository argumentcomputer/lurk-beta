use crate::field::LurkField;

use bellpepper_core::num::AllocatedNum;
use std::fmt::Debug;

/// Initialized map entry for a fixed `key` with
/// an allocated `value` computed at runtime.
pub(crate) struct CaseClause<'a, F: LurkField> {
    pub(crate) key: F,
    pub(crate) value: &'a AllocatedNum<F>,
}

impl<F: LurkField + Debug> Debug for CaseClause<'_, F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CaseClause")
            .field("key", &self.key)
            .field(
                "value",
                &format!(
                    "AllocatedNum {{ value: {:?}, variable: {:?} }}",
                    self.value.get_value(),
                    self.value.get_variable()
                ),
            )
            .finish()
    }
}
