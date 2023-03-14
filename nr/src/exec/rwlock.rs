use builtin_macros::verus_old_todo_no_ghost_blocks;


use crate::pervasive::prelude::*;
use crate::pervasive::cell::{PCell, PermissionOpt};
use crate::pervasive::map::Map;
use crate::pervasive::option::Option;
use crate::pervasive::vec::Vec;
use crate::pervasive::atomic_ghost::*;
use crate::pervasive::struct_with_invariants;

use crate::spec::cyclicbuffer::CyclicBuffer;
use crate::spec::flat_combiner::FlatCombiner;
use crate::spec::types::*;
use crate::spec::unbounded_log::UnboundedLog;



verus_old_todo_no_ghost_blocks! {

// TODO:
pub struct RwLock<D>
{
    foo: Option<D>
}


}