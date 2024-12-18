/-
Copyright (c) 2024 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Lean.Meta.Tactic.Simp.RegisterCommand

/-- The simpset `getElem_simps` is used by the tactic `get_elem_tactic_trivial`. -/
register_simp_attr getElem_simps

macro_rules | `(tactic| get_elem_tactic_trivial) => `(tactic| simp_all [getElem_simps]; done)
