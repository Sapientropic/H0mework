import Std.Tactic.BVDecide.Bitblast.BVExpr

/-!
# One shared AIG and expression cache for a vector of logical outputs

Each source expression extends the previous graph. Existing output references
are cast along that actual extension, and the returned expression cache feeds
the next compilation. Only the initial state starts from the empty graph.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat Std.Tactic.BVDecide

structure SharedLogicalGraphCurrent (count : Nat) where
  aig : AIG BVBit
  refs : AIG.RefVec aig count
  cache : BVExpr.Cache aig

def sharedLogicalGraphBoot : SharedLogicalGraphCurrent 0 :=
  ⟨AIG.empty, AIG.RefVec.empty, BVExpr.Cache.empty⟩

def sharedLogicalGraphAppend {count : Nat} (current : SharedLogicalGraphCurrent count)
    (expression : BVLogicalExpr) : SharedLogicalGraphCurrent (count + 1) :=
  let ⟨aig, refs, cache⟩ := current
  let compiled := BVLogicalExpr.bitblast.go aig expression cache
  { aig := compiled.result.val.aig
    refs := (refs.cast compiled.result.property).push compiled.result.val.ref
    cache := compiled.cache }

def sharedLogicalGraphAfter {width : Nat} (expressions : Vector BVLogicalExpr width) :
    (count : Nat) → count ≤ width → SharedLogicalGraphCurrent count
  | 0, _ => sharedLogicalGraphBoot
  | count + 1, bound => sharedLogicalGraphAppend
      (sharedLogicalGraphAfter expressions count (by omega)) expressions[count]

def compileSharedLogicalGraph {width : Nat} (expressions : Vector BVLogicalExpr width) :
    AIG.RefVecEntry BVBit width :=
  let compiled := sharedLogicalGraphAfter expressions width (Nat.le_refl _)
  ⟨compiled.aig, compiled.refs⟩

theorem sharedLogicalGraphAppend_cache_inv {count : Nat} (current : SharedLogicalGraphCurrent count)
    (expression : BVLogicalExpr) (assignment : BVExpr.Assignment)
    (invariant : BVExpr.Cache.Inv assignment current.aig current.cache) :
    BVExpr.Cache.Inv assignment (sharedLogicalGraphAppend current expression).aig
      (sharedLogicalGraphAppend current expression).cache :=
  BVLogicalExpr.bitblast.go_Inv_of_Inv expression current.aig assignment current.cache invariant

theorem sharedLogicalGraphAppend_last_denote {count : Nat} (current : SharedLogicalGraphCurrent count)
    (expression : BVLogicalExpr) (assignment : BVExpr.Assignment)
    (invariant : BVExpr.Cache.Inv assignment current.aig current.cache) :
    AIG.denote assignment.toAIGAssignment
      ⟨(sharedLogicalGraphAppend current expression).aig,
        (sharedLogicalGraphAppend current expression).refs.get count (by omega)⟩ =
      BVLogicalExpr.eval assignment expression := by
  cases current with
  | mk aig refs cache =>
    simp only [sharedLogicalGraphAppend, AIG.RefVec.get_push_ref_eq]
    exact BVLogicalExpr.bitblast.go_eval_eq_eval expression aig assignment cache invariant

theorem sharedLogicalGraphAppend_old_denote {count : Nat} (current : SharedLogicalGraphCurrent count)
    (expression : BVLogicalExpr) (assignment : BVExpr.Assignment) (index : Fin count) :
    AIG.denote assignment.toAIGAssignment
      ⟨(sharedLogicalGraphAppend current expression).aig,
        (sharedLogicalGraphAppend current expression).refs.get index.val (by omega)⟩ =
      AIG.denote assignment.toAIGAssignment ⟨current.aig, current.refs.get index.val index.isLt⟩ := by
  cases current with
  | mk aig refs cache =>
    simp only [sharedLogicalGraphAppend]
    rw [AIG.RefVec.get_push_ref_lt _ _ index.val index.isLt, AIG.RefVec.get_cast]
    exact AIG.denote.eq_of_isPrefix ⟨aig, refs.get index.val index.isLt⟩ _
      (BVLogicalExpr.bitblast.go_isPrefix_aig (expr := expression) cache)

theorem sharedLogicalGraphAfter_cache_inv {width : Nat} (expressions : Vector BVLogicalExpr width)
    (assignment : BVExpr.Assignment) (count : Nat) (bound : count ≤ width) :
    BVExpr.Cache.Inv assignment (sharedLogicalGraphAfter expressions count bound).aig
      (sharedLogicalGraphAfter expressions count bound).cache := by
  induction count with
  | zero => exact BVExpr.Cache.Inv_empty AIG.empty
  | succ count induction =>
    exact sharedLogicalGraphAppend_cache_inv _ _ assignment (induction (by omega))

theorem sharedLogicalGraphAfter_denote {width : Nat} (expressions : Vector BVLogicalExpr width)
    (assignment : BVExpr.Assignment) (count : Nat) (bound : count ≤ width) (index : Fin count) :
    AIG.denote assignment.toAIGAssignment
      ⟨(sharedLogicalGraphAfter expressions count bound).aig,
        (sharedLogicalGraphAfter expressions count bound).refs.get index.val index.isLt⟩ =
      BVLogicalExpr.eval assignment (expressions[index.val]'(by omega)) := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count induction =>
    by_cases last : index.val = count
    · simpa only [sharedLogicalGraphAfter, last] using
        sharedLogicalGraphAppend_last_denote
          (sharedLogicalGraphAfter expressions count (by omega)) expressions[count] assignment
          (sharedLogicalGraphAfter_cache_inv expressions assignment count (by omega))
    · have earlier : index.val < count := by omega
      rw [sharedLogicalGraphAfter,
        sharedLogicalGraphAppend_old_denote _ _ assignment (⟨index.val, earlier⟩ : Fin count)]
      exact induction (by omega) ⟨index.val, earlier⟩

theorem compileSharedLogicalGraph_denote {width : Nat} (expressions : Vector BVLogicalExpr width)
    (assignment : BVExpr.Assignment) (index : Fin width) :
    AIG.denote assignment.toAIGAssignment
      ⟨(compileSharedLogicalGraph expressions).aig,
        (compileSharedLogicalGraph expressions).vec.get index.val index.isLt⟩ =
      BVLogicalExpr.eval assignment expressions[index.val] :=
  sharedLogicalGraphAfter_denote expressions assignment width (Nat.le_refl _) index

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
