import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Tactic.Tauto

/-! A complete natural multiplicity update generates the newly visible support without discarding repeated increments. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceSupportAction

noncomputable section
universe u v
variable {I : Type u} [DecidableEq I] {B : Type v} [AddCommGroup B]

def read (atom : I → B) (counts : I →₀ Nat) : B := counts.support.sum atom

def born (atom : I → B) (old increment : I →₀ Nat) : B :=
  (increment.support \ old.support).sum atom

theorem support_add (old increment : I →₀ Nat) :
    (old + increment).support = old.support ∪ increment.support := by
  ext index
  simp only [Finsupp.mem_support_iff, Finsupp.add_apply, Finset.mem_union]
  simp only [ne_eq, Nat.add_eq_zero_iff, not_and_or]

theorem read_update (atom : I → B) (old increment : I →₀ Nat) :
    read atom (old + increment) = read atom old + born atom old increment := by
  change (old + increment).support.sum atom = old.support.sum atom + (increment.support \ old.support).sum atom
  have same : old.support ∪ increment.support = old.support ∪ (increment.support \ old.support) := by
    ext index
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  rw [support_add, same]
  apply Finset.sum_union
  exact Finset.disjoint_left.mpr (fun _ left right => (Finset.mem_sdiff.mp right).2 left)

end
end SourceSupportAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
