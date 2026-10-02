import H0mework.Versions.R2.Probability.Empirical.ConditionalAtom

/-! Complete conditional source weights compute the already existing transfer on every reachable next atom. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalTransfer

open SourceGeneratedEmpiricalHilbert SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedScalarCofinalTopology.NativeProbability
open scoped Classical

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {B : Type u} [AddCommGroup B] (read : process.State → B)
variable (runtime : LivingRuntimeState process) (bound : Nat)

abbrev conditionalIndices (atom : Field read) (supported : atom ∈ (fieldPMF read runtime.tick.next bound).support) :
    PMF (Fin (bound + 1)) :=
  SourceConditionalHistory.conditional (historyPMF bound) (nextAtom read runtime bound) atom (by
    change atom ∈ ((historyPMF bound).map (nextAtom read runtime bound)).support
    rw [← nextPMF_from_indices]
    exact supported)

theorem conditionalIndices_support_iff (atom : Field read)
    (supported : atom ∈ (fieldPMF read runtime.tick.next bound).support) (index : Fin (bound + 1)) :
    index ∈ (conditionalIndices read runtime bound atom supported).support ↔
      nextAtom read runtime bound index = atom := by
  rw [SourceConditionalHistory.conditional_support]
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, historyPMF, PMF.mem_support_uniformOfFintype, and_true]

theorem weighted_indices (atom : Field read)
    (supported : atom ∈ (fieldPMF read runtime.tick.next bound).support) (index : Fin (bound + 1)) :
    fieldPMF read runtime.tick.next bound atom * conditionalIndices read runtime bound atom supported index =
      if nextAtom read runtime bound index = atom then historyPMF bound index else 0 := by
  exact (congrArg (fun probability : PMF (Field read) =>
      probability atom * conditionalIndices read runtime bound atom supported index)
    (nextPMF_from_indices read runtime bound)).trans
      (SourceConditionalHistory.weighted_conditional (historyPMF bound) (nextAtom read runtime bound) atom _ index)

def conditionalValue (value : Space read runtime bound) (atom : Field read)
    (supported : atom ∈ (fieldPMF read runtime.tick.next bound).support) : ℂ :=
  ∑ index : Fin (bound + 1), (conditionalIndices read runtime bound atom supported index).toReal •
    value (fieldSample read runtime bound index)

theorem conditionalValue_weighted (value : Space read runtime bound) (atom : Field read)
    (supported : atom ∈ (fieldPMF read runtime.tick.next bound).support) :
    (fieldPMF read runtime.tick.next bound atom).toReal • conditionalValue read runtime bound value atom supported =
      ∑ index : Fin (bound + 1), (historyPMF bound index).toReal •
        (if nextAtom read runtime bound index = atom then value (fieldSample read runtime bound index) else 0) := by
  rw [conditionalValue, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [smul_smul, ← ENNReal.toReal_mul, weighted_indices]
  by_cases same : nextAtom read runtime bound index = atom <;> simp [same]

theorem transfer_at_atom (value : Space read runtime bound) (atom : Field read)
    (supported : atom ∈ (fieldPMF read runtime.tick.next bound).support) :
    transfer read runtime bound value atom = conditionalValue read runtime bound value atom supported := by
  have nonzero : (fieldPMF read runtime.tick.next bound atom).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨supported, (fieldPMF read runtime.tick.next bound).apply_ne_top atom⟩
  exact (smul_right_injective (M := ℂ) nonzero)
    ((transfer_atom_weighted read runtime bound value atom).trans
      (conditionalValue_weighted read runtime bound value atom supported).symm)

end
end SourceConditionalTransfer
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
