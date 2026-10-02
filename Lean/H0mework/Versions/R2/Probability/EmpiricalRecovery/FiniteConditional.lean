import H0mework.Versions.R2.Probability.EmpiricalRecovery.FiniteNative

/-! Finite actual windows consume the complete original conditional distribution without changing its weights. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory.FiniteRecurrence.Native

open SourceGeneratedRuntimeHistoryProbability SourceConditionalTransfer

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {B : Type u} [AddCommGroup B] (read : process.State → B)
variable (windowBound : Nat) (runtime : LivingRuntimeState process) (actorBound : Nat)

omit [AddCommGroup B] in
theorem query_supported (index : Fin (actorBound + 1)) :
    query read windowBound runtime actorBound index ∈
      ((historyPMF actorBound).map (query read windowBound runtime actorBound)).support :=
  (PMF.mem_support_map_iff _ _ _).mpr ⟨index, by simp [historyPMF], rfl⟩

def conditional (index : Fin (actorBound + 1)) : PMF (Fin (actorBound + 1)) :=
  SourceConditionalHistory.conditional (historyPMF actorBound) (query read windowBound runtime actorBound)
    (query read windowBound runtime actorBound index) (query_supported read windowBound runtime actorBound index)

variable (coefficients : Fin (windowBound + 1) → ℤ)
variable (sourceLaw : (SourceOperationNative.observer process read).comp
    (SourceOperationNative.sourceAction process ^ (windowBound + 1)) =
      ∑ index : Fin (windowBound + 1), coefficients index •
        stageEvaluator (SourceOperationNative.sourceAction process) (SourceOperationNative.observer process read) index.val)

include sourceLaw

theorem conditional_is_original (index : Fin (actorBound + 1)) :
    conditional read windowBound runtime actorBound index =
      conditionalIndices read runtime actorBound (nextAtom read runtime actorBound index)
        (SourceConditionalRecovery.nextAtom_supported read runtime actorBound index) := by
  have sameFibre :
      {candidate | query read windowBound runtime actorBound candidate = query read windowBound runtime actorBound index} =
        {candidate | nextAtom read runtime actorBound candidate = nextAtom read runtime actorBound index} := by
    ext candidate
    exact (nextAtom_fibre_iff read windowBound coefficients sourceLaw runtime actorBound candidate index).symm
  unfold conditional conditionalIndices SourceConditionalHistory.conditional
  congr 1

end
end SourceGeneratedActionObservationHistory.FiniteRecurrence.Native
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
