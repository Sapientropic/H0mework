import H0mework.Versions.R18f91d79.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Payment.Completion
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.Consumer

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.RootRelation

open SourceOperationScalarInventoryLift SourceOperationPaidRelations

attribute [local instance] relationGroups

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

private abbrev paidTrace (ordinal : Nat) :=
  (Own.runtimeCurrent (sourceRoot observation nontrivial half depth ordinal)
    (sourceCurrent observation nontrivial half depth ordinal)
    (sourceReader observation nontrivial half depth ordinal)
    (sourceRuntime observation nontrivial half depth ordinal)).2

/-- The actual R calculation's installed relation completion has the original endpoint as its unit. -/
def actualPaidCompletion (ordinal : Nat) :
    SourceCompletion observation nontrivial half depth ordinal ≃ₗ[ℤ] ℤ :=
  paidCompletionEquiv (.zero (sourceRuntime observation nontrivial half depth ordinal).emittedOccurrence)
    (paidTrace observation nontrivial half depth ordinal)

theorem actual_paid_completion_source_unit (ordinal : Nat) :
    actualPaidCompletion observation nontrivial half depth ordinal
      (sourceClass observation nontrivial half depth ordinal) = 1 := by
  let word := sourceGenerator observation nontrivial half depth ordinal
  have unit : coefficientSum word.val = 1 := by
    change coefficientSum (Finsupp.single _ 1) = 1
    simp only [coefficientSum, Finsupp.linearCombination_single, one_smul]
  exact (paid_completion_source (.zero (sourceRuntime observation nontrivial half depth ordinal).emittedOccurrence)
    (paidTrace observation nontrivial half depth ordinal) word).trans unit

private theorem read_from_integral_unit {A B : Type} [AddCommGroup A] [AddCommGroup B]
    (completion : A ≃ₗ[ℤ] ℤ) (read : A →ₗ[ℤ] B) (source : A)
    (unit : completion source = 1) (word : A) :
    read word = completion word • read source := by
  have same : word = completion word • source := by
    apply completion.injective
    rw [map_smul, unit, smul_eq_mul, mul_one]
  exact (congrArg read same).trans (map_smul read (completion word) source)

theorem actual_paid_completion_factor (ordinal : Nat)
    (word : SourceCompletion observation nontrivial half depth ordinal) :
    factor observation nontrivial half depth ordinal word =
      actualPaidCompletion observation nontrivial half depth ordinal word •
        receivedModel observation nontrivial half depth ordinal :=
  read_from_integral_unit (actualPaidCompletion observation nontrivial half depth ordinal)
    (factor observation nontrivial half depth ordinal)
    (sourceClass observation nontrivial half depth ordinal)
    (actual_paid_completion_source_unit observation nontrivial half depth ordinal) word

theorem actual_paid_model_next (ordinal : Nat) (coefficient : ℤ) :
    H.modelAction (sourceStep observation nontrivial half) (sourceBranches observation nontrivial half)
      (factor observation nontrivial half depth ordinal
        ((actualPaidCompletion observation nontrivial half depth ordinal).symm coefficient)) =
      factor observation nontrivial half depth (ordinal+1)
        ((actualPaidCompletion observation nontrivial half depth (ordinal+1)).symm coefficient) := by
  have chargeRead (index : Nat) :
      factor observation nontrivial half depth index
          ((actualPaidCompletion observation nontrivial half depth index).symm coefficient) =
        coefficient • receivedModel observation nontrivial half depth index := by
    let completion := actualPaidCompletion observation nontrivial half depth index
    have read := actual_paid_completion_factor observation nontrivial half depth index (completion.symm coefficient)
    exact read.trans (congrArg (fun charge : ℤ => charge • receivedModel observation nontrivial half depth index)
      (completion.apply_symm_apply coefficient))
  let action := H.modelAction (sourceStep observation nontrivial half) (sourceBranches observation nontrivial half)
  let current := receivedModel observation nontrivial half depth ordinal
  exact (congrArg action (chargeRead ordinal)).trans
    ((map_zsmul action coefficient current).trans
      ((congrArg (fun value => coefficient • value) (received_model_next observation nontrivial half depth ordinal)).trans
        (chargeRead (ordinal+1)).symm))

end OriginalKCofinalFullBranchFibre.RootRelation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
