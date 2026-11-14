import H0mework.Versions.R18f91d79.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCompletion
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.Terminal

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.RootRelation

open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
open SourceOperationScalarInventoryLift

attribute [local instance] relationGroups

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

private theorem actual_received_model_ne_zero (ordinal : Nat) :
    receivedModel observation nontrivial half depth ordinal ≠ 0 := by
  intro erased
  let read := modelReadback observation nontrivial half
  have source : read (receivedModel observation nontrivial half depth ordinal) =
      D.input observation nontrivial half depth ordinal :=
    (congrArg read (factor_source_class observation nontrivial half depth ordinal)).trans
      (model_readback_source observation nontrivial half _)
  have inputZero : D.input observation nontrivial half depth ordinal = 0 :=
    source.symm.trans ((congrArg read erased).trans (map_zero read))
  have rawZero := congrArg (fun pair : SourcePair => pair.1 + pair.2) inputZero
  exact KernelWrite.NativeDelta.Terminal.actual_raw_ne_zero observation nontrivial half depth ordinal
    (rawZero.trans (zero_add 0))

private theorem integral_line_injective {A B : Type} [AddCommGroup A] [AddCommGroup B] [Module ℂ B]
    (coordinate : A ≃ₗ[ℤ] ℤ) (read : A →ₗ[ℤ] B) (unit : B) (unitNonzero : unit ≠ 0)
    (source : ∀ value, read value = coordinate value • unit) : Function.Injective read := by
  intro left right equal
  have same : coordinate left • unit = coordinate right • unit :=
    (source left).symm.trans (equal.trans (source right))
  have zero : (coordinate left - coordinate right) • unit = 0 := by
    rw [sub_smul, same, sub_self]
  have scaled : ((coordinate left - coordinate right : ℤ) : ℂ) • unit = 0 :=
    (Int.cast_smul_eq_zsmul ℂ _ _).trans zero
  have coefficient := (smul_eq_zero.mp scaled).resolve_right unitNonzero
  exact coordinate.injective (sub_eq_zero.mp (Int.cast_eq_zero.mp coefficient))

/-- Original Xi and R injectivity make the whole installed source line faithful. -/
theorem actual_paid_factor_injective (ordinal : Nat) :
    Function.Injective (factor observation nontrivial half depth ordinal) :=
  integral_line_injective (actualPaidCompletion observation nontrivial half depth ordinal)
    (factor observation nontrivial half depth ordinal) (receivedModel observation nontrivial half depth ordinal)
    (actual_received_model_ne_zero observation nontrivial half depth ordinal)
    (actual_paid_completion_factor observation nontrivial half depth ordinal)

theorem actual_paid_evaluation_injective (ordinal : Nat) :
    Function.Injective ((sourceEvaluation observation nontrivial half depth ordinal).completionEvaluation
      (sourceSound observation nontrivial half depth ordinal)) := by
  intro left right equal
  apply actual_paid_factor_injective observation nontrivial half depth ordinal
  let grade := (D.packet observation nontrivial half depth ordinal).1
  exact congrArg (fun value => H.projection (sourceStep observation nontrivial half)
    (sourceBranches observation nontrivial half)
    (branchReadback observation nontrivial half (collapseLinear grade value))) equal

theorem actual_paid_kernel_zero (ordinal : Nat) :
    (sourceEvaluation observation nontrivial half depth ordinal).KernelResidual
      (sourceSound observation nontrivial half depth ordinal) = ⊥ :=
  LinearMap.ker_eq_bot.mpr (actual_paid_evaluation_injective observation nontrivial half depth ordinal)

end OriginalKCofinalFullBranchFibre.RootRelation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
