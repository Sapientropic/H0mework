import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Recurrence.Gram
open BurnolPhysicalState
open scoped InnerProductSpace
open private original_R_fixed_zero from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.Terminal
namespace Paid
export OriginalKCombCofinalRAction (original_R_direct parameter_rightQuarter)
end Paid
local instance squareTerminalComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

/-- The original Gram excludes a two-step fixed vector through its actual positive and negative branches. -/
theorem original_R_square_fixed_zero (value : BurnolL2)
 (fixed : P.R observation nontrivial half (P.R observation nontrivial half value)=value) : value=0 := by
 have sumFixed : P.R observation nontrivial half (value+P.R observation nontrivial half value)=
  value+P.R observation nontrivial half value := by
  rw [map_add,fixed,add_comm]
 have sumZero := original_R_fixed_zero observation nontrivial half _ sumFixed
 have negative : P.R observation nontrivial half value=-value :=
  eq_neg_of_add_eq_zero_right sumZero
 have direct : burnolDirectRightResolvent (observation.coordinate/2) value=-value :=
  (Paid.original_R_direct observation nontrivial half value).symm.trans negative
 have generated := burnolDirectRightResolvent_gram (observation.coordinate/2) (observation.coordinate/2)
  (Paid.parameter_rightQuarter observation half) (Paid.parameter_rightQuarter observation half) value
 have coefficient : observation.coordinate/2+star (observation.coordinate/2)-1/2=
  ((observation.coordinate.re-1/2:ℝ):ℂ) := by
  change observation.coordinate/2+(starRingEnd ℂ) (observation.coordinate/2)-1/2=_
  rw [Complex.add_conj]
  norm_num
  ring
 have diagonal : inner ℂ (burnolDirectRightResolvent (observation.coordinate/2) value)
  (burnolDirectRightResolvent (observation.coordinate/2) value)=(‖value‖:ℂ)^2 := by
  rw [inner_self_eq_norm_sq_to_K,direct,norm_neg]
  rfl
 have pairing : inner ℂ value (burnolDirectRightResolvent (observation.coordinate/2) value)=
  -(‖value‖:ℂ)^2 := by
  rw [direct,inner_neg_right,inner_self_eq_norm_sq_to_K]
  rfl
 rw [coefficient,diagonal,pairing] at generated
 have scalar := congrArg Complex.re generated
 simp [Complex.mul_re,pow_two] at scalar
 have product : (observation.coordinate.re-5/2)*‖value‖^2=0 := by nlinarith [scalar]
 have mass : ‖value‖^2=0 := (mul_eq_zero.mp product).resolve_left
  (by linarith [observation.coordinate_re_lt_one])
 exact norm_eq_zero.mp (sq_eq_zero_iff.mp mass)

end OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Recurrence.Gram
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
