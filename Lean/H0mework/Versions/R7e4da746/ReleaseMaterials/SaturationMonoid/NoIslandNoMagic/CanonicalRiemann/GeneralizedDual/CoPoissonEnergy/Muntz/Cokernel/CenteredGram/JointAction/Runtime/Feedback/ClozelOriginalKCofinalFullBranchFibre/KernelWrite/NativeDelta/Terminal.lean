import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.Action
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKRInverseKernel
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.Generator.Resolvent.Gram
import H0mework.Versions.R7e4da746.Arithmetic.RiemannBandResponse.Class

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.Terminal
open BurnolPhysicalState
open scoped InnerProductSpace
namespace D
export OriginalKCombFirstFullSourceDynamics (input raw raw_successor raw_xi_source)
end D
namespace P
export OriginalKCombPhysicalAction (R)
end P
namespace Paid
export OriginalKCombCofinalRAction (original_R_direct parameter_rightQuarter)
export OriginalKCombCofinalInverseAction (original_R_injective)
end Paid
local instance terminalComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

private theorem original_R_fixed_zero (value : BurnolL2)
 (fixed : P.R observation nontrivial half value=value) : value=0 := by
 have direct : burnolDirectRightResolvent (observation.coordinate/2) value=value :=
  (Paid.original_R_direct observation nontrivial half value).symm.trans fixed
 have generated:=burnolDirectRightResolvent_gram (observation.coordinate/2) (observation.coordinate/2)
  (Paid.parameter_rightQuarter observation half) (Paid.parameter_rightQuarter observation half) value
 have coefficient : observation.coordinate/2+star (observation.coordinate/2)-1/2=
  ((observation.coordinate.re-1/2:ℝ):ℂ) := by
  change observation.coordinate/2+(starRingEnd ℂ) (observation.coordinate/2)-1/2=_
  rw [Complex.add_conj]
  norm_num
  ring
 rw [coefficient,direct,inner_self_eq_norm_sq_to_K] at generated
 have scalar:=congrArg Complex.re generated
 simp [Complex.mul_re,pow_two] at scalar
 have product : (observation.coordinate.re-1/2+2)*‖value‖^2=0 := by nlinarith [scalar]
 have mass : ‖value‖^2=0 := (mul_eq_zero.mp product).resolve_left (by linarith [half.down])
 exact norm_eq_zero.mp (sq_eq_zero_iff.mp mass)

/-- This consumes a fixed equation of the actual original cofinal source. -/
theorem actual_input_fixed_raw_zero
 (fixed : D.input observation nontrivial half depth (ordinal+1)=D.input observation nontrivial half depth ordinal) :
 D.raw observation nontrivial half depth ordinal=0 := by
 have rawFixed:=congrArg (fun pair : BurnolL2×BurnolL2=>pair.1+pair.2) fixed
 change D.raw observation nontrivial half depth (ordinal+1)=D.raw observation nontrivial half depth ordinal at rawFixed
 exact original_R_fixed_zero observation nontrivial half _
  ((D.raw_successor observation nontrivial half depth ordinal).symm.trans rawFixed)

include observation nontrivial half in
private theorem original_comb_ne_zero : (burnolPaCombApproximation 0:BurnolL2)≠0 := by
 intro zero
 have responseZero : burnolPaCombPhysicalResponse observation nontrivial half.down 0=0 := by
  apply Subtype.ext
  change P.R observation nontrivial half (burnolPaCombApproximation 0:BurnolL2)=0
  rw [zero,map_zero]
 have pairedZero : burnolPaCombPairedPhysicalResponse observation nontrivial half.down 0=0 := by
  simp only [burnolPaCombPairedPhysicalResponse,responseZero,map_zero,add_zero,smul_zero]
 have independent:=burnolPaCombPairedPhysicalResponse_Q_ne_zero observation nontrivial half.down 0
 exact independent (by rw [pairedZero,map_zero])

/-- Exact original Xi-order genealogy and R injectivity preserve the actual seed's nonzero state. -/
theorem actual_raw_ne_zero : D.raw observation nontrivial half depth ordinal≠0 := by
 have reflects : ∀ power:Nat,∀ value:BurnolL2,
  ((P.R observation nontrivial half).toLinearMap^power) value=0→value=0 := by
  intro power
  induction power with
  | zero => intro value zero; simpa only [pow_zero,Module.End.one_apply] using zero
  | succ power previous =>
   intro value zero
   rw [pow_succ',Module.End.mul_apply] at zero
   apply previous value
   exact Paid.original_R_injective observation nontrivial half (zero.trans (map_zero _).symm)
 intro zero
 rw [D.raw_xi_source] at zero
 exact original_comb_ne_zero observation nontrivial half (reflects _ _ zero)

/-- An actual source fixed branch terminates against the original independent physical response. -/
theorem actual_input_fixed_terminal
 (fixed : D.input observation nontrivial half depth (ordinal+1)=D.input observation nontrivial half depth ordinal) : False :=
 actual_raw_ne_zero observation nontrivial half depth ordinal
  (actual_input_fixed_raw_zero observation nontrivial half depth ordinal fixed)

end OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.Terminal
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
