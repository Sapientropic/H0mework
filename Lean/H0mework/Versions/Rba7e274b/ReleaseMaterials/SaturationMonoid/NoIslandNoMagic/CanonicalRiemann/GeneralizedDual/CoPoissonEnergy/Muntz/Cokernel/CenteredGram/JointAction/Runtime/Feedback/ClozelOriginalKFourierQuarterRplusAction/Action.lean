import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPositionQuarterFTCAction.Consumer
import H0mework.Versions.V2.Arithmetic.RiemannNativeCurrent.UnitResponseRadius
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFourierQuarterRplusAction
open Complex MeasureTheory Set Filter SourceGeneratedHilbertCokernel
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
namespace Paid
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.FiniteMobiusResolventFlux (actualMean Rplus RplusIntegrand Rplus_integrable)
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalJointFluxSource (actual_mean_source_integral actual_mean_dilation_source source_weight_mean_phase)
end Paid
local notation "q" => (1/4:ℝ)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

/-- Literal compact support is consumed in the original positive Rplus integral, before any price readout. -/
theorem actual_compact_Rplus_mean_action (z : ℂ) (right : 1/4<z.re) (material : BurnolL2)
 (supported : originalPhysicalCutoff q material=material) :
 Paid.actualMean (Paid.Rplus z material)=-Paid.actualMean material/z := by
 have sourceIntegrable:=Paid.Rplus_integrable z right material
 have decay : (-z).re<0 := by simp only [Complex.neg_re];linarith
 have source : Paid.actualMean (Paid.Rplus z material)=
   -(∫ tau : ℝ in Ioi 0,Complex.exp (-z*(tau:ℂ))*Paid.actualMean material) := by
  unfold Paid.Rplus
  rw [map_neg,←Paid.actualMean.integral_comp_comm sourceIntegrable]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro tau positive
  unfold Paid.RplusIntegrand
  dsimp only
  rw [map_smul]
  change positiveMellinQuarterRightResolventWeight z tau*
    Paid.actualMean (burnolMultiplicativeDilation (tau/2) material)=_
  rw [OriginalKPositionQuarterFTCAction.actual_compact_positive_mean material supported (tau/2)
    (by change 0<tau at positive;linarith),←mul_assoc]
  rw [show -(tau/2)/2=-tau/4 by ring,Paid.source_weight_mean_phase]
 rw [source,integral_mul_const,integral_exp_mul_complex_Ioi decay 0]
 simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero]
 ring


end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFourierQuarterRplusAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
