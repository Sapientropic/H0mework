import Lean
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFourierKernelDependentRAction.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFourierKernelDependentRAction
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





def actualResonantIntegrand (z : ℂ) (source : BurnolL2) (time : ℝ) : BurnolL2 :=
 time • burnolDirectRightResolventIntegrand z source time

def actualResonantField (z : ℂ) (source : BurnolL2) : BurnolL2 :=
 ∫ time : ℝ in Ioi 0, actualResonantIntegrand z source time

/-- The literal time price is integrable from the original unitary source orbit and its own admitted decay. -/
theorem actual_resonant_integrable (z : ℂ) (right : 1/4<z.re) (source : BurnolL2) :
 IntegrableOn (actualResonantIntegrand z source) (Ioi 0) := by
 let k : ℝ:=z.re-1/4
 have positive : 0<k:=sub_pos.mpr right
 let bound : ℝ→ℝ:=fun time=>(2/k)*Real.exp (-(k/2)*time)*‖source‖
 have integrable : IntegrableOn bound (Ioi 0) :=
  ((exp_neg_integrableOn_Ioi 0 (by positivity : 0<k/2)).const_mul (2/k)).mul_const ‖source‖
 have continuous : Continuous (actualResonantIntegrand z source) := by
  unfold actualResonantIntegrand burnolDirectRightResolventIntegrand
  exact continuous_id.smul ((positiveMellinQuarterRightResolventWeight_continuous z).smul
   ((burnolMultiplicativeDilation_stronglyContinuous source).comp (by fun_prop)))
 apply Integrable.mono' integrable.norm continuous.aestronglyMeasurable.restrict
 filter_upwards [ae_restrict_mem measurableSet_Ioi] with time ht
 change 0<time at ht
 have exactNorm : ‖actualResonantIntegrand z source time‖=
   time*Real.exp (-k*time)*‖source‖ := by
  simp only [actualResonantIntegrand,norm_smul,Real.norm_eq_abs,abs_of_pos ht,
   burnolDirectRightResolventIntegrand,norm_smul,
   (burnolMultiplicativeDilation (-time/2)).norm_map,
   norm_positiveMellinQuarterRightResolventWeight,k]
  ring
 rw [exactNorm]
 have x:=Real.add_one_le_exp ((k/2)*time)
 have price : (k/2)*time≤Real.exp ((k/2)*time) :=by linarith
 have generated:=mul_le_mul_of_nonneg_right price (Real.exp_nonneg (-k*time))
 rw [←Real.exp_add] at generated
 rw [show (k/2)*time+-k*time=-(k/2)*time by ring] at generated
 have division : time*Real.exp (-k*time)≤(2/k)*Real.exp (-(k/2)*time) :=by
  have paid : (time*Real.exp (-k*time))*(k/2)≤Real.exp (-(k/2)*time) :=by
   nlinarith only [generated]
  have price:=(le_div_iff₀ (by positivity : 0<k/2)).mpr paid
  have coefficient : (k/2)⁻¹=2/k:=by field_simp
  rw [div_eq_mul_inv,coefficient] at price
  simpa only [mul_comm] using price
 have boundNonnegative : 0≤bound time:=by dsimp only [bound];positivity
 rw [Real.norm_of_nonneg boundNonnegative]
 exact mul_le_mul_of_nonneg_right division (norm_nonneg source)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFourierKernelDependentRAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
