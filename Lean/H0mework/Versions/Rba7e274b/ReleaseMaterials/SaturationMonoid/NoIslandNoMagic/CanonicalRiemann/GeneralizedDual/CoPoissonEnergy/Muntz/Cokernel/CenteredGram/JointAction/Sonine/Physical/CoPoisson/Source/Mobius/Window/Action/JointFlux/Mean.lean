import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.FourierPrimitiveAction.Consumer
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ResolventFlux.ReverseRank
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalJointFluxSource
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology BigOperators
namespace Paid
export FiniteMobiusResolventFlux (M actualMean coefficient sigma box cutoff cutoff_read box_read fullS fullPullback Rplus Rplus_sub Rplus_smul actualFlux reverseFlux defectFlux tailFlux meanFlux outerCut actual_M_R_action fullS_Rplus cutoff_Rplus_rank interiorBase reverseRankSource exteriorMoment)
end Paid

theorem actual_mean_source_integral (value : BurnolL2) :
    Paid.actualMean value=(2:ℂ)*(∫ x : ℝ in symmetricInterval (1/4:ℝ),value x) := by
  change (‖intervalConstant (1/4:ℝ)‖^2:ℂ)⁻¹*inner ℂ (intervalConstant (1/4:ℝ)) (burnolRadiusRestriction (1/4:ℝ) value)=_
  rw [burnolIntervalConstant_norm_sq (by norm_num : (0:ℝ)<1/4)]
  norm_num
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [intervalConstant_coeFn (1/4:ℝ),LpToLpRestrictCLM_coeFn ℂ (symmetricInterval (1/4:ℝ)) value] with x constant restricted
  change burnolRadiusRestriction (1/4:ℝ) value x=value x at restricted
  rw [constant,restricted,RCLike.inner_apply]
  simp only [starRingEnd_apply,star_one,mul_one]

 theorem actual_mean_dilation_source (shift : ℝ) (value : BurnolL2) :
    Paid.actualMean (burnolMultiplicativeDilation shift value)=
      (2:ℂ)*(Real.exp (-shift/2):ℂ)*(∫ x : ℝ in symmetricInterval ((1/4:ℝ)*Real.exp shift),value x) := by
  rw [actual_mean_source_integral]
  have raw : (∫ x : ℝ in symmetricInterval (1/4:ℝ),burnolMultiplicativeDilation shift value x)=
      (Real.exp (shift/2):ℂ)*(∫ x : ℝ in symmetricInterval (1/4:ℝ),value (Real.exp shift*x)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (burnolMultiplicativeDilation_coeFn shift value)] with x source
    exact source
  rw [raw]
  let profile : ℝ→ℂ := (symmetricInterval ((1/4:ℝ)*Real.exp shift)).indicator (value:ℝ→ℂ)
  have change : (∫ x : ℝ in symmetricInterval (1/4:ℝ),value (Real.exp shift*x))=
      (Real.exp shift)⁻¹ • (∫ x : ℝ in symmetricInterval ((1/4:ℝ)*Real.exp shift),value x) := by
    have changed := Measure.integral_comp_mul_left profile (Real.exp shift)
    rw [abs_of_pos (inv_pos.mpr (Real.exp_pos _))] at changed
    change (∫ x : ℝ,profile (Real.exp shift*x))=(Real.exp shift)⁻¹ •
      (∫ x : ℝ,(symmetricInterval ((1/4:ℝ)*Real.exp shift)).indicator (value:ℝ→ℂ) x) at changed
    rw [integral_indicator (measurableSet_symmetricInterval _)] at changed
    have mapped : (∫ x : ℝ,profile (Real.exp shift*x))=
        ∫ x : ℝ in symmetricInterval (1/4:ℝ),value (Real.exp shift*x) := by
      rw [← integral_indicator (measurableSet_symmetricInterval _)]
      apply integral_congr_ae
      filter_upwards [] with x
      have member : Real.exp shift*x∈symmetricInterval ((1/4:ℝ)*Real.exp shift) ↔ x∈symmetricInterval (1/4:ℝ) := by
        simp only [symmetricInterval,mem_Icc]
        have positive := Real.exp_pos shift
        constructor
        · intro h
          constructor <;> nlinarith [h.1,h.2]
        · intro h
          constructor <;> nlinarith [h.1,h.2]
      unfold profile
      by_cases inside : x∈symmetricInterval (1/4:ℝ)
      · rw [indicator_of_mem inside,indicator_of_mem (member.mpr inside)]
      · rw [indicator_of_notMem inside,indicator_of_notMem (fun h=>inside (member.mp h))]
    rw [mapped] at changed
    exact changed
  rw [change]
  simp only [Complex.real_smul,Complex.ofReal_inv]
  have phase : (Real.exp (shift/2):ℂ)*(Real.exp shift:ℂ)⁻¹=(Real.exp (-shift/2):ℂ) := by
    rw [← Complex.ofReal_inv,← Complex.ofReal_mul,← Real.exp_neg,← Real.exp_add]
    congr 2
    ring
  calc
    _=(2:ℂ)*((Real.exp (shift/2):ℂ)*(Real.exp shift:ℂ)⁻¹)*(∫ x : ℝ in symmetricInterval ((1/4:ℝ)*Real.exp shift),value x) := by ring
    _=_ := by rw [phase]
end OriginalJointFluxSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
