import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.JointFlux.Forward
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalJointFluxSource
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology BigOperators

theorem source_weight_mean_phase (z : ℂ) (tau : ℝ) :
    positiveMellinQuarterRightResolventWeight z tau*(Real.exp (-tau/4):ℂ)=Complex.exp (-z*(tau:ℂ)) := by
  unfold positiveMellinQuarterRightResolventWeight
  rw [Complex.ofReal_exp,← Complex.exp_add]
  congr 1
  push_cast
  ring

def generatedMeanCoefficient (z : ℂ) (value : BurnolL2) : ℂ :=
  Paid.sigma*(-Paid.actualMean value/z-Paid.actualMean (burnolDirectRightResolvent z value))

theorem source_mean_R_read (z : ℂ) (right : 1/4<z.re) (value : BurnolL2) :
    Paid.actualMean (burnolDirectRightResolvent z value)=
      -(∫ tau : ℝ in Ioi 0,positiveMellinQuarterRightResolventWeight z tau*
        Paid.actualMean (burnolMultiplicativeDilation (-tau/2) value)) := by
  unfold burnolDirectRightResolvent
  rw [map_neg,← Paid.actualMean.integral_comp_comm (burnolDirectRightResolventIntegrand_integrableOn z right value)]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro tau _
  unfold burnolDirectRightResolventIntegrand
  dsimp only
  rw [map_smul]
  rfl

 theorem generated_mean_response_source (z : ℂ) (right : 1/4<z.re) (value : BurnolL2) :
    sourceMeanResponse z value=generatedMeanCoefficient z value • Paid.box 4 := by
  let embed : ℂ→L[ℂ]BurnolL2:=ContinuousLinearMap.toSpanSingleton ℂ (Paid.box 4)
  have decay : (-z).re<0 := by simp only [Complex.neg_re];linarith
  have first : IntegrableOn (fun tau:ℝ=>Complex.exp (-z*(tau:ℂ))*Paid.actualMean value) (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi decay 0).mul_const _
  have second : IntegrableOn (fun tau:ℝ=>positiveMellinQuarterRightResolventWeight z tau*
      Paid.actualMean (burnolMultiplicativeDilation (-tau/2) value)) (Ioi 0) := by
    apply (Paid.actualMean.integrable_comp (burnolDirectRightResolventIntegrand_integrableOn z right value)).congr
    filter_upwards [] with tau
    unfold burnolDirectRightResolventIntegrand
    rw [map_smul]
    rfl
  have raw : sourceMeanResponseIntegrand z value=fun tau:ℝ=>embed
    (Paid.sigma*(Complex.exp (-z*(tau:ℂ))*Paid.actualMean value-
      positiveMellinQuarterRightResolventWeight z tau*Paid.actualMean (burnolMultiplicativeDilation (-tau/2) value))) := by
    funext tau
    unfold sourceMeanResponseIntegrand
    rw [source_mean_difference_actual,smul_smul]
    change _=(Paid.sigma*(Complex.exp (-z*(tau:ℂ))*Paid.actualMean value-
      positiveMellinQuarterRightResolventWeight z tau*Paid.actualMean (burnolMultiplicativeDilation (-tau/2) value))) • Paid.box 4
    have phase:=source_weight_mean_phase z tau
    rw [show -tau/2/2= -tau/4 by ring]
    rw [← phase]
    module
  unfold sourceMeanResponse
  rw [raw]
  dsimp only
  have moved := embed.integral_comp_comm ((first.sub second).const_mul Paid.sigma)
  dsimp only [Pi.sub_apply] at moved
  rw [moved]
  unfold embed
  rw [ContinuousLinearMap.toSpanSingleton_apply,integral_const_mul,integral_sub first second,integral_mul_const]
  rw [integral_exp_mul_complex_Ioi decay 0]
  simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero,neg_div_neg_eq]
  have mean:=source_mean_R_read z right value
  unfold generatedMeanCoefficient
  rw [mean]
  module
end OriginalJointFluxSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
