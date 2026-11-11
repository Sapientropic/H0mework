import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.FiniteRank.ProjectedReaction

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace FixedWindowFourierReaction.FullSchur
open Complex Filter MeasureTheory Set FixedWindowFourierReaction
open scoped InnerProductSpace Topology
local notation "T" => burnolRechartedTruncatedFourierOperator
local notation "Op" => H →L[ℂ] H
attribute [local instance 1100] Module.complexToReal NormedSpace.complexToReal

/-- The already generated finite reaction is the operator-norm square velocity. -/
theorem actual_square_velocity (radius:ℝ) (positive:0<radius) :
    HasDerivAt (fun r:ℝ => T r*T r) (rawReaction radius) radius := by
  have derivative := burnolRechartedTruncatedFourierOperator_hasDerivAt positive
  have square := derivative.mul derivative
  have effect (f:H) :
      ((burnolRadiusRechartedTruncatedFourierDerivative positive)*T radius+
        T radius*(burnolRadiusRechartedTruncatedFourierDerivative positive)) f=
          rawReaction radius f := by
    have actual := ((ContinuousLinearMap.apply ℂ H f).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
      radius square
    have integral := intervalIntegral.integral_hasDerivAt_right
      ((reaction_continuous f).intervalIntegrable radius radius)
      (reaction_continuous f).stronglyMeasurable.stronglyMeasurableAtFilter
      (reaction_continuous f).continuousAt
    have primitive := integral.const_add (T radius (T radius f))
    have exact : (fun r:ℝ => T r (T r f)) =ᶠ[𝓝 radius]
        (fun r:ℝ => T radius (T radius f)+∫ t:ℝ in radius..r,rawReaction t f) := by
      filter_upwards [lt_mem_nhds positive] with r rPositive
      have source := full_square_finite radius r positive rPositive f
      linear_combination (norm:=module) source
    have generated := primitive.congr_of_eventuallyEq exact
    exact actual.unique generated
  have generated :
      (burnolRadiusRechartedTruncatedFourierDerivative positive)*T radius+
        T radius*(burnolRadiusRechartedTruncatedFourierDerivative positive)=rawReaction radius :=
    ContinuousLinearMap.ext effect
  rw [generated] at square
  exact square

def sourceSchur (radius:ℝ) : Op := 1-T radius*T radius
def sourceInverse (radius:ℝ) : Op := Ring.inverse (sourceSchur radius)

private theorem source_T_bound (radius:ℝ) (positive:0<radius) : ‖T radius‖≤2*radius := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  rw [burnolRechartedTruncatedFourierOperator_of_pos positive]
  change ‖burnolRadiusRechartEquiv positive
    (burnolRadiusTruncatedFourier radius ((burnolRadiusRechartEquiv positive).symm f))‖≤_
  rw [(burnolRadiusRechartEquiv positive).norm_map]
  have bound := (burnolRadiusTruncatedFourier radius).le_opNorm
    ((burnolRadiusRechartEquiv positive).symm f)
  have actual := bound.trans (mul_le_mul_of_nonneg_right
    (burnolRadiusTruncatedFourier_opNorm_le positive) (norm_nonneg _))
  simpa only [(burnolRadiusRechartEquiv positive).symm.norm_map] using actual

theorem source_unit (radius:ℝ) (positive:0<radius) (short:2*radius<1) :
    IsUnit (sourceSchur radius) := by
  apply isUnit_one_sub_of_norm_lt_one
  have bound := norm_mul_le (T radius) (T radius)
  have paid := source_T_bound radius positive
  have nonnegative := norm_nonneg (T radius)
  have shorter : (2*radius)^2<1 := by nlinarith
  nlinarith

theorem actual_source_inverse (radius:ℝ) (positive:0<radius) (short:2*radius<1) :
    sourceSchur radius*sourceInverse radius=1 ∧
      sourceInverse radius*sourceSchur radius=1 :=
  ⟨Ring.mul_inverse_cancel _ (source_unit radius positive short),
    Ring.inverse_mul_cancel _ (source_unit radius positive short)⟩

/-- The complete inverse, including its constant channel, receives the actual reaction. -/
theorem actual_inverse_velocity (radius:ℝ) (positive:0<radius) (short:2*radius<1) :
    HasDerivAt sourceInverse
      (sourceInverse radius*rawReaction radius*sourceInverse radius) radius := by
  have square := actual_square_velocity radius positive
  have schur : HasDerivAt sourceSchur (-rawReaction radius) radius := by
    simpa only [sourceSchur,Pi.sub_apply,zero_sub] using!
      (hasDerivAt_const radius (1:Op)).sub square
  obtain ⟨unit,read⟩ := source_unit radius positive short
  have inverse := hasFDerivAt_ringInverse (𝕜:=ℝ) unit
  rw [read] at inverse
  have actual := inverse.comp_hasDerivAt radius schur
  have inverseRead : ((unit⁻¹:Opˣ):Op)=sourceInverse radius := by
    unfold sourceInverse
    rw [←read,Ring.inverse_unit]
  rw [inverseRead] at actual
  change HasDerivAt sourceInverse
    (-ContinuousLinearMap.mulLeftRight ℝ Op (sourceInverse radius) (sourceInverse radius)
      (-rawReaction radius)) radius at actual
  simpa only [neg_apply,ContinuousLinearMap.mulLeftRight_apply,
    neg_mul,mul_neg,neg_neg] using actual

theorem actual_inverse_source_velocity (radius:ℝ) (positive:0<radius) (short:2*radius<1)
    (source:H) :
    HasDerivAt (fun r:ℝ => sourceInverse r source)
      (sourceInverse radius (rawReaction radius (sourceInverse radius source))) radius := by
  have generated := ((ContinuousLinearMap.apply ℂ H source).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    radius (actual_inverse_velocity radius positive short)
  simpa only [ContinuousLinearMap.coe_restrictScalars',ContinuousLinearMap.apply_apply,
    mul_apply_eq_comp] using! generated

end FixedWindowFourierReaction.FullSchur
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
