import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.FiniteRank.Source.FullSchur
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.FiniteRank.Source.ConstantFourierEuler

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace FixedWindowFourierReaction.CenteredSource
open Complex Filter MeasureTheory Set FixedWindowFourierReaction
open FixedWindowFourierReaction.FullSchur
open scoped InnerProductSpace Topology
attribute [local instance 1100] Module.complexToReal NormedSpace.complexToReal
local notation "T" => burnolRechartedTruncatedFourierOperator
local notation "Op" => H →L[ℂ] H

def sourceColumn (radius:ℝ) : H := (radius:ℂ) • Q (c radius)-p radius

def sourceReaction (radius:ℝ) : Op :=
  (radius:ℂ)⁻¹ • InnerProductSpace.rankOne ℂ (sourceColumn radius) (sourceColumn radius)-
    (radius:ℂ) • InnerProductSpace.rankOne ℂ (s radius) (s radius)

private theorem column_velocity (radius:ℝ) (positive:0<radius) :
    HasDerivAt p
      (Q (burnolRadiusRechartedTruncatedFourierDerivative positive e)) radius := by
  have evaluated := ((ContinuousLinearMap.apply ℂ H e).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    radius (burnolRechartedTruncatedFourierOperator_hasDerivAt positive)
  exact (Q.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt radius evaluated

private theorem ward_column (radius:ℝ) (positive:0<radius) :
    Q (burnolRadiusRechartedTruncatedFourierDerivative positive e)=
      (2:ℂ) • Q (c radius)-(radius:ℂ)⁻¹ • p radius := by
  have ward := congrArg Q (ConstantFourierEulerVelocity.constant_column_ward radius positive)
  simp only [map_add,map_smul] at ward
  change (radius:ℂ) • Q (burnolRadiusRechartedTruncatedFourierDerivative positive e)+p radius=
    (2*radius:ℂ) • Q (c radius) at ward
  have nonzero : (radius:ℂ)≠0 := Complex.ofReal_ne_zero.mpr positive.ne'
  have scaled := congrArg (fun x:H => (radius:ℂ)⁻¹ • x) ward
  simp only [smul_add,smul_smul,inv_mul_cancel₀ nonzero,one_smul] at scaled
  have rate : (radius:ℂ)⁻¹*(2*radius:ℂ)=2 := by field_simp
  rw [rate] at scaled
  linear_combination (norm:=module) scaled

/-- The complete mean correction produces the original source column; the odd channel remains. -/
theorem actual_centered_square_velocity (radius:ℝ) (positive:0<radius) :
    HasDerivAt centeredSquare (sourceReaction radius) radius := by
  let derivative:Op := burnolRadiusRechartedTruncatedFourierDerivative positive
  have dT := burnolRechartedTruncatedFourierOperator_hasDerivAt positive
  have dS := ((hasDerivAt_const radius Q).mul dT).mul (hasDerivAt_const radius Q)
  simp only [zero_mul,zero_add,mul_zero,add_zero] at dS
  change HasDerivAt centeredOperator (Q*derivative*Q) radius at dS
  have square := dS.mul dS
  change HasDerivAt centeredSquare
    ((Q*derivative*Q)*centeredOperator radius+centeredOperator radius*(Q*derivative*Q)) radius at square
  have effect (value:H) :
      (((Q*derivative*Q)*centeredOperator radius+centeredOperator radius*(Q*derivative*Q)) value)=
        sourceReaction radius value := by
    have actual := ((ContinuousLinearMap.apply ℂ H value).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
      radius square
    have dFull := ((ContinuousLinearMap.apply ℂ H (Q value)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
      radius (actual_square_velocity radius positive)
    have dProjected := (Q.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt radius dFull
    have dp := column_velocity radius positive
    have dPair := dp.inner ℂ (hasDerivAt_const radius value)
    simp only [inner_zero_right,zero_add] at dPair
    have dRank := dPair.smul dp
    have dComplete := dProjected.sub (dRank.const_smul (1/2:ℂ))
    have same : (fun r:ℝ => centeredSquare r value) =ᶠ[𝓝 radius]
        (fun r:ℝ => Q (T r (T r (Q value)))-
          (1/2:ℂ) • (inner ℂ (p r) value • p r)) := by
      filter_upwards [lt_mem_nhds positive] with r rPositive
      have generated := congrArg (fun operator:Op => operator value) (actual_centered_square r rPositive)
      simpa only [sub_apply,ContinuousLinearMap.comp_apply,smul_apply,InnerProductSpace.rankOne_apply] using generated
    have generated := dComplete.congr_of_eventuallyEq same
    have equality := actual.unique generated
    change ((Q*derivative*Q)*centeredOperator radius+centeredOperator radius*(Q*derivative*Q)) value=
      Q (rawReaction radius (Q value))-
      (1/2:ℂ) • (inner ℂ (p radius) value • Q (derivative e)+
        inner ℂ (Q (derivative e)) value • p radius) at equality
    rw [equality,projected_reaction]
    change centeredReaction radius value-(1/2:ℂ) •
      (inner ℂ (p radius) value • Q (derivative e)+
        inner ℂ (Q (derivative e)) value • p radius)=sourceReaction radius value
    have ward := ward_column radius positive
    change Q (derivative e)=_ at ward
    rw [ward]
    simp only [sourceReaction,sourceColumn,centeredReaction,smul_apply,sub_apply,
      InnerProductSpace.rankOne_apply,inner_sub_left,inner_smul_left,sine_mean_zero,
      smul_sub,smul_add,smul_smul]
    simp only [map_inv₀,map_ofNat,Complex.conj_ofReal]
    have nonzero : (radius:ℂ)≠0 := Complex.ofReal_ne_zero.mpr positive.ne'
    field_simp
    module
  have generated := ContinuousLinearMap.ext effect
  rw [generated] at square
  exact square

/-- The original even carrier eliminates the odd source reaction by its actual parity. -/
theorem actual_even_source_reaction (radius:ℝ) (value:H)
    (even:reflectRestricted 1 value=value) :
    sourceReaction radius value=(radius:ℂ)⁻¹ •
      (inner ℂ (sourceColumn radius) value • sourceColumn radius) := by
  simp only [sourceReaction,sub_apply,smul_apply,InnerProductSpace.rankOne_apply,
    sine_even_pair_zero radius value even,zero_smul,smul_zero,sub_zero]

end FixedWindowFourierReaction.CenteredSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
