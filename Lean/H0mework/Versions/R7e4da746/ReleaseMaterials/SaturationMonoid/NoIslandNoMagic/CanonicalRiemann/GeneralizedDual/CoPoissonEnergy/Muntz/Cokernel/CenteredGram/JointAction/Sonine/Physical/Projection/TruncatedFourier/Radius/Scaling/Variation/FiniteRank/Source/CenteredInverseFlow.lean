import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.FiniteRank.Source.CenteredInverse

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace FixedWindowFourierReaction.CenteredInverseFlow
open Complex Filter MeasureTheory Set FixedWindowFourierReaction OriginalRieszSource
open FixedWindowFourierReaction.CenteredSource FixedWindowFourierReaction.CenteredInverse
open scoped InnerProductSpace Topology
attribute [local instance 1100] Module.complexToReal NormedSpace.complexToReal
local notation "q" => (1/4:ℝ)
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "Hq" => BurnolQuarterIntervalL2
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "B" => burnolMeanZeroOneMinusSquare
local notation "BI" => burnolMeanZeroBlockInverse
local notation "Op" => H →L[ℂ] H
local notation "OpM" => M →L[ℂ] M
local instance : CompleteSpace M :=
  IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete

private theorem Q_embed (value:M) : Q (embed value)=embed value := by
  rw [←embed_read,read_embed]

private theorem read_Q (value:H) : read (Q value)=read value := by
  rw [←embed_read,read_embed]

private theorem quarter_centered (value:H) :
    centeredOperator q value=embed (S (read value)) := by
  have idempotent : Q (Q value)=Q value := congrArg (fun f:H →L[ℂ] H=>f value) Q_idempotent
  have source := quarter_centered_chart (read value)
  change centeredOperator q (embed (read value))=embed (S (read value)) at source
  rw [embed_read] at source
  change Q (burnolRechartedTruncatedFourierOperator q (Q (Q value)))=_ at source
  rw [idempotent] at source
  exact source

private theorem quarter_square (value:H) :
    centeredSquare q value=embed (S (S (read value))) := by
  change centeredOperator q (centeredOperator q value)=_
  rw [quarter_centered,quarter_centered,read_embed]

def chartSchur (radius:ℝ) : Op := 1-centeredSquare radius
def chartInverse (radius:ℝ) : Op := Ring.inverse (chartSchur radius)

/-- The existing BI and literal constant channel supply the q inverse, without a new solve. -/
def existingChartInverse : Op := 1-Q+embed.comp ((burnolMeanZeroBlockInverse).comp read)

theorem existing_inverse_embed (value:M) :
    existingChartInverse (embed value)=embed (BI value) := by
  change embed value-Q (embed value)+embed (BI (read (embed value)))=_
  rw [Q_embed,read_embed,sub_self,zero_add]

private theorem existing_inverse_Q (value:H) (centered:Q value=value) :
    existingChartInverse value=embed (BI (read value)) := by
  change value-Q value+embed (BI (read value))=_
  rw [centered,sub_self,zero_add]

private theorem inverse_right : chartSchur q*existingChartInverse=1 := by
  apply ContinuousLinearMap.ext
  intro value
  change existingChartInverse value-centeredSquare q (existingChartInverse value)=value
  rw [quarter_square]
  have readInverse : read (existingChartInverse value)=BI (read value) := by
    change read (value-Q value+embed (BI (read value)))=_
    rw [map_add,map_sub,read_Q,sub_self,zero_add,read_embed]
  rw [readInverse]
  have paid := congrArg (fun operator:OpM=>operator (read value)) burnolMeanZeroBlockInverse_right
  change BI (read value)-S (S (BI (read value)))=read value at paid
  have transported := congrArg embed paid
  rw [map_sub,embed_read] at transported
  change value-Q value+embed (BI (read value))-embed (S (S (BI (read value))))=value
  linear_combination (norm:=module) transported

private theorem inverse_left : existingChartInverse*chartSchur q=1 := by
  apply ContinuousLinearMap.ext
  intro value
  change existingChartInverse (value-centeredSquare q value)=value
  rw [quarter_square]
  change value-embed (S (S (read value)))-Q (value-embed (S (S (read value))))+
    embed (BI (read (value-embed (S (S (read value))))))=value
  rw [map_sub,Q_embed,map_sub,read_embed]
  have paid := congrArg (fun operator:OpM=>operator (read value))
    (Ring.inverse_mul_cancel _ burnolMeanZeroOneMinusSquare_isUnit)
  change BI (read value-S (S (read value)))=read value at paid
  rw [paid,embed_read]
  module

private def quarterSourceUnit : Opˣ where
  val := chartSchur q
  inv := existingChartInverse
  val_inv := inverse_right
  inv_val := inverse_left

theorem actual_existing_chart_inverse : chartInverse q=existingChartInverse :=
  Ring.inverse_unit quarterSourceUnit

/-- The complete centered reaction, including sine, generates the actual inverse norm derivative. -/
theorem actual_inverse_velocity : HasDerivAt chartInverse
    (existingChartInverse*sourceReaction q*existingChartInverse) q := by
  have source : HasDerivAt chartSchur (-sourceReaction q) q := by
    simpa only [chartSchur,Pi.sub_apply,zero_sub] using!
      (hasDerivAt_const q (1:Op)).sub (actual_centered_square_velocity q (by norm_num))
  have actual := (hasFDerivAt_ringInverse (𝕜:=ℝ) quarterSourceUnit).comp_hasDerivAt q source
  change HasDerivAt chartInverse
    (-ContinuousLinearMap.mulLeftRight ℝ Op existingChartInverse existingChartInverse (-sourceReaction q)) q at actual
  simpa only [neg_apply,ContinuousLinearMap.mulLeftRight_apply,neg_mul,mul_neg,neg_neg] using actual

private theorem source_column_Q (radius:ℝ) : Q (sourceColumn radius)=sourceColumn radius := by
  have idempotent (value:H) : Q (Q value)=Q value :=
    congrArg (fun f:H →L[ℂ] H=>f value) Q_idempotent
  simp only [sourceColumn,p,map_sub,map_smul,idempotent]

private theorem source_reaction_Q (radius:ℝ) (value:H) :
    Q (sourceReaction radius value)=sourceReaction radius value := by
  simp only [sourceReaction,sub_apply,smul_apply,InnerProductSpace.rankOne_apply,map_sub,map_smul,
    source_column_Q,sine_mean_zero]

theorem actual_even_inverse_effect (value:M) (even:sourceMeanZeroReflection value=value) :
    (existingChartInverse*sourceReaction q*existingChartInverse) (embed value)=
      (16:ℂ) • (inner ℂ Response.u value • embed Response.u) := by
  change existingChartInverse (sourceReaction q (existingChartInverse (embed value)))=_
  rw [existing_inverse_embed,existing_inverse_Q _ (source_reaction_Q q _)]
  have actual := congrArg embed (actual_even_inverse_sandwich value even)
  change embed (BI (read (sourceReaction q (embed (BI value)))) )=_ at actual
  simpa only [map_smul] using actual

theorem actual_even_inverse_source_velocity (value:M) (even:sourceMeanZeroReflection value=value) :
    HasDerivAt (fun radius:ℝ=>chartInverse radius (embed value))
      ((16:ℂ) • (inner ℂ Response.u value • embed Response.u)) q := by
  have generated := ((ContinuousLinearMap.apply ℂ H (embed value)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    q actual_inverse_velocity
  change HasDerivAt (fun radius:ℝ=>chartInverse radius (embed value))
    ((existingChartInverse*sourceReaction q*existingChartInverse) (embed value)) q at generated
  rw [actual_even_inverse_effect value even] at generated
  exact generated

end FixedWindowFourierReaction.CenteredInverseFlow
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
