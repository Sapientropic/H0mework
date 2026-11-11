import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.FiniteRank.Source.CenteredReaction
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerJordanAction
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.InverseEuler.Price
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusContactClosureSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace FixedWindowFourierReaction.CenteredInverse
open Complex Filter MeasureTheory Set FixedWindowFourierReaction OriginalRieszSource
open FixedWindowFourierReaction.CenteredSource
open scoped InnerProductSpace Topology
attribute [local instance 1100] NormedSpace.complexToReal
local notation "q" => (1/4:ℝ)
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "Hq" => BurnolQuarterIntervalL2
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "B" => burnolMeanZeroOneMinusSquare
local notation "BI" => burnolMeanZeroBlockInverse
local notation "OpM" => M →L[ℂ] M
local instance : CompleteSpace M :=
  IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete

def embed : M →L[ℂ] H :=
  quarterChart.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (Submodule.subtypeL burnolQuarterMeanZeroClosedFace.toSubmodule)
def read : H →L[ℂ] M :=
  Constructor.zeroMean.comp quarterChart.symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem read_embed (value:M) : read (embed value)=value := by
  change Constructor.zeroMean (quarterChart.symm (quarterChart (value:Hq)))=value
  rw [quarterChart.symm_apply_apply]
  apply Subtype.ext
  exact Submodule.starProjection_eq_self_iff.mpr value.property

theorem embed_read (value:H) : embed (read value)=Q value := by
  change quarterChart (burnolQuarterMeanZeroProjection (quarterChart.symm value))=Q value
  rw [quarter_projection_chart,quarterChart.apply_symm_apply]

/-- The original constant-Fourier source fixes the literal quarter eta normalization. -/
theorem actual_eta_source : embed Response.eta=(1/2:ℂ) • sourceColumn q := by
  have original := ConstantFourierEulerVelocity.original_eta_velocity
  have ward := ConstantFourierEulerVelocity.constant_column_ward q (by norm_num : 0<q)
  change (q:ℂ) • burnolRadiusRechartedTruncatedFourierDerivative (by norm_num : 0<q) e+
    burnolRechartedTruncatedFourierOperator q e=(2*q:ℂ) • c q at ward
  have velocity : (q/2:ℂ) • burnolRadiusRechartedTruncatedFourierDerivative (by norm_num : 0<q) e-
      (1/2:ℂ) • burnolRechartedTruncatedFourierOperator q e=
      (q:ℂ) • c q-burnolRechartedTruncatedFourierOperator q e := by
    calc
      _=(1/2:ℂ) • ((q:ℂ) • burnolRadiusRechartedTruncatedFourierDerivative (by norm_num : 0<q) e+
          burnolRechartedTruncatedFourierOperator q e)-burnolRechartedTruncatedFourierOperator q e := by
        push_cast
        module
      _=_ := by
        rw [ward]
        push_cast
        module
  rw [velocity] at original
  have squareRoot : Real.sqrt q=1/2 :=
    (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).mpr (by norm_num)
  rw [squareRoot] at original
  change embed Response.eta=_ at original
  rw [original]
  simp only [sourceColumn,p,map_sub,map_smul]
  norm_num

def square (radius:ℝ) : OpM := read.comp ((centeredSquare radius).comp embed)
def schur (radius:ℝ) : OpM := 1-square radius
def inverse (radius:ℝ) : OpM := Ring.inverse (schur radius)
def reaction (radius:ℝ) : OpM := read.comp ((sourceReaction radius).comp embed)

theorem actual_quarter_schur : schur q=B := by
  apply ContinuousLinearMap.ext
  intro value
  change value-read (centeredSquare q (embed value))=value-S (S value)
  have twice : centeredSquare q (embed value)=embed (S (S value)) := by
    change centeredOperator q (centeredOperator q (quarterChart (value:Hq)))=_
    rw [quarter_centered_chart,quarter_centered_chart]
    rfl
  rw [twice,read_embed]

theorem actual_existing_inverse : inverse q=BI := by
  unfold inverse
  rw [actual_quarter_schur]
  rfl

open private inverse_even from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerJordanAction
open private qualified_S_pairing_left from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.InverseEuler.Price

private theorem embed_even (value:M) (even:sourceMeanZeroReflection value=value) :
    reflectRestricted 1 (embed value)=embed value := by
  change reflectRestricted 1 (burnolRadiusRechartEquiv (by norm_num : 0<q) (value:Hq))=
    quarterChart (value:Hq)
  rw [←chart_reflection]
  exact congrArg quarterChart (congrArg (fun x:M=>(x:Hq)) even)

private theorem inverse_eta_pair (value:M) : inner ℂ Response.eta (BI value)=inner ℂ Response.u value := by
  have source : Response.u-S (S Response.u)=Response.eta := Response.u_equation
  have first := qualified_S_pairing_left Response.u (S (BI value)) Response.u_reflection
  have second := qualified_S_pairing_left (S Response.u) (BI value) Response.v_reflection
  have solved := congrArg (fun operator:OpM=>operator value) burnolMeanZeroBlockInverse_right
  change BI value-S (S (BI value))=value at solved
  rw [←source,inner_sub_left,←second,←first,←inner_sub_right,solved]

theorem actual_even_inverse_sandwich (value:M) (even:sourceMeanZeroReflection value=value) :
    BI (reaction q (BI value))=(16:ℂ) • (inner ℂ Response.u value • Response.u) := by
  have evenInverse := embed_even (BI value) (inverse_even value even)
  have normalized : sourceColumn q=(2:ℂ) • embed Response.eta := by
    have source := actual_eta_source
    linear_combination (norm:=module) -(2:ℂ) • source
  change BI (read (sourceReaction q (embed (BI value))))=_
  rw [actual_even_source_reaction q _ evenInverse,normalized]
  have pair : inner ℂ (embed Response.eta) (embed (BI value))=inner ℂ Response.eta (BI value) :=
    quarterChart.inner_map_map (Response.eta:Hq) (BI value:Hq)
  simp only [inner_smul_left,map_smul,smul_smul]
  rw [pair,inverse_eta_pair,read_embed]
  rw [show BI Response.eta=Response.u from rfl]
  simp only [map_ofNat]
  norm_num
  module

end FixedWindowFourierReaction.CenteredInverse
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalConstantFourierFixedPrice
open Complex BurnolPhysicalState OriginalRieszSource
open OriginalRieszFinitePairing.CoPoisson.Ward OriginalKFiniteOrderRelease.UnitPowerJordanAction
open OriginalKPairedBEulerJunctionSource OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
open OriginalKDirectRCofinalOutsideVolterraSource
open FixedWindowFourierReaction.CenteredInverse
open scoped InnerProductSpace
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "Hq" => BurnolQuarterIntervalL2
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local instance : CompleteSpace M :=
  IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete
open private qualified_S_pairing_left from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.InverseEuler.Price
open private fourier_even from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerJordanAction

/-- The fixed original receiver consumes its actual two source drives; no nonzero moment is supplied. -/
theorem actual_fixed_price_receiver (c:BurnolCompletedMellinCoordinate) :
    OriginalWholeDebtRJointMobiusContactClosureSource.finitePrice c c=
      inner ℂ (hPowerBColumn (barC c)) (sourceDrive c 1)-
        inner ℂ (S (hPowerBColumn (barC c))) (sourceDrive c 0) := by
  let h := hPowerBColumn (barC c)
  have even := congrArg (fun value:M=>(value:Hq)) (log_B_even (barC c) 0)
  have twiceEven := congrArg (fun value:M=>(value:Hq))
    (fourier_even h (log_B_even (barC c) 0))
  have firstPair := qualified_S_pairing_left h (sourceFirst c) even
  have secondPair := qualified_S_pairing_left (S h) (sourceSecond c) twiceEven
  have first := burnolMeanZeroBlock_first_equation (burnolAmbientMeanZeroBlockRhs (sourceAction c))
  have second := burnolMeanZeroBlock_second_equation (burnolAmbientMeanZeroBlockRhs (sourceAction c))
  change sourceFirst c+S (sourceSecond c)=sourceDrive c 0 at first
  change S (sourceFirst c)+sourceSecond c=sourceDrive c 1 at second
  have native : h-S (S h)=SingularCounting.centeredPower (barC c) := by
    have paid := (h_power_B_source (barC c)).1
    change h+S (-S h)=_ at paid
    simpa only [map_neg,sub_eq_add_neg] using paid
  unfold OriginalWholeDebtRJointMobiusContactClosureSource.finitePrice
  rw [←native,←first,←second,inner_sub_left,inner_add_right,inner_add_right,firstPair,secondPair]
  ring

end OriginalConstantFourierFixedPrice
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
