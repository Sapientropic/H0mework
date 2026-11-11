import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.FiniteRank.Source.CenteredInverseFlow

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalConstantFourierPriceFlow
open Complex Filter MeasureTheory Set BurnolPhysicalState
open FixedWindowFourierReaction OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open FixedWindowFourierReaction.CenteredSource FixedWindowFourierReaction.CenteredInverse
open FixedWindowFourierReaction.CenteredInverseFlow OriginalKPairedBEulerJunctionSource
open scoped InnerProductSpace Topology
attribute [local instance 1100] Module.complexToReal NormedSpace.complexToReal
local notation "q" => (1/4:ℝ)
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "Hq" => BurnolQuarterIntervalL2
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "B" => burnolMeanZeroOneMinusSquare
local notation "BI" => burnolMeanZeroBlockInverse
local notation "Op" => H →L[ℂ] H
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local instance : CompleteSpace M :=
  IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete

def power (c:BurnolCompletedMellinCoordinate) : M := SingularCounting.centeredPower (barC c)
def nativeDrive (c:BurnolCompletedMellinCoordinate) : M := sourceDrive c 1-S (sourceDrive c 0)
def priceSource (c:BurnolCompletedMellinCoordinate) (radius:ℝ) : H :=
  embed (sourceDrive c 1)-centeredOperator radius (embed (sourceDrive c 0))
def nativePriceFlow (c:BurnolCompletedMellinCoordinate) (radius:ℝ) : ℂ :=
  inner ℂ (embed (power c)) (chartInverse radius (priceSource c radius))

def fourierVelocity : Op := Q*burnolRadiusRechartedTruncatedFourierDerivative (by norm_num : 0<q)*Q

theorem actual_centered_velocity : HasDerivAt centeredOperator fourierVelocity q := by
  have generated := ((hasDerivAt_const q Q).mul
    (burnolRechartedTruncatedFourierOperator_hasDerivAt (by norm_num : 0<q))).mul
      (hasDerivAt_const q Q)
  simp only [zero_mul,zero_add,mul_zero,add_zero] at generated
  exact generated

theorem actual_original_drive (c:BurnolCompletedMellinCoordinate) :
    priceSource c q=embed (nativeDrive c) := by
  have actual := quarter_centered_chart (sourceDrive c 0)
  change centeredOperator q (embed (sourceDrive c 0))=embed (S (sourceDrive c 0)) at actual
  unfold priceSource nativeDrive
  rw [actual,map_sub]

theorem actual_second_source_balance (c:BurnolCompletedMellinCoordinate) :
    B (sourceSecond c)=nativeDrive c := by
  have first := burnolMeanZeroBlock_first_equation (burnolAmbientMeanZeroBlockRhs (sourceAction c))
  have second := burnolMeanZeroBlock_second_equation (burnolAmbientMeanZeroBlockRhs (sourceAction c))
  change sourceFirst c+S (sourceSecond c)=sourceDrive c 0 at first
  change S (sourceFirst c)+sourceSecond c=sourceDrive c 1 at second
  change sourceSecond c-S (S (sourceSecond c))=sourceDrive c 1-S (sourceDrive c 0)
  rw [←first,←second,map_add]
  module

theorem actual_second_source_preimage (c:BurnolCompletedMellinCoordinate) :
    BI (nativeDrive c)=sourceSecond c := by
  rw [←actual_second_source_balance]
  have generated := congrArg (fun operator:M →L[ℂ] M=>operator (sourceSecond c))
    (Ring.inverse_mul_cancel _ burnolMeanZeroOneMinusSquare_isUnit)
  exact generated

open private sourceOneMinusSquare_reflect from
  H0mework.Versions.R7e4da746.Arithmetic.RieszForcing.SourceParity
open private inverse_eta_pair from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.FiniteRank.Source.CenteredInverse

private theorem original_drive_even (c:BurnolCompletedMellinCoordinate) :
    sourceMeanZeroReflection (nativeDrive c)=nativeDrive c := by
  have even : sourceMeanZeroReflection (sourceSecond c)=sourceSecond c := by
    apply Subtype.ext
    exact source_correction_even c 1
  rw [←actual_second_source_balance]
  have generated := sourceOneMinusSquare_reflect (sourceSecond c)
  rw [even] at generated
  exact generated.symm

/-- The inverse evolution is consumed by the literal original finite-price receiver. -/
theorem actual_fixed_price (c:BurnolCompletedMellinCoordinate) :
    nativePriceFlow c q=OriginalWholeDebtRJointMobiusContactClosureSource.finitePrice c c := by
  unfold nativePriceFlow
  rw [actual_original_drive,actual_existing_chart_inverse,existing_inverse_embed,actual_second_source_preimage]
  exact quarterChart.inner_map_map (power c:Hq) (sourceSecond c:Hq)

theorem actual_native_reaction_pair (c:BurnolCompletedMellinCoordinate) :
    inner ℂ Response.u (nativeDrive c)=inner ℂ Response.eta (sourceSecond c) := by
  rw [←actual_second_source_preimage]
  exact (inverse_eta_pair (nativeDrive c)).symm

/-- Both actual varying operators are differentiated; the second leg retains J S' X. -/
theorem actual_fixed_price_velocity (c:BurnolCompletedMellinCoordinate) :
    HasDerivAt (nativePriceFlow c)
      ((16:ℂ)*inner ℂ (power c) Response.u*inner ℂ Response.u (nativeDrive c)-
        inner ℂ (embed (power c))
          (existingChartInverse (fourierVelocity (embed (sourceDrive c 0))))) q := by
  let X := embed (sourceDrive c 0)
  let Y := embed (sourceDrive c 1)
  let D : Op := existingChartInverse*sourceReaction q*existingChartInverse
  have product := actual_inverse_velocity.mul actual_centered_velocity
  rw [actual_existing_chart_inverse] at product
  have left := ((ContinuousLinearMap.apply ℂ H Y).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    q actual_inverse_velocity
  have right := ((ContinuousLinearMap.apply ℂ H X).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    q product
  have difference := left.sub right
  have same : (fun radius:ℝ=>chartInverse radius (priceSource c radius)) =ᶠ[𝓝 q]
      (fun radius:ℝ=>chartInverse radius Y-(chartInverse radius*centeredOperator radius) X) := by
    apply Filter.Eventually.of_forall
    intro radius
    change chartInverse radius (Y-centeredOperator radius X)=_
    rw [map_sub]
    rfl
  have generated := difference.congr_of_eventuallyEq same
  change HasDerivAt (fun radius:ℝ=>chartInverse radius (priceSource c radius))
    (D Y-(D*centeredOperator q+existingChartInverse*fourierVelocity) X) q at generated
  have balance : embed (nativeDrive c)=Y-centeredOperator q X := (actual_original_drive c).symm
  have paid := actual_even_inverse_effect (nativeDrive c) (original_drive_even c)
  change D (embed (nativeDrive c))=_ at paid
  have velocity : D Y-(D*centeredOperator q+existingChartInverse*fourierVelocity) X=
      (16:ℂ) • (inner ℂ Response.u (nativeDrive c) • embed Response.u)-
        existingChartInverse (fourierVelocity X) := by
    change D Y-(D (centeredOperator q X)+existingChartInverse (fourierVelocity X))=_
    rw [sub_add_eq_sub_sub,←map_sub,←balance,paid]
  rw [velocity] at generated
  have output := ((innerSL ℂ (embed (power c))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt q generated
  change HasDerivAt (nativePriceFlow c)
    (inner ℂ (embed (power c))
      ((16:ℂ) • (inner ℂ Response.u (nativeDrive c) • embed Response.u)-
        existingChartInverse (fourierVelocity X))) q at output
  rw [inner_sub_right,inner_smul_right,inner_smul_right] at output
  have pairing : inner ℂ (embed (power c)) (embed Response.u)=inner ℂ (power c) Response.u :=
    quarterChart.inner_map_map (power c:Hq) (Response.u:Hq)
  rw [pairing] at output
  convert! output using 1
  ring

end OriginalConstantFourierPriceFlow
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
