import H0mework.NavierStokes.StressWholeH1.Equation
import H0mework.NavierStokes.StressWholeH1.OriginalSource
import H0mework.NavierStokes.StressResolvent.WholeResolventEquation

set_option autoImplicit false
open scoped Topology

namespace SaturationMonoid.NavierStokes.NativeWholeH1SourceUniqueness

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeRecoveryTimeGramRaw
open NativeWholeResolvent NativeWholeResolventLimit NativeWholeH1Mixed NativeWholeH1Pairing
open NativeResolventCompactness NativeEndpointVelocityCarrier NativeOriginalResolventInput

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

/-- The H¹ input face is eliminated from the original receipt; every test input
and positive resolvent step use the same full-measure set of physical times. -/
theorem source_unique_ae (source : StressAt escape) (pointLe : point ≤ 1) :
    ∀ᵐ time ∂commonTimeMeasure 1, ∀ (step : ℝ) (positive : 0 < step) (input value : wholePhysical),
      H1 value → (∀ wave : Wave,
        wholeVelocity value.1 wave.1 - step • (row (meanInput source pointLe (.fixed time)) value wave.1 -
          (nu.coeff * integerWaveViscousMultiplier wave.1) • wholeVelocity value.1 wave.1) =
            wholeVelocity input.1 wave.1) →
      value = operator source pointLe (.fixed time) step positive input := by
  filter_upwards [NativeWholeH1OriginalSource.meanInput_curl_summable_ae source pointLe] with time regular
  intro step positive input value valueH1 equation
  apply NativeWholeH1Equation.whole_resolvent_unique nu (meanInput source pointLe (.fixed time)) input value
    (operator source pointLe (.fixed time) step positive input)
    (h1_of_curl_summable _ regular) valueH1
    (h1_of_curl_summable _ (operator_curl source pointLe (.fixed time) step positive input).1)
    step positive.le equation
  intro wave
  exact NativeWholeResolventEquation.operator_equation source pointLe (.fixed time) step positive input wave

end
end SaturationMonoid.NavierStokes.NativeWholeH1SourceUniqueness
