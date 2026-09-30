import H0mework.NavierStokes.NativeWorkWhole.InstantaneousActionCommuting
import H0mework.NavierStokes.SourceEstimates.WholeKineticDecay
import H0mework.NavierStokes.Energy.StrongContinuationKineticDifferenceGronwall

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.SourceFieldRenewal

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap
open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open ThreeDimensionalVorticityCoefficientWholeInstantaneousActionCommuting
open WholeKineticDecay
open ThreeDimensionalVorticityCoefficientStrongContinuationKineticDifferenceGronwall

noncomputable section

variable {nu : Viscosity} {initial : ComplexVorticityHilbertState} {duration : ℝ}
  (receipt : WholeContinuousMildSerrinReceipt nu initial duration)

def netPowerField : ℝ → ℝ :=
  commonTimeZeroExtension duration (receiptWholeInstantaneousNetPower receipt)

theorem netPowerField_integrable : IntervalIntegrable (netPowerField receipt) volume 0 duration :=
  commonTimeZeroExtension_intervalIntegrable_of_integrable duration receipt.requestedTimePos.le _
    (receiptWholeInstantaneousNetPower_integrable receipt)

theorem mass_prefix_energy (terminal : Icc (0 : ℝ) duration) :
    (∫ t in (0 : ℝ)..terminal.1, netPowerField receipt t) =
      massField receipt terminal.1 - massField receipt 0 := by
  by_cases zero : terminal.1 = 0
  · rw [zero, intervalIntegral.integral_same, sub_self]
  · have positive : 0 < terminal.1 := terminal.2.1.lt_of_ne' zero
    let shortReceipt := restrictWholeContinuousMildSerrinReceipt positive terminal.2.2 receipt
    have powerSame (t : Icc (0 : ℝ) terminal.1) :
        netPowerField receipt t.1 = receiptWholeInstantaneousNetPower shortReceipt t := by
      rw [netPowerField, commonTimeZeroExtension_of_mem duration _ t.1
        ⟨t.2.1, t.2.2.trans terminal.2.2⟩]
      rfl
    calc
      (∫ t in (0 : ℝ)..terminal.1, netPowerField receipt t) =
          ∫ t : Icc (0 : ℝ) terminal.1, netPowerField receipt t.1
            ∂commonTimeMeasure terminal.1 :=
        (commonTime_integral_eq_intervalIntegral terminal.1 positive.le _).symm
      _ = ∫ t, receiptWholeInstantaneousNetPower shortReceipt t ∂commonTimeMeasure terminal.1 := by
        apply integral_congr_ae
        filter_upwards with t
        exact powerSame t
      _ = wholeVorticityEuclideanMass
          (shortReceipt.wholePath ⟨terminal.1, positive.le, le_rfl⟩) -
          wholeVorticityEuclideanMass initial :=
        integral_receiptWholeInstantaneousNetPower_eq_boundary shortReceipt
      _ = massField receipt terminal.1 - massField receipt 0 := by
        rw [massField_at receipt terminal]
        have zeroMass : massField receipt 0 = wholeVorticityEuclideanMass initial := by
          rw [massField_at receipt ⟨0, le_rfl, receipt.requestedTimePos.le⟩,
            receipt.wholePath_initial]
        rw [zeroMass]
        rfl

end
end SaturationMonoid.NavierStokes.SourceFieldRenewal
