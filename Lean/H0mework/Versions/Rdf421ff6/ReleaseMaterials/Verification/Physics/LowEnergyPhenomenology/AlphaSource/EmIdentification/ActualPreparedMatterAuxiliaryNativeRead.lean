import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualPreparedMatterAuxiliaryPiReturn
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualPreparedNativeTemporalPrice

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualPreparedMatterAuxiliary
open SaturationMonoid.PhysicsCore Stage9C.Material.SpinPair
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumActionFieldLift
open ActualDressedFullCoulomb ActualDressedZeroClockVector ActualDressedZeroClockFrequency
open ActualDressedEMZeroClockColumns ActualDressedEMQuantumThreshold ActualDressedEMClockDispersion
open ActualDressedEMNativeAuxiliary ActualDressedEMAuxiliaryFeedback ActualDressedEMNativeSchurClock
open ActualDressedEMNativePrincipal ActualDressedEMNativeMomentum ActualDressedEMNativeCoulomb
open ActualDressedEMCorrectedCouplingSource ActualDressedCorrectedGreen
open ActualSourcePreparedTemporalQuantumWard ActualSourcePreparedTemporalEMConstraint
open ActualSourcePreparedTemporalQuantumIR ActualSourcePreparedN3MovingResponse
open ActualSourcePreparedStaticCorrectedReturn ActualSourcePreparedEMEnclosure
open ActualSourcePreparedN3EMChargeRead ActualDressedNoetherCoulombUnit
open ActualSourcePreparedEMTemporalFreeReturn ActualDressedEMTemporal
open ActualEMResponseSplit ActualEMAction
open ActualPreparedNativeTemporal
open Filter Set MeasureTheory
open scoped Matrix BigOperators Topology ContDiff

/-- The native auxiliary-quantum read at the actual prepared driver is zero:
the generated auxiliary slice of the actual quantum driver is zero, so the
whole inverse/auxiliary/rest chain applied to it vanishes. No auxiliary-block
hypothesis is used on the native J side. -/
theorem actual_native_auxiliary_quantum_zero (event : DressedEvent) (e : scaleDomain)
    (sigma : ℝ) (n : PhysicalMomentum) (positiveSigma : 0 < sigma) :
    actualNativeAuxiliaryQuantumRead event e sigma n = 0 := by
  unfold actualNativeAuxiliaryQuantumRead
  rw [actual_quantum_driver_auxiliary_zero event e sigma n positiveSigma]
  simp only [Matrix.mulVec_zero, Pi.zero_apply]

/-- The stronger two-balance native-left scaled equation: the auxiliary
quantum read is discharged by the generated zero-slice producer, while the
native background and momentum-lower balances remain explicit. -/
theorem actual_native_scaled_two_balance (event : DressedEvent) (e : scaleDomain)
    (sigma : ℝ) (n : PhysicalMomentum) (unit : spatialSquare n = 1)
    (positive : 0 < sigma) (regular : correctedDet event e.val 0 sigma n ≠ 0) :
    (e.val : ℂ)^4 * sourceN3TemporalEMCoefficient event e.val sigma n =
      noetherPairScale^2 / (2 * (lapse : ℂ)) *
        ((3/4 : ℂ) +
          dotProduct sourceTemporalEMForce (sourceTemporalActualQuantumDriver event e sigma n) -
          actualNativeBackgroundRead event e sigma n -
          actualNativeLowerRead event e sigma n) := by
  have scaled := actual_native_scaled_em_return event e sigma n unit positive regular
  rw [actual_native_auxiliary_quantum_zero event e sigma n positive] at scaled
  linear_combination scaled

/-- The two-balance clock price: the auxiliary arm is discharged by the
generated producer; background and momentum-lower stays explicit. -/
theorem actual_native_two_balance_clock_price (event : DressedEvent) (e : scaleDomain)
    (sigma : ℝ) (n : PhysicalMomentum) (unit : spatialSquare n = 1)
    (positive : 0 < sigma) (regular : correctedDet event e.val 0 sigma n ≠ 0)
    (small : sigma ≤ 1) :
    sigma * ‖(e.val : ℂ)^4 * sourceN3TemporalEMCoefficient event e.val sigma n -
        noetherPairScale^2 / (2 * (lapse : ℂ)) * (3/4 : ℂ) +
        noetherPairScale^2 / (2 * (lapse : ℂ)) *
          (actualNativeBackgroundRead event e sigma n +
            actualNativeLowerRead event e sigma n)‖ ≤
      2 * ‖noetherPairScale^2 / (2 * (lapse : ℂ))‖ *
        ∑ j : Fin 289, emTemporalPrice event ((e.val^2 : ℝ) • n) (fieldUnit j) *
          ‖sourceTemporalCorrectedField event e.val sigma n j‖ := by
  have price := actual_native_temporal_clock_price event e sigma n unit positive regular small
  rw [actual_native_auxiliary_quantum_zero event e sigma n positive] at price
  simpa only [zero_add] using price


end LowEnergy.GaussComposite.ActualPreparedMatterAuxiliary
