import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualPreparedNativeTemporalCorrection
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedEMTemporalFreeReturn

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualPreparedNativeTemporal
open SaturationMonoid.PhysicsCore Stage9C.Material.SpinPair
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open ActualDressedFullCoulomb ActualDressedCorrectedGreen
open ActualSourcePreparedTemporalQuantumWard ActualSourcePreparedTemporalEMConstraint
open ActualSourcePreparedTemporalQuantumIR ActualSourcePreparedN3MovingResponse
open ActualSourcePreparedStaticCorrectedReturn
open ActualSourcePreparedN3EMChargeRead ActualDressedNoetherCoulombUnit
open ActualSourcePreparedEMTemporalFreeReturn ActualDressedEMTemporal
open PreparationVacuumActionFieldLift
open scoped Matrix BigOperators

/-- The scaled native-left balance: the whole corrected scalar minus the Gram
background plus the three explicit source balances is the Noether-scaled
actual EM driver contraction. -/
theorem actual_native_temporal_balance (event : DressedEvent) (e : scaleDomain)
    (sigma : ℝ) (n : PhysicalMomentum) (unit : spatialSquare n = 1)
    (positive : 0 < sigma) (regular : correctedDet event e.val 0 sigma n ≠ 0) :
    (e.val : ℂ)^4 * sourceN3TemporalEMCoefficient event e.val sigma n -
        noetherPairScale^2 / (2 * (lapse : ℂ)) * (3/4 : ℂ) +
        noetherPairScale^2 / (2 * (lapse : ℂ)) *
          (actualNativeAuxiliaryQuantumRead event e sigma n +
            actualNativeBackgroundRead event e sigma n +
            actualNativeLowerRead event e sigma n) =
      noetherPairScale^2 / (2 * (lapse : ℂ)) *
        dotProduct sourceTemporalEMForce (sourceTemporalActualQuantumDriver event e sigma n) := by
  have scaled := actual_native_scaled_em_return event e sigma n unit positive regular
  linear_combination scaled

/-- The actual two-clock price on the EM driver arm, carried back to the
corrected temporal scalar through the native balance. No uniform field norm
or fixed forcing hypothesis enters. -/
theorem actual_native_temporal_clock_price (event : DressedEvent) (e : scaleDomain)
    (sigma : ℝ) (n : PhysicalMomentum) (unit : spatialSquare n = 1)
    (positive : 0 < sigma) (regular : correctedDet event e.val 0 sigma n ≠ 0)
    (small : sigma ≤ 1) :
    sigma * ‖(e.val : ℂ)^4 * sourceN3TemporalEMCoefficient event e.val sigma n -
        noetherPairScale^2 / (2 * (lapse : ℂ)) * (3/4 : ℂ) +
        noetherPairScale^2 / (2 * (lapse : ℂ)) *
          (actualNativeAuxiliaryQuantumRead event e sigma n +
            actualNativeBackgroundRead event e sigma n +
            actualNativeLowerRead event e sigma n)‖ ≤
      2 * ‖noetherPairScale^2 / (2 * (lapse : ℂ))‖ *
        ∑ j : Fin 289, emTemporalPrice event ((e.val^2 : ℝ) • n) (fieldUnit j) *
          ‖sourceTemporalCorrectedField event e.val sigma n j‖ := by
  rw [actual_native_temporal_balance event e sigma n unit positive regular, norm_mul]
  have price := source_temporal_quantum_em_driver_clock_price event e sigma n positive small
  calc sigma * (‖noetherPairScale^2 / (2 * (lapse : ℂ))‖ *
        ‖dotProduct sourceTemporalEMForce (sourceTemporalActualQuantumDriver event e sigma n)‖)
      = ‖noetherPairScale^2 / (2 * (lapse : ℂ))‖ *
          (sigma * ‖dotProduct sourceTemporalEMForce
            (sourceTemporalActualQuantumDriver event e sigma n)‖) := by ring
    _ ≤ ‖noetherPairScale^2 / (2 * (lapse : ℂ))‖ *
          (2 * ∑ j : Fin 289, emTemporalPrice event ((e.val^2 : ℝ) • n) (fieldUnit j) *
            ‖sourceTemporalCorrectedField event e.val sigma n j‖) :=
        mul_le_mul_of_nonneg_left price (norm_nonneg _)
    _ = _ := by ring


end LowEnergy.GaussComposite.ActualPreparedNativeTemporal
