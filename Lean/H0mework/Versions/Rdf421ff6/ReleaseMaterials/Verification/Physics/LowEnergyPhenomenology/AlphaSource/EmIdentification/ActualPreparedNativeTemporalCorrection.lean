import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualPreparedNativeTemporalEquation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualPreparedNativeTemporal
open SaturationMonoid.PhysicsCore Stage9C.Material.SpinPair
open SourcePropagationNativeActionHessian ActualEMAction ActualEMCarrierOwn PhysicalEMGaugeRealization
open CanonicalGradedSpatialSource PreparationCoordinates PreparationVacuumMixedFieldReturn
  PreparationVacuumGaugeSourceInjection
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open ActualDressedFullCoulomb ActualDressedZeroClockVector ActualDressedZeroClockFrequency
open ActualDressedEMZeroClockColumns ActualDressedEMQuantumThreshold ActualDressedEMClockDispersion
open ActualDressedEMNativeAuxiliary ActualDressedEMAuxiliaryFeedback ActualDressedEMNativeSchurClock
open ActualDressedEMNativePrincipal ActualDressedEMNativeMomentum ActualDressedEMNativeCoulomb
open ActualDressedEMCorrectedCouplingSource
open ActualSourcePreparedTemporalQuantumWard ActualSourcePreparedTemporalEMConstraint
open ActualSourcePreparedTemporalQuantumIR ActualSourcePreparedN3MovingResponse
open ActualSourcePreparedStaticCorrectedReturn ActualSourcePreparedEMEnclosure
open ActualSourcePreparedN3EMChargeRead ActualDressedNoetherCoulombUnit
open ActualEMResponseSplit ActualDressedCorrectedGreen
open scoped Matrix BigOperators

/-- The auxiliary quantum forcing read at the actual prepared driver; no
auxiliary-zero hypothesis is made. -/
def actualNativeAuxiliaryQuantumRead (event : DressedEvent) (e : scaleDomain)
    (sigma : ℝ) (n : PhysicalMomentum) : ℂ :=
  (nativeEMRestInsertion.transpose *ᵥ
    (nativeRestAuxiliary (frequencyRay e.val 0 n) *ᵥ
      (nativeAuxiliaryInverseMatrix *ᵥ
        emAuxiliarySlice (sourceTemporalActualQuantumDriver event e sigma n)))) 0

/-- The native background read of the actual prepared field at zero momentum. -/
def actualNativeBackgroundRead (event : DressedEvent) (e : scaleDomain)
    (sigma : ℝ) (n : PhysicalMomentum) : ℂ :=
  (nativeEMRestInsertion.transpose *ᵥ
    (nativeSchurMatrix 0 *ᵥ
      emRestSlice (sourceTemporalCorrectedField event e.val sigma n))) 0

/-- The momentum-lower read of the actual prepared field. -/
def actualNativeLowerRead (event : DressedEvent) (e : scaleDomain)
    (sigma : ℝ) (n : PhysicalMomentum) : ℂ :=
  (nativeEMRestInsertion.transpose *ᵥ
    (nativeMomentumLower (frequencyRay e.val 0 n) *ᵥ
      emRestSlice (sourceTemporalCorrectedField event e.val sigma n))) 0

/-- The complete native correction is the actual driver contraction minus the
three explicit source balances: auxiliary quantum forcing, native background
and the momentum-lower operator. -/
theorem actual_native_temporal_correction_return (event : DressedEvent) (e : scaleDomain)
    (sigma : ℝ) (n : PhysicalMomentum) :
    actualNativeTemporalCorrection event e sigma n =
      dotProduct sourceTemporalEMForce (sourceTemporalActualQuantumDriver event e sigma n) -
        actualNativeAuxiliaryQuantumRead event e sigma n -
        actualNativeBackgroundRead event e sigma n -
        actualNativeLowerRead event e sigma n := by
  unfold actualNativeTemporalCorrection nativeCompleteCorrection nativeCompleteForceRead
    actualNativeAuxiliaryQuantumRead actualNativeBackgroundRead actualNativeLowerRead
    sourceTemporalActualQuantumDriver
  have observed := actual_complete_em_observation
    (sourcePreparedClockQuantumMatrix event e.val sigma n *ᵥ
      sourceTemporalCorrectedField event e.val sigma n)
  rw [Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.mulVec_sub, Pi.sub_apply, Pi.sub_apply,
    Pi.sub_apply, observed]
  unfold sourceTemporalEMForce
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]

/-- The scaled T00 equation decomposes the actual driver read into the explicit
auxiliary, background and momentum-lower source balances at the same occurrence. -/
theorem actual_native_scaled_em_return (event : DressedEvent) (e : scaleDomain)
    (sigma : ℝ) (n : PhysicalMomentum) (unit : spatialSquare n = 1)
    (positive : 0 < sigma) (regular : correctedDet event e.val 0 sigma n ≠ 0) :
    (e.val : ℂ)^4 * sourceN3TemporalEMCoefficient event e.val sigma n =
      noetherPairScale^2 / (2 * (lapse : ℂ)) *
        ((3/4 : ℂ) +
          dotProduct sourceTemporalEMForce (sourceTemporalActualQuantumDriver event e sigma n) -
          actualNativeAuxiliaryQuantumRead event e sigma n -
          actualNativeBackgroundRead event e sigma n -
          actualNativeLowerRead event e sigma n) := by
  have scaled := actual_native_temporal_scaled event e sigma n unit positive regular
  rw [actual_native_temporal_correction_return] at scaled
  linear_combination scaled


end LowEnergy.GaussComposite.ActualPreparedNativeTemporal
