import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedEMMovingPiAge
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedEMNativeRead

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedJointNativeObservation
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage9C.Material.SpinPair PreparationVacuumActionFieldLift
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalCharacteristic
open ActualDressedFullCoulomb ActualDressedCorrectedGreen ActualDressedNoetherCoulombUnit
open ActualSourcePreparedEMMovingPiAge ActualSourcePreparedEMNativeRead
open ActualSourcePreparedTemporalEMConstraint ActualSourcePreparedTemporalQuantumWard
open ActualSourcePreparedTemporalQuantumIR
open ActualSourcePreparedN3EMChargeRead
open Filter
open scoped Topology Matrix BigOperators
attribute [local irreducible] sourceEMMovingDriverWindow sourceTemporalCorrectedField

/-- One finite-age restriction of the full original native balance.
Background and lower terms read the same actual full field as the driver. -/
def sourceJointNativeAgeWindow (event : DressedEvent) (e : scaleDomain)
    (sigma : ℝ) (n : PhysicalMomentum) (T : ℝ) : ℂ :=
  noetherPairScale^2/(2*(lapse : ℂ))*
    ((3/4 : ℂ)+sourceEMMovingDriverWindow event e sigma n T-
      sourceEMNativeBackgroundRead (sourceTemporalCorrectedField event e.val sigma n)-
      (e.val : ℂ)^2*sourceEMNativeLowerRead (frequencyRay 1 0 n)
        (sourceTemporalCorrectedField event e.val sigma n))

/-- Actual source Pi ages feed the complete temporal coefficient on the
original chart, with the original Noether units and both finite native reads. -/
theorem source_joint_native_age_window_limit (event : DressedEvent) (e : scaleDomain)
    (sigma : ℝ) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (positive : 0<sigma) (regular : correctedDet event e.val 0 sigma n≠0) :
    Tendsto (sourceJointNativeAgeWindow event e sigma n) atTop
      (𝓝 ((e.val : ℂ)^4*sourceN3TemporalEMCoefficient event e.val sigma n)) := by
  rw [source_em_native_scaled_finite_return event e sigma n unit positive regular]
  unfold sourceJointNativeAgeWindow
  exact (((source_em_moving_actual_driver_window_limit event e sigma n positive).const_add (3/4 : ℂ)).sub
    (tendsto_const_nhds (x:=sourceEMNativeBackgroundRead
      (sourceTemporalCorrectedField event e.val sigma n)))).sub
    (tendsto_const_nhds (x:=(e.val : ℂ)^2*sourceEMNativeLowerRead (frequencyRay 1 0 n)
      (sourceTemporalCorrectedField event e.val sigma n))) |>.const_mul (noetherPairScale^2/(2*(lapse : ℂ)))

/-- The complete finite-age physical balance is priced after combining
its terms. No separate Background or Lower endpoint is supplied. -/
theorem source_joint_native_age_window_price (event : DressedEvent) (e : scaleDomain)
    (sigma : ℝ) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (positive : 0<sigma) (regular : correctedDet event e.val 0 sigma n≠0)
    (T : ℝ) (future : 0≤T) :
    ‖sourceJointNativeAgeWindow event e sigma n T-
      (e.val : ℂ)^4*sourceN3TemporalEMCoefficient event e.val sigma n‖ ≤
      ‖noetherPairScale^2/(2*(lapse : ℂ))‖*
        ∑j : Fin 289, (Real.exp (-sigma*T)*ActualDressedEMTemporal.emTemporalPrice
          event (e.val^2 • n) (fieldUnit j)*(1+T)+
          ‖(sigma : ℂ)‖*(∑i : Fin 289,‖((PreparationPhysicalPhaseGaugeRealization.sourcePhaseGaugeField 0) i : ℂ)‖)*
            ActualDressedSignal.dressedSignalTailPrice event (e.val^2 • n) (0 : Fin 4 → ℂ) (sigma : ℂ) T)*
          ‖sourceTemporalCorrectedField event e.val sigma n j‖ := by
  rw [source_em_native_scaled_finite_return event e sigma n unit positive regular]
  unfold sourceJointNativeAgeWindow
  have equation :
      noetherPairScale^2/(2*(lapse : ℂ))*
        ((3/4 : ℂ)+sourceEMMovingDriverWindow event e sigma n T-
          sourceEMNativeBackgroundRead (sourceTemporalCorrectedField event e.val sigma n)-
          (e.val : ℂ)^2*sourceEMNativeLowerRead (frequencyRay 1 0 n)
            (sourceTemporalCorrectedField event e.val sigma n))-
      noetherPairScale^2/(2*(lapse : ℂ))*
        ((3/4 : ℂ)+dotProduct sourceTemporalEMForce (sourceTemporalActualQuantumDriver event e sigma n)-
          sourceEMNativeBackgroundRead (sourceTemporalCorrectedField event e.val sigma n)-
          (e.val : ℂ)^2*sourceEMNativeLowerRead (frequencyRay 1 0 n)
            (sourceTemporalCorrectedField event e.val sigma n)) =
      noetherPairScale^2/(2*(lapse : ℂ))*
        (sourceEMMovingDriverWindow event e sigma n T-
          dotProduct sourceTemporalEMForce (sourceTemporalActualQuantumDriver event e sigma n)) := by ring
  rw [equation,norm_mul]
  exact mul_le_mul_of_nonneg_left (source_em_moving_actual_driver_window_price event e sigma n positive T future)
    (norm_nonneg _)

end LowEnergy.GaussComposite.ActualSourcePreparedJointNativeObservation
