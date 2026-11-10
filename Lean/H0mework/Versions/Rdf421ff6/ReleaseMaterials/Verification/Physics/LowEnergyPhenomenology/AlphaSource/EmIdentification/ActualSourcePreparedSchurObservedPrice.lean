import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedSchurClockPrice
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedJointNativeObservation

set_option autoImplicit false
set_option maxHeartbeats 240000
set_option maxRecDepth 1024
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedSchurObservedPrice
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalCharacteristic ActualDressedFullCoulomb ActualDressedCorrectedGreen
open ActualDressedNoetherCoulombUnit ActualSourcePreparedN3EMChargeRead
open ActualSourcePreparedTemporalEMConstraint ActualSourcePreparedJointNativeObservation
open ActualSourcePreparedTemporalQuantumWard ActualSourcePreparedTemporalQuantumIR
open ActualSourcePreparedSchurClockPrice ActualSourcePreparedN3EMAnalyticPrice
open LowEnergy.ActualDressedVisiblePole
open SaturationMonoid.PhysicsCore Stage9C.Material.SpinPair
open PreparationVacuumActionFieldLift
open scoped BigOperators
attribute [local irreducible] sourceJointNativeAgeWindow sourceTemporalCorrectedField
  sourceSchurDampingFraction sourceN3TemporalEMCoefficient

def sourceSchurClockCoefficientPrincipal (event : DressedEvent) (n : PhysicalMomentum)
    (eps sigma : ℝ) : ℂ :=
  let R := sourceSchurDampingFraction event n eps
  noetherPairScale^2/(2*(lapse : ℂ))*((3/4 : ℂ)+
    (principalNumerator R 0).eval (sigma : ℂ)/(sigma : ℂ)^poleOrder R 0+sourceEMAnalyticCenter R)

/-- Actual finite-age endpoint and prepared tails, plus the full source clock
remainder. Every field column norm and all three observation scales remain. -/
def sourceSchurObservedError (event : DressedEvent) (e : scaleDomain)
    (sigma : ℝ) (n : PhysicalMomentum) (T : ℝ) : ℝ :=
  ‖noetherPairScale^2/(2*(lapse : ℂ))‖*
    ((∑j : Fin 289, (Real.exp (-sigma*T)*ActualDressedEMTemporal.emTemporalPrice
        event (e.val^2 • n) (fieldUnit j)*(1+T)+
        ‖(sigma : ℂ)‖*(∑i : Fin 289,‖((PreparationPhysicalPhaseGaugeRealization.sourcePhaseGaugeField 0) i : ℂ)‖)*
          ActualDressedSignal.dressedSignalTailPrice event (e.val^2 • n) (0 : Fin 4 → ℂ) (sigma : ℂ) T)*
        ‖sourceTemporalCorrectedField event e.val sigma n j‖)+
      sourceEMAnalyticSlope (sourceSchurDampingFraction event n e.val)*‖(sigma : ℂ)‖)

private theorem two_errors (w t a : ℂ) (u v : ℝ)
    (age : ‖w-t‖ ≤ u) (clock : ‖t-a‖ ≤ v) : ‖w-a‖ ≤ u+v := by
  calc
    ‖w-a‖ = ‖(w-t)+(t-a)‖ := by congr 1; ring
    _ ≤ ‖w-t‖+‖t-a‖ := norm_add_le _ _
    _ ≤ u+v := add_le_add age clock

/-- A single source disk encloses the original configuration's finite-age
observation by its complete clock principal and generated analytic center. -/
theorem source_schur_actual_observation_price (event : DressedEvent) (e : scaleDomain)
    (sigma : ℝ) (n : PhysicalMomentum) (unit : spatialSquare n=1) (positive : 0<sigma)
    (regular : correctedDet event e.val 0 sigma n≠0) (T : ℝ) (future : 0 ≤ T)
    (small : ‖(sigma : ℂ)‖ ≤ sourceEMAnalyticRadius (sourceSchurDampingFraction event n e.val)) :
    0<sourceEMAnalyticRadius (sourceSchurDampingFraction event n e.val) ∧
    ‖sourceJointNativeAgeWindow event e sigma n T-sourceSchurClockCoefficientPrincipal event n e.val sigma‖ ≤
      sourceSchurObservedError event e sigma n T := by
  have age := source_joint_native_age_window_price event e sigma n unit positive regular T future
  have clock := source_em_full_clock_coefficient_price event e sigma n unit positive regular small
  refine ⟨clock.1, ?_⟩
  have joined := two_errors _ _ _ _ _ age clock.2
  simpa only [sourceSchurClockCoefficientPrincipal,sourceSchurObservedError,mul_add] using joined

end LowEnergy.GaussComposite.ActualSourcePreparedSchurObservedPrice
