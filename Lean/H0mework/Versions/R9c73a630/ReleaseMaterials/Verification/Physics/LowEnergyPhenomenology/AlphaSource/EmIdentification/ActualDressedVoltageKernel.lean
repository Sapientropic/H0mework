import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedHistoryKernel

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedHistoryKernel
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumActionFieldLift PreparationVacuumGaugeSourceInjection
open PreparationVacuumStaticVoltageSource PreparationPhysicalVoltageCompleteReturn
open ActualDressedFullCoulomb ActualDressedNoether ActualEMCauchyDynamic
open MeasureTheory Filter Set
open scoped Matrix BigOperators Topology Interval
attribute [local irreducible] dressedHistoryInitial dressedHistoryContact dressedHistoryMemory dressedNoetherJet

/-- The zero-transfer input retains the original scalar normal velocity. -/
theorem voltage_origin_real (t : ℝ) :
    (voltageNativeTimeJet (PreparationVacuumPhysicalFeedback.physicalSpatial 0) false t).value=fieldUnit 20-t • fieldUnit 8 := by
  funext i
  simp [voltageNativeTimeJet,voltageQuadrature,sourceVoltageSpatialVector,sourceVoltageTemporalVector,
    PreparationVacuumPhysicalFeedback.physicalSpatial,fieldUnit,Pi.single_apply]
  split_ifs <;> simp [sub_eq_add_neg]

theorem voltage_origin_imaginary (t : ℝ) :
    (voltageNativeTimeJet (PreparationVacuumPhysicalFeedback.physicalSpatial 0) true t).value=0 := by
  funext i
  simp [voltageNativeTimeJet,voltageQuadrature,sourceVoltageSpatialVector,sourceVoltageTemporalVector,
    PreparationVacuumPhysicalFeedback.physicalSpatial,Pi.single_apply]
  split_ifs <;> simp

/-- The true current contains both scalar-time and memory moments before reading a pole. -/
theorem dressed_voltage_origin_real_current (event : DressedEvent) (t : ℝ) (i : Fin 289) :
    (dressedNoetherJet event 0 (voltageNativeTimeJet (PreparationVacuumPhysicalFeedback.physicalSpatial 0) false) t i).value=
      dressedHistoryInitial event 0 t (fieldUnit 20) i+
        dressedHistoryContact event 0 t (fieldUnit 20-t • fieldUnit 8) i+
        ∫s in (0:ℝ)..t,dressedHistoryMemory event 0 t s (fieldUnit 20-s • fieldUnit 8) i := by
  rw [dressed_history_kernel_generated event 0 _ (voltage_timejet_continuous _ false).1]
  simp only [voltage_origin_real,zero_smul,sub_zero]

theorem dressed_voltage_origin_imaginary_current (event : DressedEvent) (t : ℝ) (i : Fin 289) :
    (dressedNoetherJet event 0 (voltageNativeTimeJet (PreparationVacuumPhysicalFeedback.physicalSpatial 0) true) t i).value=0 := by
  rw [dressed_history_kernel_generated event 0 _ (voltage_timejet_continuous _ true).1]
  simp only [voltage_origin_imaginary,map_zero,Pi.zero_apply,intervalIntegral.integral_zero,zero_add]

/-- The actual moving-source IR endpoint has a complete original-history kernel expression. -/
theorem dressed_voltage_origin_forcing (event : DressedEvent) (lambda : ℂ) (T : ℝ) :
    dressedVoltageForcing event 0 lambda T=
      fun i=>∫t in (0:ℝ)..T,laplaceWeight lambda t*
        (dressedHistoryInitial event 0 t (fieldUnit 20) i+
          dressedHistoryContact event 0 t (fieldUnit 20-t • fieldUnit 8) i+
          ∫s in (0:ℝ)..t,dressedHistoryMemory event 0 t s (fieldUnit 20-s • fieldUnit 8) i) := by
  funext i
  simp only [dressedVoltageForcing,dressedNoetherForcing,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
    dressed_voltage_origin_imaginary_current,mul_zero,intervalIntegral.integral_zero,add_zero]
  simp_rw [dressed_voltage_origin_real_current]

end LowEnergy.GaussComposite.ActualDressedHistoryKernel
