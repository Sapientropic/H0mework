import H0mework.NavierStokes.StressNegativeOne.Write
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

set_option autoImplicit false
open scoped Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeOriginalNegativeOneDerivative

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeOriginalNegativeOneWrite NativeResolventCompactness
open PhysicsCore.ProofFreeRicherAnholonomicSource PhysicsCore.StageNineCanonicalCauchyState
open PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

def stateAt (source : StressAt escape) (pointLe : point ≤ 1) (time : ℝ) : State :=
  state source pointLe (projIcc (0 : ℝ) 1 zero_le_one time)

theorem primitive_hasDerivAt_ae (source : StressAt escape) (pointLe : point ≤ 1) (space : StageNineSpatialPoint) :
    ∀ᵐ time : ℝ, time ∈ Icc (0 : ℝ) 1 →
      HasDerivAt (fun actual => generatedState source pointLe (canonicalCauchySlicePoint actual space))
        (action source pointLe time) time := by
  filter_upwards [(action_intervalIntegrable source pointLe).ae_hasDerivAt_integral] with time derivative
  intro inside
  have actual := derivative (by simpa only [uIcc_of_le zero_le_one] using inside) 0 (by simp)
  simpa [generatedState, canonicalTimePrimitive, profile, add_comm] using
    actual.const_add (state source pointLe ⟨0, le_rfl, zero_le_one⟩)

theorem source_hasDerivAt_ae (source : StressAt escape) (pointLe : point ≤ 1) :
    ∀ᵐ time : ℝ, time ∈ Ioo (0 : ℝ) 1 →
      HasDerivAt (stateAt source pointLe) (action source pointLe time) time := by
  filter_upwards [primitive_hasDerivAt_ae source pointLe 0] with time derivative
  intro inside
  apply (derivative ⟨inside.1.le, inside.2.le⟩).congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds inside.1 inside.2] with actual member
  simpa only [stateAt, projIcc_of_mem zero_le_one member] using
    (generatedState_original source pointLe ⟨actual, member⟩ 0).symm

theorem source_continuous (source : StressAt escape) (pointLe : point ≤ 1) :
    Continuous (state source pointLe) := by
  have primitive := intervalIntegral.continuousOn_primitive_interval' (action_intervalIntegrable source pointLe) left_mem_uIcc
  have interval := primitive.comp_continuous continuous_subtype_val (fun time => by
    simpa only [uIcc_of_le zero_le_one] using time.2)
  convert continuous_const.add interval using 1
  funext time
  exact (eq_add_of_sub_eq (source_integral source pointLe time).symm).trans (add_comm _ _)

end
end SaturationMonoid.NavierStokes.NativeOriginalNegativeOneDerivative
