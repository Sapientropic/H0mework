import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.LoadCost

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Collision Load.Source Propagation.Producer
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

/-- Both actual pointer branches, the original source input, and the source clock enter this budget. -/
theorem original_net_PC_norm : ‖gainObservable Sectors.pointerPCObservable‖ ≤ (123/1000 : ℝ) := by
  have sum : loadResponseCost+max loadResponseCost exchangeResponseCost ≤ 281 := by
    have bound : max loadResponseCost exchangeResponseCost ≤ 180 := max_le
      (original_load_cost.trans (by norm_num)) original_exchange_cost
    linarith [original_load_cost]
  apply original_net_PC_response.trans
  have paid := mul_le_mul_of_nonneg_left sum Load.Producer.StrictThermal.nativeClock_small.1.le
  apply paid.trans
  rw [nativeClockStep_exact]
  norm_num

theorem original_PC_gain_finite_error :
    |(Resource.pcEnergyOf (bodyRead Weak.execution.joint)-Resource.pcEnergyOf (bodyRead Weak.origin.joint))-
      (Resource.pcEnergyOf (bodyRead (approximatedEleven originalFrameNumericOutput original_frame_numeric_hermitian))-
       Resource.pcEnergyOf (bodyRead (approximatedNine originalFrameNumericOutput original_frame_numeric_hermitian)))| ≤
      (7/10^6 : ℝ) := by
  exact original_PC_gain_instrument_error.trans (by nlinarith [original_net_PC_norm])

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
