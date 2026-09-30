import H0mework.Chemistry.LAlanineElectronicFrame.ProducerSourceGeneratedSCFProjectionGap
import H0mework.Chemistry.LAlanineElectronicFrame.DynamicsPolarFrameTransportError

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.ElectronicFrame.Producer

open Propagation.Interface
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem matrix_entry_norm_le (A : Matrix Basis Basis ℂ) (i j : Basis) : ‖A i j‖ ≤ ‖A‖ := by
  let e : EuclideanSpace ℂ Basis := PiLp.single 2 j 1
  let T := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Basis) A
  have entry : (T e).ofLp i = A i j := by
    change (A *ᵥ Pi.single j 1) i = A i j
    simp only [Matrix.mulVec_single_one, Matrix.col_apply]
  calc
    _ = ‖(T e).ofLp i‖ := congrArg norm entry.symm
    _ ≤ ‖T e‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖T‖ * ‖e‖ := T.le_opNorm e
    _ = ‖A‖ := by simp only [e, PiLp.norm_single, norm_one, mul_one]; rfl

theorem heldTransport_error_small :
    ‖Source.heldStateTransport heldMatrix - Source.crossMatrix * heldMatrix * star Source.crossMatrix‖ <
      (6 : ℝ) / 10 ^ 10 := by
  have bound := Polar.transport_error_le_close Source.crossMatrix heldMatrix Source.crossMatrix_close
  change ‖Source.heldStateTransport heldMatrix - Source.crossMatrix * heldMatrix * star Source.crossMatrix‖ ≤ _ at bound
  apply bound.trans_lt
  calc
    _ ≤ ‖star Source.crossMatrix * Source.crossMatrix - 1‖ * 10 * 3 := by
      gcongr
      · exact heldMatrix_norm_le_ten
      · linarith [Source.crossMatrix_close]
    _ < _ := by nlinarith [Source.gram_norm_small]

/-- The raw single-coordinate separation exceeds the independently bounded polar correction. -/
theorem heldState_transport_not_scfReset : Source.heldStateTransport heldMatrix ≠ scfBenchmark := by
  intro same
  have error := heldTransport_error_small
  rw [same, norm_sub_rev] at error
  have entry := matrix_entry_norm_le
    (Source.crossMatrix * heldMatrix * star Source.crossMatrix - scfBenchmark) 19 19
  have gap := rawProjection_entry_gap
  linarith

end
end LAlanine40K2025.ElectronicFrame.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
