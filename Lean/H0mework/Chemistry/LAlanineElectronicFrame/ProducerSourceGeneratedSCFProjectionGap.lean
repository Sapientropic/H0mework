import H0mework.Chemistry.LAlanineElectronicFrame.ProducerSourceGeneratedHeldElectronicMatrix

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.ElectronicFrame.Producer

open Propagation.Interface
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def projectionNumerator : Int :=
  (∑ j : Basis, ∑ i : Basis, Source.crossNumerator 19 i * heldNumerator i j * Source.crossNumerator 19 j) -
    scfNumerator 19 19 * 10 ^ 30

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem projectionNumerator_exact :
    projectionNumerator = -1124010508271092953183232264483601 := by decide

attribute [local irreducible] Source.crossNumerator heldNumerator scfNumerator heldMatrix scfBenchmark

private theorem projectionTerm (i j : Basis) :
    (Source.crossMatrix 19 i * heldMatrix i j) * star (Source.crossMatrix 19 j) =
      ((Source.crossNumerator 19 i * heldNumerator i j * Source.crossNumerator 19 j : Int) : ℂ) / 10 ^ 42 := by
  rw [held_entry]
  simp only [Source.crossMatrix, Int.cast_mul]
  norm_num
  ring

theorem rawProjection_difference_entry :
    (Source.crossMatrix * heldMatrix * star Source.crossMatrix - scfBenchmark) 19 19 =
      (projectionNumerator : ℂ) / 10 ^ 42 := by
  have projected : (Source.crossMatrix * heldMatrix * star Source.crossMatrix) 19 19 =
      ((∑ j : Basis, ∑ i : Basis,
        Source.crossNumerator 19 i * heldNumerator i j * Source.crossNumerator 19 j : Int) : ℂ) / 10 ^ 42 := by
    change (∑ j : Basis, (∑ i : Basis, Source.crossMatrix 19 i * heldMatrix i j) *
      star (Source.crossMatrix 19 j)) = _
    simp only [Finset.sum_mul, projectionTerm, Int.cast_sum, Finset.sum_div]
  change (Source.crossMatrix * heldMatrix * star Source.crossMatrix) 19 19 - scfBenchmark 19 19 = _
  rw [projected, scf_entry]
  simp only [projectionNumerator, Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
  ring

theorem rawProjection_entry_gap :
    (1 : ℝ) / 10 ^ 9 < ‖(Source.crossMatrix * heldMatrix * star Source.crossMatrix - scfBenchmark) 19 19‖ := by
  rw [rawProjection_difference_entry, projectionNumerator_exact]
  norm_num [norm_div, Complex.norm_intCast]

end
end LAlanine40K2025.ElectronicFrame.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
