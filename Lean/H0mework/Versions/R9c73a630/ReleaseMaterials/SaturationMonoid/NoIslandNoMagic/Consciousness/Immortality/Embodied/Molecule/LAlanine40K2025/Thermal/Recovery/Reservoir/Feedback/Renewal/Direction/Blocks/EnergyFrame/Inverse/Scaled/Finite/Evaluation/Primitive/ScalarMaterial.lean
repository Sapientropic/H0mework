import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.ScalarSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Diagonal.Certificate

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive

structure ScalarMaterial (energy : ℚ) where
  one : Scalar.QComplex
  two : Scalar.QComplex
  three : Scalar.QComplex
  one_error : Scalar.distance (Scalar.polynomial (scalarSeed energy 1) 14) one ≤ (1/10^24 : ℚ)
  two_error : Scalar.distance (Scalar.polynomial (scalarSeed energy 2) 14) two ≤ (1/10^24 : ℚ)
  three_error : Scalar.distance (Scalar.polynomial (scalarSeed energy 3) 14) three ≤ (1/10^24 : ℚ)

theorem material_one_error (energy : ℚ) (M : ScalarMaterial energy) :
    ‖Scalar.value (Scalar.polynomial (scalarSeed energy 1) 14)-Scalar.value M.one‖ ≤ (1/10^24 : ℝ) :=
  (Scalar.value_distance _ _).trans (by simpa only [Rat.cast_div,Rat.cast_pow,Rat.cast_one,Rat.cast_ofNat] using Diagonal.rational_order M.one_error)

theorem material_two_error (energy : ℚ) (M : ScalarMaterial energy) :
    ‖Scalar.value (Scalar.polynomial (scalarSeed energy 2) 14)-Scalar.value M.two‖ ≤ (1/10^24 : ℝ) :=
  (Scalar.value_distance _ _).trans (by simpa only [Rat.cast_div,Rat.cast_pow,Rat.cast_one,Rat.cast_ofNat] using Diagonal.rational_order M.two_error)

theorem material_three_error (energy : ℚ) (M : ScalarMaterial energy) :
    ‖Scalar.value (Scalar.polynomial (scalarSeed energy 3) 14)-Scalar.value M.three‖ ≤ (1/10^24 : ℝ) :=
  (Scalar.value_distance _ _).trans (by simpa only [Rat.cast_div,Rat.cast_pow,Rat.cast_one,Rat.cast_ofNat] using Diagonal.rational_order M.three_error)

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
