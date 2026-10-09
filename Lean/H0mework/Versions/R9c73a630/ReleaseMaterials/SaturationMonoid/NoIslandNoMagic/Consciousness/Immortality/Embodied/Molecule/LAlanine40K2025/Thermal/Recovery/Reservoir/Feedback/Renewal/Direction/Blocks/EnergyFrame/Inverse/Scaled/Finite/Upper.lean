import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Factors.Block0Minus
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Factors.Block0Plus
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Factors.Block1Minus
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Factors.Block1Plus
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Factors.Block2Minus
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Factors.Block2Plus
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Factors.Block3Minus
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Factors.Block3Plus
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Factors.Block4Minus
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Factors.Block4Plus
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.FactorBound
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Hermitian

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite
open RationalMatrix
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem block0_norm_upper : ‖block0‖ ≤ (480362644764/10^10 : ℝ) := by
  rw [← rational_block0]
  simpa only [Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] using norm_from_rational_factors real0 imag0
    Factors.Block0Minus.realFactor Factors.Block0Minus.imagFactor
    Factors.Block0Plus.realFactor Factors.Block0Plus.imagFactor
    (480362644764/10^10) (1/10^12)
    (cast_hermitian _ _ (by decide +kernel) (by decide +kernel))
    (by norm_num) (by norm_num) Factors.Block0Minus.checked Factors.Block0Plus.checked

theorem block1_norm_upper : ‖block1‖ ≤ (480362644764/10^10 : ℝ) := by
  rw [← rational_block1]
  simpa only [Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] using norm_from_rational_factors real1 imag1
    Factors.Block1Minus.realFactor Factors.Block1Minus.imagFactor
    Factors.Block1Plus.realFactor Factors.Block1Plus.imagFactor
    (480362644764/10^10) (1/10^12)
    (cast_hermitian _ _ (by decide +kernel) (by decide +kernel))
    (by norm_num) (by norm_num) Factors.Block1Minus.checked Factors.Block1Plus.checked

theorem block2_norm_upper : ‖block2‖ ≤ (480362644764/10^10 : ℝ) := by
  rw [← rational_block2]
  simpa only [Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] using norm_from_rational_factors real2 imag2
    Factors.Block2Minus.realFactor Factors.Block2Minus.imagFactor
    Factors.Block2Plus.realFactor Factors.Block2Plus.imagFactor
    (480362644764/10^10) (1/10^12)
    (cast_hermitian _ _ (by decide +kernel) (by decide +kernel))
    (by norm_num) (by norm_num) Factors.Block2Minus.checked Factors.Block2Plus.checked

theorem block3_norm_upper : ‖block3‖ ≤ (480362644764/10^10 : ℝ) := by
  rw [← rational_block3]
  simpa only [Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] using norm_from_rational_factors real3 imag3
    Factors.Block3Minus.realFactor Factors.Block3Minus.imagFactor
    Factors.Block3Plus.realFactor Factors.Block3Plus.imagFactor
    (480362644764/10^10) (1/10^12)
    (cast_hermitian _ _ (by decide +kernel) (by decide +kernel))
    (by norm_num) (by norm_num) Factors.Block3Minus.checked Factors.Block3Plus.checked

theorem block4_norm_upper : ‖block4‖ ≤ (480362644764/10^10 : ℝ) := by
  rw [← rational_block4]
  simpa only [Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] using norm_from_rational_factors real4 imag4
    Factors.Block4Minus.realFactor Factors.Block4Minus.imagFactor
    Factors.Block4Plus.realFactor Factors.Block4Plus.imagFactor
    (480362644764/10^10) (1/10^12)
    (cast_hermitian _ _ (by decide +kernel) (by decide +kernel))
    (by norm_num) (by norm_num) Factors.Block4Minus.checked Factors.Block4Plus.checked

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
