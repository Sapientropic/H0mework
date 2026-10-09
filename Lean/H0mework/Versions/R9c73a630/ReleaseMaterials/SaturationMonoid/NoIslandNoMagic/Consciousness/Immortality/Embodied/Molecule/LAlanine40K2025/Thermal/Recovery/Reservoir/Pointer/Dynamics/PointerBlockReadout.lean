import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Dynamics.BinaryPointerDilation
import H0mework.Chemistry.LAlanineThermalDynamics.PartialSwapEnergyPopulation

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer

open scoped Matrix ComplexOrder
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def zeroRead (joint : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) : ℝ := joint.toBlocks₁₁.trace.re
def oneRead (joint : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) : ℝ := joint.toBlocks₂₂.trace.re
def bodyRead (joint : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) : Matrix ι ι ℂ := joint.toBlocks₁₁ + joint.toBlocks₂₂

omit [Fintype ι] [DecidableEq ι] in
theorem prepared_bodyRead (rho : Matrix ι ι ℂ) : bodyRead (prepared rho) = rho := by
  simp [bodyRead, prepared]

theorem pointer_zero_read (E rho : Matrix ι ι ℂ) (positive : E.PosSemidef) :
    zeroRead (dilationMatrix E * prepared rho * (dilationMatrix E)ᴴ) = Collision.energy E rho := by
  rw [dilation_prepared_blocks, zeroRead, Matrix.toBlocks_fromBlocks₁₁]
  rw [Matrix.trace_mul_cycle, effectRoot_square E positive]
  rfl

theorem pointer_one_read (E rho : Matrix ι ι ℂ) (positive : (1 - E).PosSemidef) :
    oneRead (dilationMatrix E * prepared rho * (dilationMatrix E)ᴴ) = Collision.energy (1 - E) rho := by
  rw [dilation_prepared_blocks, oneRead, Matrix.toBlocks_fromBlocks₂₂]
  rw [Matrix.trace_mul_cycle, complementRoot_square E positive]
  rfl

theorem bodyRead_backreaction (E rho : Matrix ι ι ℂ) :
    bodyRead (dilationMatrix E * prepared rho * (dilationMatrix E)ᴴ) =
      effectRoot E * rho * effectRoot E + complementRoot E * rho * complementRoot E := by
  rw [dilation_prepared_blocks, bodyRead, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₂₂]

theorem pointer_binary_sum (E rho : Matrix ι ι ℂ) (positive : E.PosSemidef)
    (complement : (1 - E).PosSemidef) (normalized : rho.trace = 1) :
    zeroRead (dilationMatrix E * prepared rho * (dilationMatrix E)ᴴ) +
      oneRead (dilationMatrix E * prepared rho * (dilationMatrix E)ᴴ) = 1 := by
  rw [pointer_zero_read E rho positive, pointer_one_read E rho complement]
  simp only [Collision.energy, Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, normalized,
    Complex.sub_re, Complex.one_re]
  ring

omit [DecidableEq ι] in
theorem zeroRead_nonnegative (joint : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) (positive : joint.PosSemidef) :
    0 ≤ zeroRead joint :=
  (Complex.nonneg_iff.mp ((positive.submatrix Sum.inl).trace_nonneg)).1

omit [DecidableEq ι] in
theorem oneRead_nonnegative (joint : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) (positive : joint.PosSemidef) :
    0 ≤ oneRead joint :=
  (Complex.nonneg_iff.mp ((positive.submatrix Sum.inr).trace_nonneg)).1

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
