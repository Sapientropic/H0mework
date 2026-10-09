import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def effectRoot (E : Matrix ι ι ℂ) : Matrix ι ι ℂ := CFC.sqrt E
def complementRoot (E : Matrix ι ι ℂ) : Matrix ι ι ℂ := CFC.sqrt (1 - E)

theorem effectRoot_positive (E : Matrix ι ι ℂ) : (effectRoot E).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg E)

theorem complementRoot_positive (E : Matrix ι ι ℂ) : (complementRoot E).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (1 - E))

theorem effectRoot_square (E : Matrix ι ι ℂ) (positive : E.PosSemidef) :
    effectRoot E * effectRoot E = E := CFC.sqrt_mul_sqrt_self E positive.nonneg

theorem complementRoot_square (E : Matrix ι ι ℂ) (positive : (1 - E).PosSemidef) :
    complementRoot E * complementRoot E = 1 - E :=
  CFC.sqrt_mul_sqrt_self (1 - E) positive.nonneg

theorem roots_commute (E : Matrix ι ι ℂ) : Commute (effectRoot E) (complementRoot E) := by
  have base : Commute E (1 - E) := (Commute.one_right E).sub_right (Commute.refl E)
  unfold effectRoot complementRoot
  rw [CFC.sqrt_eq_cfc, CFC.sqrt_eq_cfc]
  exact ((base.cfc_nnreal NNReal.sqrt).symm.cfc_nnreal NNReal.sqrt).symm

def dilationMatrix (E : Matrix ι ι ℂ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  Matrix.fromBlocks (effectRoot E) (-complementRoot E) (complementRoot E) (effectRoot E)

theorem dilationMatrix_adjoint (E : Matrix ι ι ℂ) :
    (dilationMatrix E)ᴴ =
      Matrix.fromBlocks (effectRoot E) (complementRoot E) (-complementRoot E) (effectRoot E) := by
  rw [dilationMatrix, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_neg,
    (effectRoot_positive E).isHermitian.eq, (complementRoot_positive E).isHermitian.eq]

theorem dilationMatrix_mul_adjoint (E : Matrix ι ι ℂ) (positive : E.PosSemidef)
    (complementPositive : (1 - E).PosSemidef) :
    dilationMatrix E * (dilationMatrix E)ᴴ = 1 := by
  rw [dilationMatrix_adjoint, dilationMatrix, Matrix.fromBlocks_multiply]
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, effectRoot_square E positive,
    complementRoot_square E complementPositive, (roots_commute E).eq]
  simp [Matrix.fromBlocks_one]

theorem dilationMatrix_adjoint_mul (E : Matrix ι ι ℂ) (positive : E.PosSemidef)
    (complementPositive : (1 - E).PosSemidef) :
    (dilationMatrix E)ᴴ * dilationMatrix E = 1 := by
  rw [dilationMatrix_adjoint, dilationMatrix, Matrix.fromBlocks_multiply]
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, effectRoot_square E positive,
    complementRoot_square E complementPositive, (roots_commute E).eq]
  simp [Matrix.fromBlocks_one]

def dilation (E : Matrix ι ι ℂ) (positive : E.PosSemidef)
    (complementPositive : (1 - E).PosSemidef) : Matrix.unitaryGroup (ι ⊕ ι) ℂ :=
  ⟨dilationMatrix E, by
    constructor
    · exact dilationMatrix_adjoint_mul E positive complementPositive
    · exact dilationMatrix_mul_adjoint E positive complementPositive⟩

def prepared (rho : Matrix ι ι ℂ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  Matrix.fromBlocks rho 0 0 0

theorem dilation_prepared_blocks (E rho : Matrix ι ι ℂ) :
    dilationMatrix E * prepared rho * (dilationMatrix E)ᴴ =
      Matrix.fromBlocks
        (effectRoot E * rho * effectRoot E) (effectRoot E * rho * complementRoot E)
        (complementRoot E * rho * effectRoot E) (complementRoot E * rho * complementRoot E) := by
  rw [dilationMatrix_adjoint, dilationMatrix, prepared, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
