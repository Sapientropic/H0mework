import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.OneBody
import Mathlib.LinearAlgebra.Matrix.SchurComplement

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody
open scoped Matrix BigOperators
noncomputable section

private def selectRows (a b : Fin 48) : Matrix (Fin 48) (Fin 2) ℂ :=
  fun i k => if k = 0 then if i = a then 1 else 0 else if i = b then 1 else 0

private def rowDeviation (a b : Fin 48) (u v : Fin 48 → ℂ) :
    Matrix (Fin 2) (Fin 48) ℂ :=
  fun k j => if k = 0 then u j - (1 : Matrix (Fin 48) (Fin 48) ℂ) a j
    else v j - (1 : Matrix (Fin 48) (Fin 48) ℂ) b j

theorem det_double_update_one (a b : Fin 48) (different : a ≠ b)
    (u v : Fin 48 → ℂ) :
    (((1 : Matrix (Fin 48) (Fin 48) ℂ).updateRow a u).updateRow b v).det =
      u a * v b - u b * v a := by
  let U := selectRows a b
  let V := rowDeviation a b u v
  have matrixIdentity :
      ((1 : Matrix (Fin 48) (Fin 48) ℂ).updateRow a u).updateRow b v =
        1 + U * V := by
    ext i j
    by_cases ia : i = a
    · subst i
      simp [U,V,selectRows,rowDeviation,Matrix.updateRow_apply,
        Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply,different]
    · by_cases ib : i = b
      · subst i
        simp [U,V,selectRows,rowDeviation,Matrix.updateRow_apply,
          Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply,different.symm]
      · simp [U,V,selectRows,rowDeviation,Matrix.updateRow_apply,
          Matrix.mul_apply,Matrix.one_apply,ia,ib]
  rw [matrixIdentity,Matrix.det_one_add_mul_comm]
  rw [Matrix.det_fin_two]
  simp [U,V,selectRows,rowDeviation,Matrix.mul_apply,Matrix.one_apply,
    different,different.symm]

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
