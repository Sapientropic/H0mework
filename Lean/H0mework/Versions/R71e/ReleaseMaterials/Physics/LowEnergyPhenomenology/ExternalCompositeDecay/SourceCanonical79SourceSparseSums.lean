import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79SourceSparseData
set_option autoImplicit false
noncomputable section
namespace LowEnergy.ActualCanonical79Imaginary
open scoped BigOperators

theorem source_sparse_sum_left (v : Fin 16 → ℂ) (i : Fin 79) (f : Fin 97 → ℂ) :
    (∑a : Fin 97,sourceSparseRow v i a * f a) =
      ∑s : Fin 8,sourceWeight v i s * f (sourceField i s) := by
  classical
  simp only [sourceSparseRow,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  simp

theorem source_sparse_sum_right (v : Fin 16 → ℂ) (i : Fin 79) (f : Fin 97 → ℂ) :
    (∑a : Fin 97,f a * sourceSparseRow v i a) =
      ∑s : Fin 8,f (sourceField i s) * sourceWeight v i s := by
  classical
  simp only [sourceSparseRow,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  simp

theorem source_sparse_pair (v w : Fin 16 → ℂ) (i j : Fin 79) (M : Fin 97 → Fin 97 → ℂ) :
    (∑a : Fin 97,∑b : Fin 97,sourceSparseRow v i a * M a b * sourceSparseRow w j b) =
      ∑s : Fin 8,∑t : Fin 8,sourceWeight v i s *
        M (sourceField i s) (sourceField j t) * sourceWeight w j t := by
  calc
    _ = ∑a : Fin 97,sourceSparseRow v i a *
        (∑b : Fin 97,M a b * sourceSparseRow w j b) := by
      simp only [Finset.mul_sum,mul_assoc]
    _ = ∑a : Fin 97,sourceSparseRow v i a *
        (∑t : Fin 8,M a (sourceField j t) * sourceWeight w j t) := by
      simp_rw [source_sparse_sum_right]
    _ = ∑s : Fin 8,sourceWeight v i s *
        (∑t : Fin 8,M (sourceField i s) (sourceField j t) * sourceWeight w j t) :=
      source_sparse_sum_left v i _
    _ = _ := by simp only [Finset.mul_sum,mul_assoc]

end LowEnergy.ActualCanonical79Imaginary
