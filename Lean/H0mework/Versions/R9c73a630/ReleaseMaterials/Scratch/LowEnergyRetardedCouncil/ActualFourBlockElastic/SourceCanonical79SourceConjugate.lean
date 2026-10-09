import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceCanonical79SourceSparseRows
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
noncomputable section
namespace LowEnergy.ActualCanonical79Imaginary
open scoped BigOperators
attribute [local irreducible] sourceSchema

private theorem source_weight_star (v : Fin 16 → ℂ) (i : Fin 79) (s : Fin 8) :
    sourceWeight (fun n => star (v n)) i s = star (sourceWeight v i s) := by
  fin_cases i <;> fin_cases s <;> first | rfl | exact (star_zero ℂ).symm

theorem actual_source_polynomial_star (a : Fin 16) :
    sourcePolynomialPoint true a = star (sourcePolynomialPoint false a) := by
  fin_cases a <;> norm_num [sourcePolynomialPoint]

theorem actual_source_point_star (i : Fin 79) (a : Fin 97) :
    sourceMapPoint true i a = star (sourceMapPoint false i a) := by
  have h : sourcePolynomialPoint true = fun n => star (sourcePolynomialPoint false n) :=
    funext actual_source_polynomial_star
  change sourceSchema (sourcePolynomialPoint true) i a =
    star (sourceSchema (sourcePolynomialPoint false) i a)
  rw [actual_source_sparse_rows,actual_source_sparse_rows,h]
  simp only [sourceSparseRow,star_sum]
  apply Finset.sum_congr rfl
  intro s _
  split_ifs <;> simp only [source_weight_star,star_zero]

theorem conjugate_source_current (L : Fin 79 → Fin 97 → ℂ)
    (M : Fin 97 → Fin 97 → ℂ) (hM : ∀a b,M a b = M b a) (i j : Fin 79) :
    (∑a : Fin 97,∑b : Fin 97,star (L i a) * star (M a b) * L j b) =
      star (∑a : Fin 97,∑b : Fin 97,star (L j a) * M a b * L i b) := by
  simp only [star_sum,star_mul,star_star]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [hM b a]
  ring

end LowEnergy.ActualCanonical79Imaginary
