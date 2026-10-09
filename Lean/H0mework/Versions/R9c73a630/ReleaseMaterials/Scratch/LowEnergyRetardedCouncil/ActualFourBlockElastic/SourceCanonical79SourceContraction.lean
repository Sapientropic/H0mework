import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceCanonical79SourceSparseSums
set_option autoImplicit false
noncomputable section
namespace LowEnergy.ActualCanonical79Imaginary
open scoped BigOperators

private theorem sum_exchange (f : Fin 97 → Fin 97 → Fin 79 → Fin 79 → ℂ) :
    (∑a : Fin 97,∑b : Fin 97,∑i : Fin 79,∑j : Fin 79,f a b i j) =
      ∑i : Fin 79,∑j : Fin 79,∑a : Fin 97,∑b : Fin 97,f a b i j := by
  calc
    _ = ∑a : Fin 97,∑i : Fin 79,∑b : Fin 97,∑j : Fin 79,f a b i j := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑i : Fin 79,∑a : Fin 97,∑b : Fin 97,∑j : Fin 79,f a b i j := Finset.sum_comm
    _ = ∑i : Fin 79,∑a : Fin 97,∑j : Fin 79,∑b : Fin 97,f a b i j := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm

theorem source_coefficient_pair_contraction
    (L R : Fin 79 → Fin 97 → ℂ) (G : Fin 79 → Fin 79 → ℂ)
    (M : Fin 97 → Fin 97 → ℂ) :
    (∑a : Fin 97,∑b : Fin 97,
      ((-1/2 : ℂ)*(∑i : Fin 79,∑j : Fin 79,L i a * G i j * R j b))*M a b) =
      ∑i : Fin 79,∑j : Fin 79,((-1/2 : ℂ)*G i j)*
        (∑a : Fin 97,∑b : Fin 97,L i a * M a b * R j b) := by
  simp only [Finset.mul_sum,Finset.sum_mul]
  rw [sum_exchange]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

end LowEnergy.ActualCanonical79Imaginary
