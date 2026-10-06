import H0mework.Versions.AD.Checks.Physics.IndependentBell.NistReal.NominalReplay.ObservableClosure.EnvironmentSource.Environmentsource

set_option autoImplicit false

namespace P23.EnvironmentSource.Consumer

open Matrix
open P23.GaussianWindow.NativeEffects
open scoped BigOperators ComplexOrder
noncomputable section

def densityBorn {I : Type*} [Fintype I] (E rho : Matrix I I ℂ) : ℂ :=
  Matrix.trace (E * rho)

def finitePhiBorn {I : Type*} [Fintype I] (E : Matrix I I ℂ) (phi : I → ℂ) : ℂ :=
  star phi ⬝ᵥ (E *ᵥ phi)

theorem gram_finitePhi {I J : Type*} [Fintype I] [Fintype J]
    (ports : Matrix J I ℂ) (phi : I → ℂ) :
    finitePhiBorn (portsᴴ * ports) phi =
      star (ports *ᵥ phi) ⬝ᵥ (ports *ᵥ phi) := by
  rw [finitePhiBorn, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_conjTranspose, star_star]

theorem density_probability_sum (s : EnvironmentPrim) (a : ℝ) (rho : Matrix Bool Bool ℂ) :
    densityBorn (clickedGram s a) rho + densityBorn (noClickGram s a) rho = Matrix.trace rho := by
  rw [densityBorn, densityBorn, ← Matrix.trace_add, ← Matrix.add_mul, click_noClick_sum,
    Matrix.one_mul]

theorem onePhoton_density_generated (s : EnvironmentPrim) (a : ℝ)
    (rho : Matrix Bool Bool ℂ) :
    densityBorn (clickedGram s a) rho = densityBorn (clickedFormula s a) rho ∧
      densityBorn (noClickGram s a) rho = densityBorn (1 - clickedFormula s a) rho := by
  constructor
  · rw [clickedGram_formula]
  · rw [noClick_complement, clickedGram_formula]

theorem onePhoton_finitePhi_generated (s : EnvironmentPrim) (a : ℝ) (phi : Bool → ℂ) :
    finitePhiBorn (clickedGram s a) phi =
        star (clickedRows s a *ᵥ phi) ⬝ᵥ (clickedRows s a *ᵥ phi) ∧
      finitePhiBorn (noClickGram s a) phi =
        star (noClickRows s a *ᵥ phi) ⬝ᵥ (noClickRows s a *ᵥ phi) :=
  ⟨gram_finitePhi (clickedRows s a) phi, gram_finitePhi (noClickRows s a) phi⟩

theorem number_density_generated (s : EnvironmentPrim) (a : ℝ) (n : ℕ)
    (rho : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    densityBorn (gamma s a n) rho =
      densityBorn ((numberPorts s a n)ᴴ * numberPorts s a n) rho := by
  rw [gamma_port_born]

theorem number_finitePhi_generated (s : EnvironmentPrim) (a : ℝ) (n : ℕ)
    (phi : Fin (n + 1) → ℂ) :
    finitePhiBorn (gamma s a n) phi =
      star (numberPorts s a n *ᵥ phi) ⬝ᵥ (numberPorts s a n *ᵥ phi) := by
  rw [gamma_port_born]
  exact gram_finitePhi (numberPorts s a n) phi

theorem environment_source_consumer (s : EnvironmentPrim) (a : ℝ)
    (rho : Matrix Bool Bool ℂ) :
    (occupiedColumns s)ᴴ * occupiedColumns s = 1 ∧
      (sixPorts s a)ᴴ * sixPorts s a = 1 ∧
      clickedGram s a = clickedFormula s a ∧
      noClickGram s a = 1 - clickedFormula s a ∧
      (noClickGram s a).PosSemidef ∧ (1 - noClickGram s a).PosSemidef ∧
      densityBorn (clickedGram s a) rho + densityBorn (noClickGram s a) rho = Matrix.trace rho ∧
      ∀ n : ℕ,
        gamma s a n = (numberPorts s a n)ᴴ * numberPorts s a n ∧
        (gamma s a n).PosSemidef ∧ (1 - gamma s a n).PosSemidef ∧
        (wordTensor (sixPorts s a) n * occupation n)ᴴ *
          (wordTensor (sixPorts s a) n * occupation n) = 1 ∧
        ∀ phi : Fin (n + 1) → ℂ,
          finitePhiBorn (gamma s a n) phi =
            star (numberPorts s a n *ᵥ phi) ⬝ᵥ (numberPorts s a n *ᵥ phi) := by
  refine ⟨occupiedColumns_isometry s, sixPorts_gram s a, clickedGram_formula s a, ?_,
    (onePhoton_bounds s a).1, (onePhoton_bounds s a).2, density_probability_sum s a rho, ?_⟩
  · rw [noClick_complement, clickedGram_formula]
  · intro n
    exact ⟨gamma_port_born s a n, (gamma_bounds s a n).1, (gamma_bounds s a n).2,
      allPorts_number_isometry s a n, number_finitePhi_generated s a n⟩

theorem rankOne_limit_consumer (s : EnvironmentPrim) (a : ℝ) (hxi : s.xi = 1)
    (rho : Matrix Bool Bool ℂ) :
    densityBorn (noClickGram s a) rho = densityBorn (onePhotonEffect s.detector a) rho ∧
      ∀ n : ℕ, gamma s a n = P23.GaussianWindow.NativeEffects.gamma s.detector a n := by
  refine ⟨?_, fun n => rankOne_gamma s a n hxi⟩
  rw [rankOne_noClick s a hxi]

end
end P23.EnvironmentSource.Consumer
