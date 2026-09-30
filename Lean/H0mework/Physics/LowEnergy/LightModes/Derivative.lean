import H0mework.Physics.LowEnergy.LightModes.Wave
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! The exact source factor has a nonzero complex time derivative at each
generated root. This supplies the simple-pole input from the source itself. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.LightModes
noncomputable section

def squaredPolynomial (branch : Branch) (w : ℝ) : Polynomial ℝ :=
  sourceFactor branch Polynomial.X (Polynomial.C w)

theorem squared_polynomial_eval (branch : Branch) (w v : ℝ) :
    (squaredPolynomial branch w).eval v=sourceFactor branch v w := by
  cases branch <;> simp [squaredPolynomial,sourceFactor] <;> ring

theorem squared_derivative_nonzero (branch : Branch) (w : ℝ)
    (small : |w|≤(sourceRoot branch).radius) (nonzero : w≠0) :
    (squaredPolynomial branch w).derivative.eval (w^(sourcePower branch)*(sourceRoot branch).root w)≠0 := by
  have source := source_root_simple branch w small nonzero
  have generated := ((squaredPolynomial branch w).hasDerivAt
    (w^(sourcePower branch)*(sourceRoot branch).root w)).comp ((sourceRoot branch).root w)
      ((hasDerivAt_id ((sourceRoot branch).root w)).const_mul (w^(sourcePower branch)))
  simp only [squared_polynomial_eval,Function.comp_def,mul_one] at generated
  have same := source.1.unique generated
  intro zero
  rw [zero,zero_mul] at same
  exact source.2 same

def complexSquaredPolynomial (branch : Branch) (w : ℝ) : Polynomial ℂ :=
  (squaredPolynomial branch w).map Complex.ofRealHom

theorem complex_squared_eval (branch : Branch) (w : ℝ) (v : ℂ) :
    (complexSquaredPolynomial branch w).eval v=sourceFactor branch v (w : ℂ) := by
  cases branch <;> simp [complexSquaredPolynomial,squaredPolynomial,sourceFactor] <;> ring

theorem source_complex_simple (branch : Branch) (q : ℝ) (small : |q|≤momentumRadius) (nonzero : q≠0) :
    HasDerivAt (fun z : ℂ => sourceFactor branch (z^2) ((q : ℂ)^2))
      ((complexSquaredPolynomial branch (q^2)).derivative.eval ((sourceWave branch q)^2)*(2*sourceWave branch q))
      (sourceWave branch q) ∧
    (complexSquaredPolynomial branch (q^2)).derivative.eval ((sourceWave branch q)^2)*(2*sourceWave branch q)≠0 := by
  constructor
  · have generated := ((complexSquaredPolynomial branch (q^2)).hasDerivAt ((sourceWave branch q)^2)).comp
      (sourceWave branch q) ((hasDerivAt_id (sourceWave branch q)).pow 2)
    simpa only [complex_squared_eval,Function.comp_def,Pi.pow_apply,id_eq,Complex.ofReal_pow,Nat.cast_ofNat,show 2-1=1 by decide,pow_one,mul_one] using generated
  · apply mul_ne_zero
    · rw [source_wave_square,complexSquaredPolynomial,Polynomial.derivative_map]
      have realNonzero := squared_derivative_nonzero branch (q^2) (momentum_root_domain branch q small) (pow_ne_zero _ nonzero)
      change ((squaredPolynomial branch (q^2)).derivative.map Complex.ofRealHom).eval
        (Complex.ofRealHom ((q^2)^(sourcePower branch)*(sourceRoot branch).root (q^2)))≠0
      rw [Polynomial.eval_map_apply]
      exact Complex.ofReal_ne_zero.mpr realNonzero
    · exact mul_ne_zero (by norm_num) (source_wave_nonzero branch q nonzero)

end
end SaturationMonoid.PhysicsCore.LowEnergy.LightModes
