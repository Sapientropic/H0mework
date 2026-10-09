import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Radial

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Kinetic
open BasinRefinement GaussianPrimitive SourceGaussianModel ContinuousGradient
open Polynomial
noncomputable section

/-- The axis-a derivative of a Gaussian primitive expands into two terms that
    share the same centre and exponent: w·p·x^(p-1) − 2αw·x^(p+1). -/
def derivativeTerms (t : Term) (a : Fin 3) : List Term :=
  [⟨t.weight * (t.powers a : ℚ),t.exponent,t.centre,
      Function.update t.powers a (t.powers a - 1)⟩,
    ⟨-(2 * t.exponent) * t.weight,t.exponent,t.centre,
      Function.update t.powers a (t.powers a + 1)⟩]

theorem factor_raise (alpha : ℚ) (power : ℕ) (x : ℝ) :
    factor alpha power 1 x =
      (power : ℝ) * factor alpha (power - 1) 0 x -
        2 * (alpha : ℝ) * factor alpha (power + 1) 0 x := by
  have polyEq : (jetPoly alpha power 1).map (algebraMap ℚ ℝ) =
      Polynomial.C (power : ℝ) * X ^ (power - 1) -
        Polynomial.C (2 * (alpha : ℝ)) * X ^ (power + 1) := by
    have base : jetPolynomial alpha (X ^ power) =
        Polynomial.C (power : ℚ) * X ^ (power - 1) -
          Polynomial.C (2 * alpha) * X ^ (power + 1) := by
      unfold jetPolynomial
      rw [Polynomial.derivative_X_pow]
      rw [mul_assoc, ← pow_succ']
    calc (jetPoly alpha power 1).map (algebraMap ℚ ℝ)
        = (jetPolynomial alpha (X ^ power)).map (algebraMap ℚ ℝ) := by
          simp only [jetPoly, Function.iterate_one]
      _ = _ := by rw [base]; simp
  have lhs : factor alpha power 1 x =
      gaussian (alpha : ℝ) ((jetPoly alpha power 1).map (algebraMap ℚ ℝ)) x := rfl
  rw [lhs, polyEq]
  simp only [factor_zero, gaussian, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  ring

/-- One primitive differentiated along one axis equals the two expansion terms. -/
theorem value_raise_axis (t : Term) (a : Fin 3) (x : Point) :
    value t (raise zeroJet a) x =
      value (⟨t.weight * (t.powers a : ℚ),t.exponent,t.centre,
          Function.update t.powers a (t.powers a - 1)⟩ : Term) zeroJet x +
      value (⟨-(2 * t.exponent) * t.weight,t.exponent,t.centre,
          Function.update t.powers a (t.powers a + 1)⟩ : Term) zeroJet x := by
  fin_cases a
  all_goals (
    unfold value raise zeroJet
    simp only [Function.update_apply]
    simp)
  all_goals (
    rw [factor_raise]
    simp only [factor_zero]
    ring)

/-- Pointwise derivative expansion of an orbital along one axis. -/
theorem orbital_raise_eq (terms : List Term) (a : Fin 3) (x : Point) :
    orbital terms (raise zeroJet a) x =
      orbital (terms.flatMap fun t => derivativeTerms t a) zeroJet x := by
  induction terms with
  | nil => simp [orbital]
  | cons t rest ih =>
      simp only [List.flatMap_cons]
      rw [show orbital (t :: rest) (raise zeroJet a) x =
            value t (raise zeroJet a) x + orbital rest (raise zeroJet a) x
          from by simp only [orbital, List.map_cons, List.sum_cons]]
      rw [show orbital (derivativeTerms t a ++
              List.flatMap (fun s => derivativeTerms s a) rest) zeroJet x =
            orbital (derivativeTerms t a) zeroJet x +
              orbital (List.flatMap (fun s => derivativeTerms s a) rest) zeroJet x
          from by simp only [orbital, List.map_append, List.sum_append]]
      rw [ih]
      simp only [show derivativeTerms t a =
          [⟨t.weight * (t.powers a : ℚ),t.exponent,t.centre,
              Function.update t.powers a (t.powers a - 1)⟩,
            ⟨-(2 * t.exponent) * t.weight,t.exponent,t.centre,
              Function.update t.powers a (t.powers a + 1)⟩] from rfl]
      simp only [orbital, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil]
      rw [value_raise_axis]
      ring

/-- Derivative terms keep the source exponent and centre. -/
theorem derivative_terms_same_fields (t : Term) (a : Fin 3) :
    ∀ u ∈ derivativeTerms t a, u.exponent = t.exponent ∧ u.centre = t.centre := by
  intro u hu
  simp only [derivativeTerms, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

/-- Derivative pairs share the same radial address as their parent pair. -/
theorem derivative_terms_same_radial (s t : Term) (a : Fin 3)
    (u : Term) (hu : u ∈ derivativeTerms s a)
    (v : Term) (hv : v ∈ derivativeTerms t a) :
    pairExponent u v = pairExponent s t ∧
      pairPenalty u v = pairPenalty s t := by
  rcases derivative_terms_same_fields s a u hu with ⟨ue, uc⟩
  rcases derivative_terms_same_fields t a v hv with ⟨ve, vc⟩
  have pe : u.exponent + v.exponent = s.exponent + t.exponent :=
    congrArg₂ _ ue ve
  have pp : (∑ k : Fin 3, u.exponent * v.exponent / (u.exponent + v.exponent) *
        (u.centre k - v.centre k)^2) =
      ∑ k : Fin 3, s.exponent * t.exponent / (s.exponent + t.exponent) *
        (s.centre k - t.centre k)^2 := by
    rw [ue, uc, ve, vc]
  exact ⟨pe, pp⟩

end
end LAlanine40K2025.UnifiedOrbitals.Kinetic
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
