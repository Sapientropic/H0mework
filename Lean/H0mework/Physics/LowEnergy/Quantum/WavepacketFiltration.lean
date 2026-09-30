import H0mework.Physics.LowEnergy.Quantum.MagnusDerivative

/-! Occupation filtration for the finite Magnus exponential, including the
mixed grades of its linear and quadratic logarithmic terms. -/
set_option autoImplicit false
namespace SourceWavepacketFiltration
open SourceWavepacketGrade
open scoped BigOperators
noncomputable section
variable {Ω B : Type*} [AddCommGroup B] [Module ℂ B]

def Above (weight : Ω → ℕ) (n : ℕ) (f : Ω → B) : Prop :=
  ∀ x, weight x < n → f x = 0

def Raises (weight : Ω → ℕ) (k : ℕ) (T : Module.End ℂ (Ω → B)) : Prop :=
  ∀ n f, Above weight n f → Above weight (n+k) (T f)

theorem raises_of_grade (weight : Ω → ℕ) (N k : ℕ) (bound : ∀ x, weight x ≤ N)
    (T : Module.End ℂ (Ω → B))
    (law : grade weight * T = T * grade weight + (k : ℂ) • T) : Raises weight k T := by
  intro n f hf x low
  have each (m : ℕ) : T (project weight m f) x = 0 := by
    by_cases small : m < n
    · have empty : project weight m f = 0 := by
        funext z
        by_cases equal : weight z = m
        · simp [project, equal, hf z (by omega)]
        · simp [project, equal]
      rw [empty, map_zero, Pi.zero_apply]
    · have state := project_eigenstate weight m f
      have raised := congrArg (fun U : Module.End ℂ (Ω → B) => U (project weight m f)) law
      simp only [Module.End.mul_apply, LinearMap.add_apply, state, map_smul,
        LinearMap.smul_apply, ← add_smul] at raised
      have value := congrFun raised x
      have scalar_ne : ((weight x : ℂ) - ((m : ℂ)+(k : ℂ))) ≠ 0 := by
        rw [← Nat.cast_add]
        exact sub_ne_zero.mpr (by exact_mod_cast (show weight x ≠ m+k by omega))
      have annihilates : ((weight x : ℂ) - ((m : ℂ)+(k : ℂ))) •
          T (project weight m f) x = 0 := by
        simpa only [grade_apply, Pi.smul_apply, sub_smul, sub_eq_zero] using value
      exact (smul_eq_zero.mp annihilates).resolve_left scalar_ne
  rw [finite_grade_decomposition weight N bound f, map_sum, Finset.sum_apply]
  simp only [each, Finset.sum_const_zero]

theorem raises_mono (weight : Ω → ℕ) (k l : ℕ) (le : k ≤ l)
    (T : Module.End ℂ (Ω → B)) (h : Raises weight l T) : Raises weight k T := by
  intro n f hf x low
  exact h n f hf x (by omega)

theorem raises_add (weight : Ω → ℕ) (k : ℕ) (T U : Module.End ℂ (Ω → B))
    (hT : Raises weight k T) (hU : Raises weight k U) : Raises weight k (T+U) := by
  intro n f hf x low
  simp only [LinearMap.add_apply, Pi.add_apply, hT n f hf x low, hU n f hf x low, add_zero]

theorem raises_smul (weight : Ω → ℕ) (k : ℕ) (T : Module.End ℂ (Ω → B))
    (h : Raises weight k T) (c : ℂ) : Raises weight k (c • T) := by
  intro n f hf x low
  simp only [LinearMap.smul_apply, Pi.smul_apply, h n f hf x low, smul_zero]

theorem raises_sub (weight : Ω → ℕ) (k : ℕ) (T U : Module.End ℂ (Ω → B))
    (hT : Raises weight k T) (hU : Raises weight k U) : Raises weight k (T-U) := by
  intro n f hf x low
  simp only [LinearMap.sub_apply, Pi.sub_apply, hT n f hf x low, hU n f hf x low, sub_self]

theorem raises_mul (weight : Ω → ℕ) (k l : ℕ) (T U : Module.End ℂ (Ω → B))
    (hT : Raises weight k T) (hU : Raises weight l U) : Raises weight (k+l) (T*U) := by
  intro n f hf
  simpa only [Module.End.mul_apply, Nat.add_assoc, Nat.add_comm l k] using hT (n+l) (U f) (hU n f hf)

theorem raises_pow (weight : Ω → ℕ) (k : ℕ) (T : Module.End ℂ (Ω → B))
    (h : Raises weight k T) (n : ℕ) : Raises weight (n*k) (T^n) := by
  induction n with
  | zero => intro m f hf; simpa using hf
  | succ n ih =>
    simpa only [pow_succ, Nat.add_mul, Nat.one_mul] using raises_mul weight (n*k) k (T^n) T ih h

theorem raises_above_bound_zero (weight : Ω → ℕ) (N k : ℕ)
    (bound : ∀ x, weight x ≤ N) (high : N < k)
    (T : Module.End ℂ (Ω → B)) (h : Raises weight k T) : T = 0 := by
  apply LinearMap.ext
  intro f
  funext x
  exact h 0 f (by intro z low; omega) x (by have := bound x; omega)

theorem graded_magnus_ODE (weight : Ω → ℕ) (n : ℕ) (bound : ∀ x, weight x ≤ n+1)
    (D : Module.End ℂ (Ω → B) →ₗ[ℂ] Module.End ℂ (Ω → B)) (one : D 1 = 0)
    (leibniz : ∀ a b, D (a * b) = D a * b + a * D b)
    (X Y C : Module.End ℂ (Ω → B))
    (derivative : D X = Y - (1/2 : ℂ) • C)
    (commutator : X * (Y - (1/2 : ℂ) • C) - (Y - (1/2 : ℂ) • C) * X = C)
    (central : Commute X C)
    (raiseX : Raises weight 1 X) (raiseY : Raises weight 1 Y) (raiseC : Raises weight 2 C) :
    D (SourceMagnusDerivative.partialExp (n+2) X) =
      Y * SourceMagnusDerivative.partialExp (n+2) X := by
  have first : Raises weight 1 (Y - (1/2 : ℂ) • C) := by
    exact raises_sub weight 1 _ _ raiseY
      (raises_smul weight 1 C (raises_mono weight 1 2 (by omega) C raiseC) (1/2 : ℂ))
  apply SourceMagnusDerivative.magnus_ODE D one leibniz X Y C derivative commutator central n
  · apply raises_above_bound_zero weight (n+1) (1+(n+1)*1) bound (by omega)
    exact raises_mul weight 1 ((n+1)*1) _ _ first (raises_pow weight 1 X raiseX (n+1))
  · apply raises_above_bound_zero weight (n+1) (2+n*1) bound (by omega)
    exact raises_mul weight 2 (n*1) _ _ raiseC (raises_pow weight 1 X raiseX n)

theorem all_N_magnus_ODE (weight : Ω → ℕ) (N : ℕ) (bound : ∀ x, weight x ≤ N)
    (D : Module.End ℂ (Ω → B) →ₗ[ℂ] Module.End ℂ (Ω → B)) (one : D 1 = 0)
    (leibniz : ∀ a b, D (a * b) = D a * b + a * D b)
    (X Y C : Module.End ℂ (Ω → B))
    (derivative : D X = Y - (1/2 : ℂ) • C)
    (commutator : X * (Y - (1/2 : ℂ) • C) - (Y - (1/2 : ℂ) • C) * X = C)
    (central : Commute X C)
    (raiseX : Raises weight 1 X) (raiseY : Raises weight 1 Y) (raiseC : Raises weight 2 C) :
    D (SourceMagnusDerivative.partialExp (N+1) X) =
      Y * SourceMagnusDerivative.partialExp (N+1) X := by
  cases N with
  | zero =>
    have empty := raises_above_bound_zero weight 0 1 bound (by omega) Y raiseY
    simp [SourceMagnusDerivative.partialExp, SourceMagnusDerivative.term, one, empty]
  | succ n =>
    exact graded_magnus_ODE weight n bound D one leibniz X Y C derivative commutator central
      raiseX raiseY raiseC

end
end SourceWavepacketFiltration
