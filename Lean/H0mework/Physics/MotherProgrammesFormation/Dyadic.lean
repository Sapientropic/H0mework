import Mathlib.Analysis.SpecialFunctions.Complex.Circle

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.DyadicFormation

noncomputable section

/-- One selected orientation of the circle; conjugation gives the opposite choice. -/
def Upper (value : Circle) : Prop := 0 < Complex.arg (value : ℂ)

/-- This step reads only the current point. -/
def step (current : Circle) : Circle :=
  Circle.exp (Complex.arg (current : ℂ) / 2)

theorem step_arg (current : Circle) (upper : Upper current) :
    Complex.arg (step current : ℂ) = Complex.arg (current : ℂ) / 2 := by
  apply Circle.arg_exp
  · have : 0 < Complex.arg (current : ℂ) / 2 := half_pos upper
    linarith [Real.pi_pos]
  · have := Complex.arg_le_pi (current : ℂ)
    linarith [Real.pi_pos]

theorem step_upper (current : Circle) (upper : Upper current) : Upper (step current) := by
  unfold Upper
  rw [step_arg current upper]
  exact half_pos upper

theorem step_square (current : Circle) : step current ^ 2 = current := by
  rw [step, pow_two, ← Circle.exp_add]
  convert Circle.exp_arg current using 1
  congr 1
  ring

theorem step_im_pos (current : Circle) (upper : Upper current) :
    0 < (step current : ℂ).im := by
  change 0 < (Complex.exp ((Complex.arg (current : ℂ) / 2 : ℝ) * Complex.I)).im
  rw [Complex.exp_ofReal_mul_I_im]
  apply Real.sin_pos_of_pos_of_lt_pi (half_pos upper)
  have := Complex.arg_le_pi (current : ℂ)
  linarith [Real.pi_pos]

theorem step_unique (current : Circle) (upper : Upper current) (candidate : Circle)
    (square : candidate ^ 2 = current) (oriented : 0 ≤ (candidate : ℂ).im) :
    candidate = step current := by
  have squares : (candidate : ℂ) ^ 2 = (step current : ℂ) ^ 2 :=
    congrArg (fun value : Circle => (value : ℂ)) (square.trans (step_square current).symm)
  rcases eq_or_eq_neg_of_sq_eq_sq (candidate : ℂ) (step current : ℂ) squares with same | same
  · exact Circle.ext same
  · have imaginary := congrArg Complex.im same
    simp only [Complex.neg_im] at imaginary
    have positive := step_im_pos current upper
    linarith

theorem step_existsUnique (current : Circle) (upper : Upper current) :
    ∃! next : Circle, next ^ 2 = current ∧ 0 ≤ (next : ℂ).im := by
  exact ⟨step current, ⟨step_square current, (step_im_pos current upper).le⟩,
    fun next valid => step_unique current upper next valid.1 valid.2⟩

theorem primitive_eq_neg_one (seed : Circle) (involution : seed ^ 2 = 1)
    (effective : seed ≠ 1) : seed = -1 := by
  have square : (seed : ℂ) ^ 2 = 1 := congrArg (fun value : Circle => (value : ℂ)) involution
  rcases sq_eq_one_iff.mp square with same | same
  · exact False.elim (effective (Circle.ext same))
  · exact Circle.ext same

theorem primitive_upper (seed : Circle) (involution : seed ^ 2 = 1)
    (effective : seed ≠ 1) : Upper seed := by
  rw [primitive_eq_neg_one seed involution effective]
  simpa [Upper] using Real.pi_pos

/-- Finite recursion uses the previous generated point, without a rate or future inventory. -/
def generatedAt (seed : Circle) : ℕ → Circle
  | 0 => seed
  | depth + 1 => step (generatedAt seed depth)

theorem at_upper (seed : Circle) (upper : Upper seed) (depth : ℕ) : Upper (generatedAt seed depth) := by
  induction depth with
  | zero => exact upper
  | succ depth previous => exact step_upper (generatedAt seed depth) previous

theorem at_square (seed : Circle) (depth : ℕ) : generatedAt seed (depth + 1) ^ 2 = generatedAt seed depth :=
  step_square (generatedAt seed depth)

theorem at_im_nonneg (seed : Circle) (upper : Upper seed) (depth : ℕ) :
    0 ≤ (generatedAt seed depth : ℂ).im :=
  Complex.arg_nonneg_iff.mp (at_upper seed upper depth).le

theorem at_arg (seed : Circle) (upper : Upper seed) (depth : ℕ) :
    Complex.arg (generatedAt seed depth : ℂ) = Complex.arg (seed : ℂ) / 2 ^ depth := by
  induction depth with
  | zero => simp [generatedAt]
  | succ depth previous =>
    change Complex.arg (step (generatedAt seed depth) : ℂ) = _
    rw [step_arg _ (at_upper seed upper depth), previous, pow_succ, div_div]

theorem primitive_normalForm (seed : Circle) (involution : seed ^ 2 = 1)
    (effective : seed ≠ 1) (depth : ℕ) :
    generatedAt seed depth = Circle.exp (Real.pi / 2 ^ depth) := by
  have angle := at_arg seed (primitive_upper seed involution effective) depth
  have seed_angle : Complex.arg (seed : ℂ) = Real.pi := by
    rw [primitive_eq_neg_one seed involution effective]
    simp
  rw [seed_angle] at angle
  rw [← Circle.exp_arg (generatedAt seed depth), angle]

/-- A competitor needs only the history up to this depth. -/
theorem finite_unique (seed : Circle) (upper : Upper seed) (depth : ℕ)
    (candidate : Fin (depth + 1) → Circle)
    (initial : candidate ⟨0, by omega⟩ = seed)
    (squares : ∀ index : Fin depth,
      candidate index.succ ^ 2 = candidate index.castSucc)
    (oriented : ∀ index, 0 ≤ (candidate index : ℂ).im) :
    ∀ index, candidate index = generatedAt seed index.val := by
  intro index
  induction index using Fin.induction with
  | zero => exact initial
  | succ index previous =>
    apply step_unique (generatedAt seed index.val) (at_upper seed upper index.val)
    · exact (squares index).trans previous
    · exact oriented index.succ

theorem finite_existsUnique (seed : Circle) (involution : seed ^ 2 = 1)
    (effective : seed ≠ 1) (depth : ℕ) :
    ∃! history : Fin (depth + 1) → Circle,
      history ⟨0, by omega⟩ = seed ∧
      (∀ index : Fin depth, history index.succ ^ 2 = history index.castSucc) ∧
      ∀ index, 0 ≤ (history index : ℂ).im := by
  have upper := primitive_upper seed involution effective
  refine ⟨fun index => generatedAt seed index.val,
    ⟨rfl, fun index => at_square seed index.val,
      fun index => at_im_nonneg seed upper index.val⟩, ?_⟩
  intro history valid
  funext index
  exact finite_unique seed upper depth history valid.1 valid.2.1 valid.2.2 index

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.DyadicFormation
