import H0mework.Physics.MotherProgrammesFormationClockBF.Action

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ClockBF

open Filter
open scoped Topology

noncomputable section

private theorem positive_near (u : ℝ) (positive : 0 < 1 + u) :
    ∀ᶠ x in 𝓝 u, 0 < 1 + x :=
  (isOpen_lt continuous_const (continuous_const.add continuous_id)).mem_nhds positive

theorem clock_derivative (u b : ℝ) (positive : 0 < 1 + u) :
    deriv (fun x => clockBFAction x b) u = responseScale * (2*b + b^2) := by
  have same : (fun x => clockBFAction x b) =ᶠ[𝓝 u]
      (fun x => (clockBFAction 0 0 + responseScale*b^2) + responseScale*(2*b+b^2)*x) := by
    filter_upwards [positive_near u positive] with x hx
    rw [action_normalForm x b hx]
    ring
  rw [same.deriv_eq]
  exact ((hasDerivAt_const_mul (x := u) (responseScale*(2*b+b^2))).const_add
    (clockBFAction 0 0 + responseScale*b^2)).deriv

theorem auxiliary_derivative (u b : ℝ) (positive : 0 < 1 + u) :
    deriv (fun x => clockBFAction u x) b = 2*responseScale*(1+u)*b + 2*responseScale*u := by
  have same : (fun x => clockBFAction u x) =
      (fun x => clockBFAction 0 0 + (responseScale*(1+u)*x^2 + (2*responseScale*u)*x)) := by
    funext x
    rw [action_normalForm u x positive]
    ring
  rw [same]
  have polynomial := ((((hasDerivAt_id b).pow 2).const_mul (responseScale*(1+u))).add
    (hasDerivAt_const_mul (x := b) (2*responseScale*u))).const_add (clockBFAction 0 0)
  simp only [Pi.pow_apply, Pi.add_apply, id_eq] at polynomial
  convert polynomial.deriv using 1
  ring

/-- Entries are actual iterated derivatives of the complete original action;
the first coordinate is the clock-column variation, the second is B. -/
def quadraticBlock : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![deriv (deriv (fun u => clockBFAction u 0)) 0,
      deriv (fun u => deriv (fun b => clockBFAction u b) 0) 0],
    ![deriv (fun b => deriv (fun u => clockBFAction u b) 0) 0,
      deriv (deriv (fun b => clockBFAction 0 b)) 0]]

theorem quadraticBlock_value : quadraticBlock =
    ![![0, 2*responseScale], ![2*responseScale, 2*responseScale]] := by
  have uu : deriv (deriv (fun u => clockBFAction u 0)) 0 = 0 := by
    have same : deriv (fun u => clockBFAction u 0) =ᶠ[𝓝 0] (fun _ => (0 : ℝ)) := by
      filter_upwards [positive_near 0 (by norm_num)] with x hx
      simp [clock_derivative x 0 hx]
    rw [same.deriv_eq]
    simp
  have ub : deriv (fun u => deriv (fun b => clockBFAction u b) 0) 0 = 2*responseScale := by
    have same : (fun u => deriv (fun b => clockBFAction u b) 0) =ᶠ[𝓝 0]
        (fun u => (2*responseScale)*u) := by
      filter_upwards [positive_near 0 (by norm_num)] with x hx
      simp [auxiliary_derivative x 0 hx]
    rw [same.deriv_eq]
    exact (hasDerivAt_const_mul (x := 0) (2*responseScale)).deriv
  have bu : deriv (fun b => deriv (fun u => clockBFAction u b) 0) 0 = 2*responseScale := by
    have same : (fun b => deriv (fun u => clockBFAction u b) 0) =
        (fun b => responseScale*(2*b+b^2)) := by
      funext b
      exact clock_derivative 0 b (by norm_num)
    rw [same]
    have polynomial := ((hasDerivAt_const_mul (x := (0 : ℝ)) 2).add
      ((hasDerivAt_id (0 : ℝ)).pow 2)).const_mul responseScale
    simp only [Pi.pow_apply, Pi.add_apply, id_eq] at polynomial
    convert polynomial.deriv using 1
    ring
  have bb : deriv (deriv (fun b => clockBFAction 0 b)) 0 = 2*responseScale := by
    have same : deriv (fun b => clockBFAction 0 b) = (fun b => (2*responseScale)*b) := by
      funext b
      simpa using auxiliary_derivative 0 b (by norm_num)
    rw [same]
    exact (hasDerivAt_const_mul (x := 0) (2*responseScale)).deriv
  ext row column
  fin_cases row <;> fin_cases column
  · exact uu
  · exact ub
  · exact bu
  · exact bb

theorem quadraticBlock_determinant : Matrix.det quadraticBlock = -4*responseScale^2 := by
  rw [Matrix.det_fin_two, quadraticBlock_value]
  simp
  ring

theorem quadraticBlock_evidence :
    quadraticBlock 0 0 = 0 ∧ quadraticBlock 0 1 ≠ 0 ∧ Matrix.det quadraticBlock ≠ 0 := by
  have nonzero : responseScale ≠ 0 := ne_of_gt responseScale_pos
  rw [quadraticBlock_determinant, quadraticBlock_value]
  simp [nonzero]

theorem generatedB_unique (u b : ℝ) (positive : 0 < 1 + u) :
    clockBFAction u b = effectiveClockAction u ↔ b = generatedB u := by
  rw [action_elimination u b positive]
  simp [mul_eq_zero, ne_of_gt responseScale_pos, ne_of_gt positive, sub_eq_zero]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ClockBF
