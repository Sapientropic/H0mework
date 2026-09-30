import H0mework.Physics.LowEnergy.LightInteraction.Coefficients

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.LightInteraction
open LightModes Filter Topology
noncomputable section

def complexValue : List Term → ℂ → ℂ → ℂ
  | [],_,_ => 0
  | t::ts,r,w => (t.coefficient : ℂ)*r^t.rPower*w^t.wPower+complexValue ts r w

def rebuild : List Term → ℂ → ℂ → ℂ
  | [],_,_ => 0
  | t::ts,v,w => (t.coefficient : ℂ)*v^t.rPower*w^(t.wPower+2-t.rPower)+rebuild ts v w

theorem complexValue_real (terms : List Term) (r w : ℝ) :
    complexValue terms r w=(value terms r w : ℝ) := by
  induction terms with
  | nil => simp [complexValue,value]
  | cons t ts ih => simp [complexValue,value,ih]

theorem complexValue_continuous (terms : List Term) :
    Continuous (fun x : ℂ × ℂ => complexValue terms x.1 x.2) := by
  induction terms with
  | nil => exact continuous_const
  | cons t ts ih => simp only [complexValue]; fun_prop

theorem rebuild_continuous (terms : List Term) :
    Continuous (fun x : ℂ × ℂ => rebuild terms x.1 x.2) := by
  induction terms with
  | nil => exact continuous_const
  | cons t ts ih => simp only [rebuild]; fun_prop

theorem rebuild_scaling (terms : List Term)
    (admissible : ∀ t∈terms, t.rPower≤t.wPower+2) (r w : ℂ) :
    rebuild terms (w*r) w=w^2*complexValue terms r w := by
  induction terms with
  | nil => simp [rebuild,complexValue]
  | cons t ts ih =>
    have first := admissible t (by simp)
    have rest := ih (fun x hx => admissible x (by simp [hx]))
    have powers : w^t.rPower*w^(t.wPower+2-t.rPower)=w^(t.wPower+2) := by
      rw [← pow_add,Nat.add_sub_of_le first]
    simp only [rebuild,complexValue,rest,mul_add]
    congr 1
    calc
      _ = (t.coefficient : ℂ)*r^t.rPower*(w^t.rPower*w^(t.wPower+2-t.rPower)) := by
        rw [mul_pow]
        ring
      _ = _ := by rw [powers,pow_add]; ring

def sourcePolynomial (v w : ℂ) : ℂ := v+rebuild responseTerms v w

theorem source_polynomial_scaling (r w : ℂ) :
    sourcePolynomial (w*r) w=w*(r+w*complexValue responseTerms r w) := by
  rw [sourcePolynomial,rebuild_scaling responseTerms response_admissible]
  ring

def axialRoot (q : ℝ) : ℝ := (sourceRoot .axialPhase).root (q^2)
def axialDerivative (q : ℝ) : ℝ :=
  1+q^2*value (differentiate (sourceRoot .axialPhase).terms) (axialRoot q) (q^2)
def currentNormal (q : ℝ) : ℝ := axialRoot q+q^2*value responseTerms (axialRoot q) (q^2)

theorem axial_root_positive (q : ℝ) : 0<axialRoot q := by
  have lower := ((sourceRoot .axialPhase).root_in_window (q^2)).1
  change (125/162 : ℝ)-1/20≤axialRoot q at lower
  linarith

theorem current_normal_positive (q : ℝ) (small : |q| ≤ momentumRadius) : 0<currentNormal q := by
  have window := (sourceRoot .axialPhase).root_in_window (q^2)
  have rbound := (sourceRoot .axialPhase).window_bound _ window
  have qbound : |q^2|≤1 := by
    rw [abs_pow]
    exact (pow_le_pow_left₀ (abs_nonneg q) (small.trans momentumRadius_bound) 2).trans (by norm_num)
  have qsq : q^2 ≤ momentumRadius^2 := by nlinarith [abs_nonneg q,sq_abs q]
  have error : |q^2*value responseTerms (axialRoot q) (q^2)|<1/20 := by
    rw [abs_mul,abs_of_nonneg (sq_nonneg q)]
    calc
      _ ≤ momentumRadius^2*coefficientBound responseTerms :=
        mul_le_mul qsq (value_bound responseTerms _ _ rbound qbound)
          (abs_nonneg _) (sq_nonneg _)
      _ < _ := response_error_small
  have lower := window.1
  change (125/162 : ℝ)-1/20≤axialRoot q at lower
  unfold currentNormal
  linarith [(abs_lt.mp error).1,lower]

theorem axial_derivative_positive (q : ℝ) (small : |q| ≤ momentumRadius) : 0<axialDerivative q :=
  (sourceRoot .axialPhase).root_derivative_positive (q^2) (momentum_root_domain .axialPhase q small)

theorem axial_root_limit : Tendsto axialRoot (𝓝 0) (𝓝 (125/162 : ℝ)) := by
  have square : Tendsto (fun q : ℝ => q^2) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_pow 2).tendsto (0 : ℝ)
  exact (sourceRoot .axialPhase).root_limit.comp square

theorem current_normal_limit : Tendsto currentNormal (𝓝 0) (𝓝 (125/162 : ℝ)) := by
  have square : Tendsto (fun q : ℝ => q^2) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_pow 2).tendsto (0 : ℝ)
  have table := (value_continuous responseTerms).tendsto ((125/162 : ℝ),0)
  have generated := axial_root_limit.add (square.mul (table.comp (axial_root_limit.prodMk_nhds square)))
  unfold currentNormal
  simpa only [zero_mul,add_zero,Function.comp_def] using generated

theorem axial_derivative_limit : Tendsto axialDerivative (𝓝 0) (𝓝 (1 : ℝ)) := by
  have square : Tendsto (fun q : ℝ => q^2) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_pow 2).tendsto (0 : ℝ)
  have table := (value_continuous (differentiate (sourceRoot .axialPhase).terms)).tendsto ((125/162 : ℝ),0)
  have generated := (tendsto_const_nhds (x := (1 : ℝ))).add (square.mul (table.comp (axial_root_limit.prodMk_nhds square)))
  unfold axialDerivative
  simpa only [zero_mul,add_zero,Function.comp_def] using generated

end
end SaturationMonoid.PhysicsCore.LowEnergy.LightInteraction
