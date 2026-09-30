import H0mework.Physics.LowEnergy.VertexTensor.Coefficients

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.VertexTensor
open LightModes LightInteraction DrivenInteraction Filter Topology
noncomputable section

def differenceTerms (same : Bool) : List Term := if same then sameDifference else oppositeDifference

theorem difference_admissible (same : Bool) : ∀ t∈differenceTerms same, t.rPower≤ t.wPower+2 := by
  cases same
  · exact opposite_difference_admissible
  · exact same_difference_admissible

theorem difference_small (same : Bool) : momentumRadius^2*coefficientBound (differenceTerms same)<1/20 := by
  cases same
  · exact opposite_difference_small
  · exact same_difference_small

def transversePolynomial (same : Bool) (v w : ℂ) : ℂ :=
  if same then growthPolynomial v w else sourcePolynomial v w

def longitudinalPolynomial (same : Bool) (v w : ℂ) : ℂ :=
  transversePolynomial same v w+rebuild (differenceTerms same) v w

def transverseNormal (same : Bool) (q : ℝ) : ℝ :=
  if same then growthNormal q else currentNormal q

def longitudinalNormal (same : Bool) (q : ℝ) : ℝ :=
  transverseNormal same q+q^2*value (differenceTerms same) (axialRoot q) (q^2)

theorem longitudinal_polynomial_difference (same : Bool) (r w : ℂ) :
    longitudinalPolynomial same (w*r) w-transversePolynomial same (w*r) w=
      w^2*complexValue (differenceTerms same) r w := by
  rw [longitudinalPolynomial,rebuild_scaling _ (difference_admissible same)]
  ring

theorem longitudinal_normal_positive (same : Bool) (q : ℝ) (small : |q|≤ momentumRadius) :
    0<longitudinalNormal same q := by
  have response := (source_table_bound responseTerms q small).trans_lt response_error_small
  have difference := (source_table_bound (differenceTerms same) q small).trans_lt (difference_small same)
  have lower := ((sourceRoot .axialPhase).root_in_window (q^2)).1
  change (125/162 : ℝ)-1/20≤ axialRoot q at lower
  have even := source_table_bound evenTerms q small
  have evenBound : 2*|q^2*value evenTerms (axialRoot q) (q^2)|<1/20 := by
    nlinarith [even_error_small]
  cases same
  · change 0<currentNormal q+q^2*value (differenceTerms false) (axialRoot q) (q^2)
    unfold currentNormal
    linarith [(abs_lt.mp response).1,(abs_lt.mp difference).1]
  · change 0<growthNormal q+q^2*value (differenceTerms true) (axialRoot q) (q^2)
    unfold growthNormal currentNormal
    nlinarith [(abs_lt.mp response).1,(abs_lt.mp difference).1,
      neg_le_abs (q^2*value evenTerms (axialRoot q) (q^2))]

theorem transverse_normal_limit (same : Bool) :
    Tendsto (transverseNormal same) (𝓝 0) (𝓝 (125/162 : ℝ)) := by
  cases same
  · exact current_normal_limit
  · exact growth_normal_limit

theorem longitudinal_normal_limit (same : Bool) :
    Tendsto (longitudinalNormal same) (𝓝 0) (𝓝 (125/162 : ℝ)) := by
  have square : Tendsto (fun q : ℝ => q^2) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_pow 2).tendsto (0 : ℝ)
  have table := (value_continuous (differenceTerms same)).tendsto ((125/162 : ℝ),0)
  have generated := (transverse_normal_limit same).add
    (square.mul (table.comp (axial_root_limit.prodMk_nhds square)))
  unfold longitudinalNormal
  simpa only [zero_mul,add_zero,Function.comp_def] using generated

theorem longitudinal_normal_difference (same : Bool) (q : ℝ) :
    longitudinalNormal same q-transverseNormal same q=
      q^2*value (differenceTerms same) (axialRoot q) (q^2) := by
  rw [longitudinalNormal]
  ring

theorem longitudinal_normal_difference_bound (same : Bool) (q : ℝ) (small : |q|≤ momentumRadius) :
    |longitudinalNormal same q-transverseNormal same q|≤
      q^2*coefficientBound (differenceTerms same) := by
  rw [longitudinal_normal_difference,abs_mul,abs_of_nonneg (sq_nonneg q)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg q)
  have window := (sourceRoot .axialPhase).root_in_window (q^2)
  have bound := (sourceRoot .axialPhase).window_bound _ window
  have qbound : |q^2|≤1 := by
    rw [abs_pow]
    exact (pow_le_pow_left₀ (abs_nonneg q) (small.trans momentumRadius_bound) 2).trans (by norm_num)
  exact value_bound _ _ _ bound qbound

end
end SaturationMonoid.PhysicsCore.LowEnergy.VertexTensor
