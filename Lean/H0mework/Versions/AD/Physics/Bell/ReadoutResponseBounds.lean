import H0mework.Versions.AD.Physics.Bell.ReadoutIdentification

/-!
# Source-generated response bounds from correlation and bias intervals

The correlation is the original 32-probability source family's signed moment. Its centered
absolute value bounds the product of local response gains, hence each gain. Primitive interval
bounds generate a four-corner bias-product enclosure and a distance-to-zero gain lower bound.
Canonical channel errors then inherit the resulting upper bounds. The statistical validity of
the supplied intervals belongs to their consumer; source/current/next moments are retained.
-/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.Bell.ReadoutResponseBounds

open ReadoutIdentification ProofFreeRicherAnholonomicSource

noncomputable section

def centeredCorrelation (family : SettingFamily) (plus a b : Bool) : ℝ :=
  family.correlation plus a b - (family.alice a).mu * (family.bob b).mu

/-- Two-coordinate Cauchy bounds the actual source correlation moment, for either herald. -/
theorem centered_correlation_product_bound (family : SettingFamily) (plus a b : Bool) :
    |centeredCorrelation family plus a b| ≤ (family.alice a).gain * (family.bob b).gain := by
  have squared : (centeredCorrelation family plus a b) ^ 2 ≤
      ((family.alice a).gain * (family.bob b).gain) ^ 2 := by
    rw [mul_pow, CompactReadoutEffect.gain_sq, CompactReadoutEffect.gain_sq]
    cases plus
    · simp only [centeredCorrelation, SettingFamily.correlation_eq, sign]
      nlinarith only [sq_nonneg
        ((family.alice a).u * (family.bob b).z - (family.alice a).z * (family.bob b).u)]
    · simp only [centeredCorrelation, SettingFamily.correlation_eq, sign]
      nlinarith only [sq_nonneg
        ((family.alice a).u * (family.bob b).z + (family.alice a).z * (family.bob b).u)]
  exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg
    (family.alice a).gain_nonnegative (family.bob b).gain_nonnegative)).mp
      (by simpa only [sq_abs] using squared)

theorem gain_product_le_alice (family : SettingFamily) (a b : Bool) :
    (family.alice a).gain * (family.bob b).gain ≤ (family.alice a).gain := by
  have bound := mul_le_mul_of_nonneg_left (family.bob b).gain_le_one
    (family.alice a).gain_nonnegative
  simpa only [mul_one] using bound

theorem gain_product_le_bob (family : SettingFamily) (a b : Bool) :
    (family.alice a).gain * (family.bob b).gain ≤ (family.bob b).gain := by
  have bound := mul_le_mul_of_nonneg_right (family.alice a).gain_le_one
    (family.bob b).gain_nonnegative
  simpa only [one_mul] using bound

/-- Both individual source responses are bounded below by the same centered correlation. -/
theorem centered_correlation_response_bounds (family : SettingFamily) (plus a b : Bool) :
    |centeredCorrelation family plus a b| ≤ (family.alice a).gain ∧
      |centeredCorrelation family plus a b| ≤ (family.bob b).gain :=
  ⟨(centered_correlation_product_bound family plus a b).trans (gain_product_le_alice family a b),
    (centered_correlation_product_bound family plus a b).trans (gain_product_le_bob family a b)⟩

def sourceCorrelationMoment (family : SettingFamily) (point : BasePoint) (plus a b : Bool) : ℝ :=
  ∑ x : Bool, ∑ y : Bool, sign x * sign y * family.sourceProbability point plus a b x y

def currentCorrelationMoment (family : SettingFamily) (point : BasePoint) (plus a b : Bool) : ℝ :=
  ∑ x : Bool, ∑ y : Bool, sign x * sign y * family.currentProbability point plus a b x y

def nextCorrelationMoment (family : SettingFamily) (point : BasePoint) (plus a b : Bool) : ℝ :=
  ∑ x : Bool, ∑ y : Bool, sign x * sign y * family.nextProbability point plus a b x y

theorem source_correlation_moment (family : SettingFamily) (point : BasePoint) (plus a b : Bool) :
    sourceCorrelationMoment family point plus a b = family.correlation plus a b := by
  simp only [sourceCorrelationMoment, SettingFamily.source_probability]
  rfl

theorem current_correlation_moment (family : SettingFamily) (point : BasePoint) (plus a b : Bool) :
    currentCorrelationMoment family point plus a b = family.correlation plus a b := by
  simp only [currentCorrelationMoment, SettingFamily.current_probability]
  rfl

theorem next_correlation_moment (family : SettingFamily) (point : BasePoint) (plus a b : Bool) :
    nextCorrelationMoment family point plus a b = family.correlation plus a b := by
  simp only [nextCorrelationMoment, SettingFamily.next_probability]
  rfl

/-- A scalar interval produces its exact minimum possible absolute value. -/
def intervalDistance (L U : ℝ) : ℝ := max 0 (max L (-U))

theorem interval_distance_le_abs (value L U : ℝ) (lower : L ≤ value) (upper : value ≤ U) :
    intervalDistance L U ≤ |value| := by
  apply max_le (abs_nonneg _)
  exact max_le (lower.trans (le_abs_self _)) ((neg_le_neg upper).trans (neg_le_abs _))

/-- The supplied centered-moment interval generates gain bounds without a gain premise. -/
theorem centered_interval_response_bounds (family : SettingFamily) (plus a b : Bool) (L U : ℝ)
    (lower : L ≤ centeredCorrelation family plus a b)
    (upper : centeredCorrelation family plus a b ≤ U) :
    intervalDistance L U ≤ (family.alice a).gain ∧
      intervalDistance L U ≤ (family.bob b).gain := by
  have interval := interval_distance_le_abs (centeredCorrelation family plus a b) L U lower upper
  have source := centered_correlation_response_bounds family plus a b
  exact ⟨interval.trans source.1, interval.trans source.2⟩

theorem constant_interval_bounds (coefficient value L U : ℝ)
    (lower : L ≤ value) (upper : value ≤ U) :
    min (coefficient * L) (coefficient * U) ≤ coefficient * value ∧
      coefficient * value ≤ max (coefficient * L) (coefficient * U) := by
  by_cases nonnegative : 0 ≤ coefficient
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left lower nonnegative),
      (mul_le_mul_of_nonneg_left upper nonnegative).trans (le_max_right _ _)⟩
  · have nonpositive := (lt_of_not_ge nonnegative).le
    exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left upper nonpositive),
      (mul_le_mul_of_nonpos_left lower nonpositive).trans (le_max_left _ _)⟩

def productLower (AL AU BL BU : ℝ) : ℝ := min (min (AL * BL) (AU * BL)) (min (AL * BU) (AU * BU))

def productUpper (AL AU BL BU : ℝ) : ℝ := max (max (AL * BL) (AU * BL)) (max (AL * BU) (AU * BU))

/-- Four primitive corners enclose every product in the whole rectangle, including sign changes. -/
theorem product_interval_bounds (first second AL AU BL BU : ℝ)
    (first_lower : AL ≤ first) (first_upper : first ≤ AU)
    (second_lower : BL ≤ second) (second_upper : second ≤ BU) :
    productLower AL AU BL BU ≤ first * second ∧ first * second ≤ productUpper AL AU BL BU := by
  have at_lower : min (AL * BL) (AU * BL) ≤ first * BL ∧
      first * BL ≤ max (AL * BL) (AU * BL) := by
    simpa only [mul_comm] using constant_interval_bounds BL first AL AU first_lower first_upper
  have at_upper : min (AL * BU) (AU * BU) ≤ first * BU ∧
      first * BU ≤ max (AL * BU) (AU * BU) := by
    simpa only [mul_comm] using constant_interval_bounds BU first AL AU first_lower first_upper
  have middle := constant_interval_bounds first second BL BU second_lower second_upper
  constructor
  · exact (le_min ((min_le_left _ _).trans at_lower.1)
      ((min_le_right _ _).trans at_upper.1)).trans middle.1
  · exact middle.2.trans (max_le (at_lower.2.trans (le_max_left _ _))
      (at_upper.2.trans (le_max_right _ _)))

/-- Correlation and two local bias intervals internally generate the centered source enclosure. -/
theorem correlation_intervals_centered (family : SettingFamily) (plus a b : Bool)
    (CL CU AL AU BL BU : ℝ) (correlation_lower : CL ≤ family.correlation plus a b)
    (correlation_upper : family.correlation plus a b ≤ CU)
    (alice_lower : AL ≤ (family.alice a).mu) (alice_upper : (family.alice a).mu ≤ AU)
    (bob_lower : BL ≤ (family.bob b).mu) (bob_upper : (family.bob b).mu ≤ BU) :
    CL - productUpper AL AU BL BU ≤ centeredCorrelation family plus a b ∧
      centeredCorrelation family plus a b ≤ CU - productLower AL AU BL BU := by
  have product := product_interval_bounds (family.alice a).mu (family.bob b).mu AL AU BL BU
    alice_lower alice_upper bob_lower bob_upper
  dsimp [centeredCorrelation]
  constructor <;> linarith only [correlation_lower, correlation_upper, product.1, product.2]

theorem correlation_intervals_response_bounds (family : SettingFamily) (plus a b : Bool)
    (CL CU AL AU BL BU : ℝ) (correlation_lower : CL ≤ family.correlation plus a b)
    (correlation_upper : family.correlation plus a b ≤ CU)
    (alice_lower : AL ≤ (family.alice a).mu) (alice_upper : (family.alice a).mu ≤ AU)
    (bob_lower : BL ≤ (family.bob b).mu) (bob_upper : (family.bob b).mu ≤ BU) :
    intervalDistance (CL - productUpper AL AU BL BU) (CU - productLower AL AU BL BU) ≤
      (family.alice a).gain ∧
    intervalDistance (CL - productUpper AL AU BL BU) (CU - productLower AL AU BL BU) ≤
      (family.bob b).gain := by
  have centered := correlation_intervals_centered family plus a b CL CU AL AU BL BU
    correlation_lower correlation_upper alice_lower alice_upper bob_lower bob_upper
  exact centered_interval_response_bounds family plus a b _ _ centered.1 centered.2

/-- Canonical error-zero upper bound reads the already source-generated channel. -/
theorem canonical_error0_bound (effect : CompactReadoutEffect) (G ML : ℝ)
    (gain_lower : G ≤ effect.gain) (mean_lower : ML ≤ effect.mu) :
    0 ≤ effect.channel.error0 ∧ effect.channel.error0 ≤ (1 - G - ML) / 2 := by
  constructor
  · exact effect.channel.error0_nonnegative
  · simp only [CompactReadoutEffect.channel]
    linarith only [gain_lower, mean_lower]

theorem canonical_error1_bound (effect : CompactReadoutEffect) (G MU : ℝ)
    (gain_lower : G ≤ effect.gain) (mean_upper : effect.mu ≤ MU) :
    0 ≤ effect.channel.error1 ∧ effect.channel.error1 ≤ (1 - G + MU) / 2 := by
  constructor
  · exact effect.channel.error1_nonnegative
  · simp only [CompactReadoutEffect.channel]
    linarith only [gain_lower, mean_upper]

end
end SaturationMonoid.PhysicsCore.Stage10.Bell.ReadoutResponseBounds
