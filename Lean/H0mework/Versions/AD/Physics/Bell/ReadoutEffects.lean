import H0mework.Versions.AD.Physics.Bell.Readout

/-!
# Complete compact coordinates for same-source Bell readout

The closed local coordinates `(mu,u,z)` construct a legal channel and its canonical XZ axis.
Conversely every original channel and XZ axis constructs these coordinates, including negative
and zero channel gain, without changing any reported probability. The actual source/current/next
readout therefore has an exact polynomial law on the complete continuous coordinate domain.
Rational coordinates give exact rational probabilities despite the internal square root.
-/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.Bell

open Stage9DEF ProofFreeRicherAnholonomicSource

noncomputable section

/-- Closed local effect coordinates; all inequalities constrain primitive coordinates. -/
@[ext] structure CompactReadoutEffect where
  mu : ℝ
  u : ℝ
  z : ℝ
  mu_lower : -1 ≤ mu
  mu_upper : mu ≤ 1
  norm_plus : u ^ 2 + z ^ 2 ≤ (1 + mu) ^ 2
  norm_minus : u ^ 2 + z ^ 2 ≤ (1 - mu) ^ 2

def CompactReadoutEffect.gain (e : CompactReadoutEffect) : ℝ :=
  Real.sqrt (e.u ^ 2 + e.z ^ 2)

theorem CompactReadoutEffect.gain_nonnegative (e : CompactReadoutEffect) : 0 ≤ e.gain :=
  Real.sqrt_nonneg _

theorem CompactReadoutEffect.gain_sq (e : CompactReadoutEffect) :
    e.gain ^ 2 = e.u ^ 2 + e.z ^ 2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg e.u) (sq_nonneg e.z))

theorem CompactReadoutEffect.gain_le_plus (e : CompactReadoutEffect) : e.gain ≤ 1 + e.mu :=
  Real.sqrt_le_iff.mpr ⟨by linarith only [e.mu_lower], e.norm_plus⟩

theorem CompactReadoutEffect.gain_le_minus (e : CompactReadoutEffect) : e.gain ≤ 1 - e.mu :=
  Real.sqrt_le_iff.mpr ⟨by linarith only [e.mu_upper], e.norm_minus⟩

theorem CompactReadoutEffect.gain_le_one (e : CompactReadoutEffect) : e.gain ≤ 1 := by
  linarith only [e.gain_le_plus, e.gain_le_minus]

theorem CompactReadoutEffect.coordinate_bounds (e : CompactReadoutEffect) :
    (-1 ≤ e.u ∧ e.u ≤ 1) ∧ (-1 ≤ e.z ∧ e.z ≤ 1) := by
  have bound : e.u ^ 2 + e.z ^ 2 ≤ 1 := by
    nlinarith [e.gain_sq, e.gain_nonnegative, e.gain_le_one]
  constructor <;> constructor <;> nlinarith [sq_nonneg e.u, sq_nonneg e.z]

theorem CompactReadoutEffect.zero_coordinates (e : CompactReadoutEffect) (zero : e.gain = 0) :
    e.u = 0 ∧ e.z = 0 := by
  have norm := e.gain_sq
  rw [zero] at norm
  constructor <;> nlinarith [sq_nonneg e.u, sq_nonneg e.z]

/-- Normalize a nonzero coordinate vector; the zero vector uses the original Z axis. -/
def CompactReadoutEffect.axis (e : CompactReadoutEffect) : Axis :=
  if positive : 0 < e.gain then
    ⟨e.u / e.gain, e.z / e.gain, by
      field_simp [ne_of_gt positive]
      nlinarith [e.gain_sq]⟩
  else ⟨0, 1, by norm_num⟩

/-- The legal stochastic channel is generated internally from coordinate radius and mean. -/
def CompactReadoutEffect.channel (e : CompactReadoutEffect) : BinaryReadoutChannel where
  error0 := (1 - e.gain - e.mu) / 2
  error1 := (1 - e.gain + e.mu) / 2
  error0_nonnegative := by linarith only [e.gain_le_minus]
  error0_le_one := by linarith only [e.gain_nonnegative, e.mu_lower]
  error1_nonnegative := by linarith only [e.gain_le_plus]
  error1_le_one := by linarith only [e.gain_nonnegative, e.mu_upper]

theorem CompactReadoutEffect.channel_bias (e : CompactReadoutEffect) : e.channel.bias = e.mu := by
  simp only [channel, BinaryReadoutChannel.bias]
  ring

theorem CompactReadoutEffect.channel_gain (e : CompactReadoutEffect) :
    e.channel.gain = e.gain := by
  simp only [channel, BinaryReadoutChannel.gain]
  ring

theorem CompactReadoutEffect.gain_axis_x (e : CompactReadoutEffect) : e.gain * e.axis.x = e.u := by
  by_cases positive : 0 < e.gain
  · simp only [axis, dif_pos positive]
    field_simp [ne_of_gt positive]
  · have zero : e.gain = 0 := le_antisymm (le_of_not_gt positive) e.gain_nonnegative
    simp [axis, zero, (e.zero_coordinates zero).1]

theorem CompactReadoutEffect.gain_axis_z (e : CompactReadoutEffect) : e.gain * e.axis.z = e.z := by
  by_cases positive : 0 < e.gain
  · simp only [axis, dif_pos positive]
    field_simp [ne_of_gt positive]
  · have zero : e.gain = 0 := le_antisymm (le_of_not_gt positive) e.gain_nonnegative
    simp [axis, zero, (e.zero_coordinates zero).2]

theorem channel_axis_norm (channel : BinaryReadoutChannel) (a : Axis) :
    (channel.gain * a.x) ^ 2 + (channel.gain * a.z) ^ 2 = channel.gain ^ 2 := by
  linear_combination channel.gain ^ 2 * a.unit

theorem channel_plus_slack (channel : BinaryReadoutChannel) :
    (1 + channel.bias) ^ 2 - channel.gain ^ 2 = 4 * channel.error1 * (1 - channel.error0) := by
  simp only [BinaryReadoutChannel.bias, BinaryReadoutChannel.gain]
  ring

theorem channel_minus_slack (channel : BinaryReadoutChannel) :
    (1 - channel.bias) ^ 2 - channel.gain ^ 2 = 4 * channel.error0 * (1 - channel.error1) := by
  simp only [BinaryReadoutChannel.bias, BinaryReadoutChannel.gain]
  ring

/-- Every original local channel and axis constructs valid compact coordinates using signed gain. -/
def CompactReadoutEffect.ofChannel (channel : BinaryReadoutChannel) (a : Axis) :
    CompactReadoutEffect where
  mu := channel.bias
  u := channel.gain * a.x
  z := channel.gain * a.z
  mu_lower := by
    simp only [BinaryReadoutChannel.bias]
    linarith only [channel.error1_nonnegative, channel.error0_le_one]
  mu_upper := by
    simp only [BinaryReadoutChannel.bias]
    linarith only [channel.error1_le_one, channel.error0_nonnegative]
  norm_plus := by
    rw [channel_axis_norm]
    have positive : 0 ≤ 4 * channel.error1 * (1 - channel.error0) :=
      mul_nonneg (mul_nonneg (by norm_num) channel.error1_nonnegative)
        (sub_nonneg.mpr channel.error0_le_one)
    linarith only [positive, channel_plus_slack channel]
  norm_minus := by
    rw [channel_axis_norm]
    have positive : 0 ≤ 4 * channel.error0 * (1 - channel.error1) :=
      mul_nonneg (mul_nonneg (by norm_num) channel.error0_nonnegative)
        (sub_nonneg.mpr channel.error1_le_one)
    linarith only [positive, channel_minus_slack channel]

/-- The canonical positive radius preserves the magnitude of every original signed gain. -/
theorem CompactReadoutEffect.gain_of_channel (channel : BinaryReadoutChannel) (a : Axis) :
    (ofChannel channel a).gain = |channel.gain| := by
  change Real.sqrt ((channel.gain * a.x) ^ 2 + (channel.gain * a.z) ^ 2) = _
  rw [channel_axis_norm, Real.sqrt_sq_eq_abs]

/-- The internally generated channel and axis return the exact original compact effect. -/
theorem CompactReadoutEffect.roundtrip (e : CompactReadoutEffect) :
    ofChannel e.channel e.axis = e := by
  apply CompactReadoutEffect.ext
  · exact e.channel_bias
  · change e.channel.gain * e.axis.x = e.u
    rw [e.channel_gain, e.gain_axis_x]
  · change e.channel.gain * e.axis.z = e.z
    rw [e.channel_gain, e.gain_axis_z]

/-- Source readout on the canonical channel/axis generated by each compact effect. -/
def effectProbability (first second : CompactReadoutEffect) (plus : Bool) (x y : Bool) : ℝ :=
  reportedProbability first.channel second.channel plus first.axis second.axis x y

def effectSourceWeight (first second : CompactReadoutEffect) (plus : Bool)
    (point : BasePoint) (x y : Bool) : ℝ :=
  reportedSourceWeight first.channel second.channel plus point first.axis second.axis x y

def effectRuntimeProbability (first second : CompactReadoutEffect) (plus : Bool)
    (point : BasePoint) (x y : Bool) : ℝ :=
  reportedRuntimeProbability first.channel second.channel plus point first.axis second.axis x y

def effectNextProbability (first second : CompactReadoutEffect) (plus : Bool)
    (point : BasePoint) (x y : Bool) : ℝ :=
  reportedNextProbability first.channel second.channel plus point first.axis second.axis x y

/-- The full joint polynomial generated by the source correlation and primitive local coordinates. -/
def effectJointPolynomial (first second : CompactReadoutEffect) (plus : Bool) (x y : Bool) : ℝ :=
  (1 + sign x * first.mu + sign y * second.mu + sign x * sign y *
    (first.mu * second.mu - sign plus * first.u * second.u - first.z * second.z)) / 4

theorem effect_source_probability (first second : CompactReadoutEffect) (plus : Bool)
    (point : BasePoint) (x y : Bool) :
    effectSourceWeight first second plus point x y = effectProbability first second plus x y :=
  reported_probability_from_source first.channel second.channel plus point first.axis second.axis x y

theorem effect_runtime_probability (first second : CompactReadoutEffect) (plus : Bool)
    (point : BasePoint) (x y : Bool) :
    effectRuntimeProbability first second plus point x y = effectProbability first second plus x y :=
  reported_runtime_probability first.channel second.channel plus point first.axis second.axis x y

theorem effect_next_probability (first second : CompactReadoutEffect) (plus : Bool)
    (point : BasePoint) (x y : Bool) :
    effectNextProbability first second plus point x y = effectProbability first second plus x y :=
  reported_next_probability first.channel second.channel plus point first.axis second.axis x y

theorem CompactReadoutEffect.source_pairing (first second : CompactReadoutEffect) (plus : Bool) :
    first.gain * second.gain * latentCorrelation plus first.axis second.axis =
      - (sign plus * first.u * second.u + first.z * second.z) := by
  have herald_x : (heraldAxis plus second.axis).x = sign plus * second.axis.x := by
    cases plus <;> simp [heraldAxis, Axis.reflected, sign]
  have herald_z : (heraldAxis plus second.axis).z = second.axis.z := by
    cases plus <;> simp [heraldAxis, Axis.reflected]
  rw [latent_correlation, herald_x, herald_z]
  calc
    first.gain * second.gain *
        -(first.axis.x * (sign plus * second.axis.x) + first.axis.z * second.axis.z) =
        -(sign plus * (first.gain * first.axis.x) * (second.gain * second.axis.x) +
          (first.gain * first.axis.z) * (second.gain * second.axis.z)) := by ring
    _ = _ := by rw [first.gain_axis_x, second.gain_axis_x,
      first.gain_axis_z, second.gain_axis_z]

theorem effect_probability_polynomial (first second : CompactReadoutEffect) (plus : Bool)
    (x y : Bool) : effectProbability first second plus x y =
      effectJointPolynomial first second plus x y := by
  simp only [effectProbability, reported_probability_closed_form, effectJointPolynomial,
    CompactReadoutEffect.channel_bias, CompactReadoutEffect.channel_gain]
  linear_combination (sign x * sign y) / 4 * first.source_pairing second plus

/-- Complete forward image coverage; no sign restriction on the original channel gain. -/
theorem effect_probability_of_channel (first second : BinaryReadoutChannel) (plus : Bool)
    (a b : Axis) (x y : Bool) :
    effectProbability (CompactReadoutEffect.ofChannel first a)
      (CompactReadoutEffect.ofChannel second b) plus x y =
        reportedProbability first second plus a b x y := by
  rw [effect_probability_polynomial, reported_probability_closed_form, latent_correlation]
  cases plus <;>
    simp only [effectJointPolynomial, CompactReadoutEffect.ofChannel,
      heraldAxis, Bool.false_eq_true, if_false, if_true, Axis.reflected, sign] <;> ring

theorem effect_probability_nonnegative (first second : CompactReadoutEffect) (plus : Bool)
    (x y : Bool) : 0 ≤ effectProbability first second plus x y :=
  reported_probability_nonnegative first.channel second.channel plus first.axis second.axis x y

theorem effect_probability_le_one (first second : CompactReadoutEffect) (plus : Bool)
    (x y : Bool) : effectProbability first second plus x y ≤ 1 :=
  reported_probability_le_one first.channel second.channel plus first.axis second.axis x y

theorem effect_probability_normalized (first second : CompactReadoutEffect) (plus : Bool) :
    ∑ x : Bool, ∑ y : Bool, effectProbability first second plus x y = 1 :=
  reported_probability_normalized first.channel second.channel plus first.axis second.axis

theorem effect_probability_left_marginal (first second : CompactReadoutEffect) (plus : Bool)
    (x : Bool) : ∑ y : Bool, effectProbability first second plus x y = (1 + sign x * first.mu) / 2 := by
  simp only [effectProbability, reported_probability_left_marginal,
    BinaryReadoutChannel.marginal, first.channel_bias]

theorem effect_probability_right_marginal (first second : CompactReadoutEffect) (plus : Bool)
    (y : Bool) : ∑ x : Bool, effectProbability first second plus x y = (1 + sign y * second.mu) / 2 := by
  simp only [effectProbability, reported_probability_right_marginal,
    BinaryReadoutChannel.marginal, second.channel_bias]

theorem effect_no_signalling_left (first second other : CompactReadoutEffect) (plus : Bool)
    (x : Bool) : (∑ y : Bool, effectProbability first second plus x y) =
      ∑ y : Bool, effectProbability first other plus x y := by
  rw [effect_probability_left_marginal, effect_probability_left_marginal]

theorem effect_no_signalling_right (first other second : CompactReadoutEffect) (plus : Bool)
    (y : Bool) : (∑ x : Bool, effectProbability first second plus x y) =
      ∑ x : Bool, effectProbability other second plus x y := by
  rw [effect_probability_right_marginal, effect_probability_right_marginal]

theorem effect_correlation (first second : CompactReadoutEffect) (plus : Bool) :
    (∑ x : Bool, ∑ y : Bool, sign x * sign y * effectProbability first second plus x y) =
      first.mu * second.mu - sign plus * first.u * second.u - first.z * second.z := by
  simp only [effect_probability_polynomial, effectJointPolynomial]
  simp [sign]
  ring

/-- Zero-error local effect on any of the original XZ axes. -/
def CompactReadoutEffect.ideal (a : Axis) : CompactReadoutEffect :=
  ofChannel BinaryReadoutChannel.identity a

theorem effect_probability_ideal (plus : Bool) (a b : Axis) (x y : Bool) :
    effectProbability (CompactReadoutEffect.ideal a) (CompactReadoutEffect.ideal b) plus x y =
      probability a (heraldAxis plus b) x y := by
  rw [CompactReadoutEffect.ideal, CompactReadoutEffect.ideal,
    effect_probability_of_channel, reported_probability_identity]

/-- Exact rational primitive coordinates in the same complete local effect domain. -/
structure RationalReadoutEffect where
  mu : ℚ
  u : ℚ
  z : ℚ
  mu_lower : -1 ≤ mu
  mu_upper : mu ≤ 1
  norm_plus : u ^ 2 + z ^ 2 ≤ (1 + mu) ^ 2
  norm_minus : u ^ 2 + z ^ 2 ≤ (1 - mu) ^ 2

def RationalReadoutEffect.toReal (e : RationalReadoutEffect) : CompactReadoutEffect where
  mu := e.mu
  u := e.u
  z := e.z
  mu_lower := by exact_mod_cast e.mu_lower
  mu_upper := by exact_mod_cast e.mu_upper
  norm_plus := by exact_mod_cast e.norm_plus
  norm_minus := by exact_mod_cast e.norm_minus

/-- Exact rational arithmetic output, with no observed probability table as input. -/
def rationalEffectProbability (first second : RationalReadoutEffect) (plus x y : Bool) : ℚ :=
  let sx : ℚ := if x then -1 else 1
  let sy : ℚ := if y then -1 else 1
  let sh : ℚ := if plus then -1 else 1
  (1 + sx * first.mu + sy * second.mu + sx * sy *
    (first.mu * second.mu - sh * first.u * second.u - first.z * second.z)) / 4

theorem rational_effect_probability (first second : RationalReadoutEffect) (plus x y : Bool) :
    effectProbability first.toReal second.toReal plus x y =
      (rationalEffectProbability first second plus x y : ℝ) := by
  rw [effect_probability_polynomial]
  cases plus <;> cases x <;> cases y <;>
    simp [effectJointPolynomial, RationalReadoutEffect.toReal, rationalEffectProbability, sign]

/-- Complete continuous image coverage and exact rational readout retain the original activation. -/
structure SameOccurrenceReadoutEffectPrediction : Prop extends SameOccurrenceReadoutPrediction where
  canonicalCoverage : ∀ effect : CompactReadoutEffect,
    CompactReadoutEffect.ofChannel effect.channel effect.axis = effect
  originalCoverage : ∀ first second plus a b x y,
    effectProbability (CompactReadoutEffect.ofChannel first a)
      (CompactReadoutEffect.ofChannel second b) plus x y =
        reportedProbability first second plus a b x y
  signedGainCoverage : ∀ channel a, (CompactReadoutEffect.ofChannel channel a).gain = |channel.gain|
  effectSourceBorn : ∀ first second plus point x y,
    effectSourceWeight first second plus point x y = effectProbability first second plus x y
  effectCurrentBorn : ∀ first second plus point x y,
    effectRuntimeProbability first second plus point x y = effectProbability first second plus x y
  effectNextBorn : ∀ first second plus point x y,
    effectNextProbability first second plus point x y = effectProbability first second plus x y
  effectJoint : ∀ first second plus x y,
    effectProbability first second plus x y = effectJointPolynomial first second plus x y
  effectPositive : ∀ first second plus x y, 0 ≤ effectProbability first second plus x y
  effectBounded : ∀ first second plus x y, effectProbability first second plus x y ≤ 1
  effectTotal : ∀ first second plus,
    ∑ x : Bool, ∑ y : Bool, effectProbability first second plus x y = 1
  effectLeftMarginal : ∀ first second plus x,
    ∑ y : Bool, effectProbability first second plus x y = (1 + sign x * first.mu) / 2
  effectRightMarginal : ∀ first second plus y,
    ∑ x : Bool, effectProbability first second plus x y = (1 + sign y * second.mu) / 2
  effectNoSigLeft : ∀ first second other plus x,
    (∑ y : Bool, effectProbability first second plus x y) =
      ∑ y : Bool, effectProbability first other plus x y
  effectNoSigRight : ∀ first other second plus y,
    (∑ x : Bool, effectProbability first second plus x y) =
      ∑ x : Bool, effectProbability other second plus x y
  effectZeroError : ∀ plus a b x y,
    effectProbability (CompactReadoutEffect.ideal a) (CompactReadoutEffect.ideal b) plus x y =
      probability a (heraldAxis plus b) x y
  rationalReadout : ∀ first second plus x y,
    effectProbability (RationalReadoutEffect.toReal first) (RationalReadoutEffect.toReal second)
      plus x y = (rationalEffectProbability first second plus x y : ℝ)

/-- Nullary complete source-to-compact-effect producer; the original root/ledger/next are inherited. -/
theorem sameOccurrenceReadoutEffectPrediction : SameOccurrenceReadoutEffectPrediction :=
  { toSameOccurrenceReadoutPrediction := sameOccurrenceReadoutPrediction
    canonicalCoverage := CompactReadoutEffect.roundtrip
    originalCoverage := effect_probability_of_channel
    signedGainCoverage := CompactReadoutEffect.gain_of_channel
    effectSourceBorn := effect_source_probability
    effectCurrentBorn := effect_runtime_probability
    effectNextBorn := effect_next_probability
    effectJoint := effect_probability_polynomial
    effectPositive := effect_probability_nonnegative
    effectBounded := effect_probability_le_one
    effectTotal := effect_probability_normalized
    effectLeftMarginal := effect_probability_left_marginal
    effectRightMarginal := effect_probability_right_marginal
    effectNoSigLeft := effect_no_signalling_left
    effectNoSigRight := effect_no_signalling_right
    effectZeroError := effect_probability_ideal
    rationalReadout := rational_effect_probability }

end
end SaturationMonoid.PhysicsCore.Stage10.Bell
