import H0mework.Versions.AD.Physics.Bell.ReadoutIdentification

/-!
# Calibrated inverse readout from independent local probe responses

The complete Bell law supplies the biases and rank-one products. Two known XZ Bloch probes
with nonzero determinant supply signed local responses at one regular setting. Their responses
compute both local coordinates by linear inversion; the law then computes all four local effects.
This is an inverse consumer of measured probe expectations. It does not generate calibration
measurements or select an actual device from Bell probabilities alone.
-/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.Bell.ReadoutAnchors

open ProofFreeRicherAnholonomicSource ReadoutIdentification

noncomputable section

/-- A known normalized qubit probe; mixed XZ preparations are included. -/
structure BlochProbe where
  x : ℝ
  z : ℝ
  norm_le_one : x ^ 2 + z ^ 2 ≤ 1

def BlochProbe.response (r : BlochProbe) (e : CompactReadoutEffect) : ℝ :=
  e.mu + e.u * r.x + e.z * r.z

/-- The response is the canonical readout channel acting on the probe's latent mean. -/
theorem BlochProbe.response_channel (r : BlochProbe) (e : CompactReadoutEffect) :
    r.response e = e.channel.bias + e.channel.gain * (e.axis.x * r.x + e.axis.z * r.z) := by
  rw [e.channel_bias, e.channel_gain]
  simp only [response]
  linear_combination -(e.gain_axis_x) * r.x - (e.gain_axis_z) * r.z

theorem BlochProbe.directional_sq_le (r : BlochProbe) (e : CompactReadoutEffect) :
    (e.u * r.x + e.z * r.z) ^ 2 ≤ e.gain ^ 2 := by
  rw [e.gain_sq]
  have product := mul_le_mul_of_nonneg_left r.norm_le_one
    (add_nonneg (sq_nonneg e.u) (sq_nonneg e.z))
  nlinarith [sq_nonneg (e.u * r.z - e.z * r.x)]

theorem BlochProbe.response_bounds (r : BlochProbe) (e : CompactReadoutEffect) :
    -1 ≤ r.response e ∧ r.response e ≤ 1 := by
  have sq := r.directional_sq_le e
  have gain := e.gain_nonnegative
  have lower : -e.gain ≤ e.u * r.x + e.z * r.z := by nlinarith
  have upper : e.u * r.x + e.z * r.z ≤ e.gain := by nlinarith
  simp only [response]
  constructor <;> linarith only [lower, upper, e.gain_le_plus, e.gain_le_minus]

def BlochProbe.probability (r : BlochProbe) (e : CompactReadoutEffect) (outcome : Bool) : ℝ :=
  (1 + sign outcome * r.response e) / 2

theorem BlochProbe.probability_nonnegative (r : BlochProbe) (e : CompactReadoutEffect)
    (outcome : Bool) : 0 ≤ r.probability e outcome := by
  cases outcome <;> simp only [probability, sign] <;>
    linarith only [r.response_bounds e]

theorem BlochProbe.probability_normalized (r : BlochProbe) (e : CompactReadoutEffect) :
    ∑ outcome : Bool, r.probability e outcome = 1 := by
  simp [probability, sign]
  ring

theorem BlochProbe.probability_mean (r : BlochProbe) (e : CompactReadoutEffect) :
    ∑ outcome : Bool, sign outcome * r.probability e outcome = r.response e := by
  simp [probability, sign]
  ring

/-- Only probe preparation coordinates enter this determinant. -/
def determinant (r₀ r₁ : BlochProbe) : ℝ := r₀.x * r₁.z - r₁.x * r₀.z

def recoveredU (r₀ r₁ : BlochProbe) (mu m₀ m₁ : ℝ) : ℝ :=
  ((m₀ - mu) * r₁.z - (m₁ - mu) * r₀.z) / determinant r₀ r₁

def recoveredZ (r₀ r₁ : BlochProbe) (mu m₀ m₁ : ℝ) : ℝ :=
  (r₀.x * (m₁ - mu) - r₁.x * (m₀ - mu)) / determinant r₀ r₁

theorem recovered_u (r₀ r₁ : BlochProbe) (independent : determinant r₀ r₁ ≠ 0)
    (e : CompactReadoutEffect) :
    recoveredU r₀ r₁ e.mu (r₀.response e) (r₁.response e) = e.u := by
  apply (div_eq_iff independent).mpr
  simp only [BlochProbe.response, determinant]
  ring

theorem recovered_z (r₀ r₁ : BlochProbe) (independent : determinant r₀ r₁ ≠ 0)
    (e : CompactReadoutEffect) :
    recoveredZ r₀ r₁ e.mu (r₀.response e) (r₁.response e) = e.z := by
  apply (div_eq_iff independent).mpr
  simp only [BlochProbe.response, determinant]
  ring

@[ext] structure EffectCoordinates where
  mu : ℝ
  u : ℝ
  z : ℝ

def coordinates (e : CompactReadoutEffect) : EffectCoordinates := ⟨e.mu, e.u, e.z⟩

@[ext] structure FamilyCoordinates where
  alice : Bool → EffectCoordinates
  bob : Bool → EffectCoordinates

def familyCoordinates (family : SettingFamily) : FamilyCoordinates where
  alice := fun a => coordinates (family.alice a)
  bob := fun b => coordinates (family.bob b)

/-- All recovered coordinates are computed from law readouts and two measured local means. -/
def reconstruct (law : IdentifiedCoordinates) (r₀ r₁ : BlochProbe) (m₀ m₁ : ℝ) :
    FamilyCoordinates :=
  let anchorU := recoveredU r₀ r₁ (law.aliceBias false) m₀ m₁
  let anchorZ := recoveredZ r₀ r₁ (law.aliceBias false) m₀ m₁
  { alice := fun a =>
      ⟨law.aliceBias a, law.productX a false / (law.productX false false / anchorU),
        law.productZ a false / (law.productZ false false / anchorZ)⟩
    bob := fun b =>
      ⟨law.bobBias b, law.productX false b / anchorU, law.productZ false b / anchorZ⟩ }

/-- Complete exact reconstruction of all four legal source effects on the regular stratum. -/
theorem reconstruct_eq (family : SettingFamily) (regular : Regular family)
    (r₀ r₁ : BlochProbe) (independent : determinant r₀ r₁ ≠ 0) :
    reconstruct family.recovered r₀ r₁ (r₀.response (family.alice false))
      (r₁.response (family.alice false)) = familyCoordinates family := by
  rw [family.recovered_eq_identified]
  have ux := (mul_ne_zero_iff.mp regular.1).1
  have bx := (mul_ne_zero_iff.mp regular.1).2
  have uz := (mul_ne_zero_iff.mp regular.2).1
  have bz := (mul_ne_zero_iff.mp regular.2).2
  simp only [reconstruct, SettingFamily.identified,
    recovered_u r₀ r₁ independent, recovered_z r₀ r₁ independent,
    familyCoordinates, coordinates]
  apply FamilyCoordinates.ext
  · funext a
    apply EffectCoordinates.ext
    · rfl
    · field_simp [ux, bx]
    · field_simp [uz, bz]
  · funext b
    apply EffectCoordinates.ext
    · rfl
    · field_simp [ux]
    · field_simp [uz]

theorem familyCoordinates_injective {first second : SettingFamily}
    (same : familyCoordinates first = familyCoordinates second) : first = second := by
  apply SettingFamily.ext
  · funext a
    have local_eq := congrFun (congrArg FamilyCoordinates.alice same) a
    apply CompactReadoutEffect.ext
    · exact congrArg EffectCoordinates.mu local_eq
    · exact congrArg EffectCoordinates.u local_eq
    · exact congrArg EffectCoordinates.z local_eq
  · funext b
    have local_eq := congrFun (congrArg FamilyCoordinates.bob same) b
    apply CompactReadoutEffect.ext
    · exact congrArg EffectCoordinates.mu local_eq
    · exact congrArg EffectCoordinates.u local_eq
    · exact congrArg EffectCoordinates.z local_eq

/-- Equality of the complete law and two independent local responses identifies all effects. -/
theorem same_law_two_probes_unique (original other : SettingFamily) (regular : Regular original)
    (same : SameLaw other original) (r₀ r₁ : BlochProbe)
    (independent : determinant r₀ r₁ ≠ 0)
    (first_response : r₀.response (other.alice false) = r₀.response (original.alice false))
    (second_response : r₁.response (other.alice false) = r₁.response (original.alice false)) :
    other = original := by
  have law := (same_law_iff_identified other original).mp same
  have other_regular : Regular other := by
    constructor
    · change other.identified.productX false false ≠ 0
      rw [law]
      exact regular.1
    · change other.identified.productZ false false ≠ 0
      rw [law]
      exact regular.2
  have recovered_law : other.recovered = original.recovered := by
    rw [other.recovered_eq_identified, original.recovered_eq_identified, law]
  apply familyCoordinates_injective
  rw [← reconstruct_eq other other_regular r₀ r₁ independent,
    ← reconstruct_eq original regular r₀ r₁ independent,
    recovered_law, first_response, second_response]

/-- Source/current/next transports remain the fixed original occurrence after inverse recovery. -/
theorem anchored_same_occurrence (original other : SettingFamily) (regular : Regular original)
    (same : SameLaw other original) (r₀ r₁ : BlochProbe)
    (independent : determinant r₀ r₁ ≠ 0)
    (first_response : r₀.response (other.alice false) = r₀.response (original.alice false))
    (second_response : r₁.response (other.alice false) = r₁.response (original.alice false))
    (point : BasePoint) (plus a b x y : Bool) :
    other = original ∧
      other.sourceProbability point plus a b x y = original.sourceProbability point plus a b x y ∧
      other.currentProbability point plus a b x y = original.currentProbability point plus a b x y ∧
      other.nextProbability point plus a b x y = original.nextProbability point plus a b x y := by
  have recovered := same_law_two_probes_unique original other regular same r₀ r₁ independent
    first_response second_response
  exact ⟨recovered, by rw [recovered], by rw [recovered], by rw [recovered]⟩

/-- The X and Z product anchors may occupy different settings on either side. -/
def RegularAt (family : SettingFamily) (ax bx az bz : Bool) : Prop :=
  (family.alice ax).u * (family.bob bx).u ≠ 0 ∧
    (family.alice az).z * (family.bob bz).z ≠ 0

theorem regular_at_scale_relation (original other : SettingFamily) (ax bx az bz : Bool)
    (regular : RegularAt original ax bx az bz) (same : SameLaw other original) :
    ScaleRelation original other ((other.alice ax).u / (original.alice ax).u)
      ((other.alice az).z / (original.alice az).z) := by
  have law := (same_law_iff_identified other original).mp same
  have products_x : ∀ a b, (other.alice a).u * (other.bob b).u =
      (original.alice a).u * (original.bob b).u :=
    fun a b => congrFun (congrFun (congrArg IdentifiedCoordinates.productX law) a) b
  have products_z : ∀ a b, (other.alice a).z * (other.bob b).z =
      (original.alice a).z * (original.bob b).z :=
    fun a b => congrFun (congrFun (congrArg IdentifiedCoordinates.productZ law) a) b
  have x_scale := rank_one_scale (fun a => (original.alice a).u)
    (fun b => (original.bob b).u) (fun a => (other.alice a).u)
    (fun b => (other.bob b).u) ax bx regular.1 products_x
  have z_scale := rank_one_scale (fun a => (original.alice a).z)
    (fun b => (original.bob b).z) (fun a => (other.alice a).z)
    (fun b => (other.bob b).z) az bz regular.2 products_z
  exact
    { s_nonzero := x_scale.1
      t_nonzero := z_scale.1
      alice_mu := fun a => congrFun (congrArg IdentifiedCoordinates.aliceBias law) a
      bob_mu := fun b => congrFun (congrArg IdentifiedCoordinates.bobBias law) b
      alice_u := x_scale.2.1
      bob_u := x_scale.2.2
      alice_z := z_scale.2.1
      bob_z := z_scale.2.2 }

/-- Relative local directions are computed from the identifiable product matrices. -/
def relativeX (law : IdentifiedCoordinates) (ax bx setting : Bool) : ℝ :=
  law.productX setting bx / law.productX ax bx

def relativeZ (law : IdentifiedCoordinates) (az bz setting : Bool) : ℝ :=
  law.productZ setting bz / law.productZ az bz

theorem relative_x_eq (family : SettingFamily) (ax bx az bz setting : Bool)
    (regular : RegularAt family ax bx az bz) :
    relativeX family.identified ax bx setting = (family.alice setting).u / (family.alice ax).u := by
  simp only [relativeX, SettingFamily.identified]
  field_simp [(mul_ne_zero_iff.mp regular.1).1, (mul_ne_zero_iff.mp regular.1).2]

theorem relative_z_eq (family : SettingFamily) (ax bx az bz setting : Bool)
    (regular : RegularAt family ax bx az bz) :
    relativeZ family.identified az bz setting = (family.alice setting).z / (family.alice az).z := by
  simp only [relativeZ, SettingFamily.identified]
  field_simp [(mul_ne_zero_iff.mp regular.2).1, (mul_ne_zero_iff.mp regular.2).2]

/-- Probe coefficient rows come from the complete law and known preparations. -/
def coefficientX (law : IdentifiedCoordinates) (ax bx setting : Bool) (r : BlochProbe) : ℝ :=
  relativeX law ax bx setting * r.x

def coefficientZ (law : IdentifiedCoordinates) (az bz setting : Bool) (r : BlochProbe) : ℝ :=
  relativeZ law az bz setting * r.z

def splitDeterminant (law : IdentifiedCoordinates) (ax bx az bz s₀ s₁ : Bool)
    (r₀ r₁ : BlochProbe) : ℝ :=
  coefficientX law ax bx s₀ r₀ * coefficientZ law az bz s₁ r₁ -
    coefficientX law ax bx s₁ r₁ * coefficientZ law az bz s₀ r₀

def splitU (law : IdentifiedCoordinates) (ax bx az bz s₀ s₁ : Bool)
    (r₀ r₁ : BlochProbe) (m₀ m₁ : ℝ) : ℝ :=
  ((m₀ - law.aliceBias s₀) * coefficientZ law az bz s₁ r₁ -
    (m₁ - law.aliceBias s₁) * coefficientZ law az bz s₀ r₀) /
      splitDeterminant law ax bx az bz s₀ s₁ r₀ r₁

def splitZ (law : IdentifiedCoordinates) (ax bx az bz s₀ s₁ : Bool)
    (r₀ r₁ : BlochProbe) (m₀ m₁ : ℝ) : ℝ :=
  (coefficientX law ax bx s₀ r₀ * (m₁ - law.aliceBias s₁) -
    coefficientX law ax bx s₁ r₁ * (m₀ - law.aliceBias s₀)) /
      splitDeterminant law ax bx az bz s₀ s₁ r₀ r₁

theorem split_response_eq (family : SettingFamily) (ax bx az bz setting : Bool)
    (regular : RegularAt family ax bx az bz) (r : BlochProbe) :
    r.response (family.alice setting) - family.identified.aliceBias setting =
      coefficientX family.identified ax bx setting r * (family.alice ax).u +
        coefficientZ family.identified az bz setting r * (family.alice az).z := by
  simp only [coefficientX, coefficientZ]
  rw [relative_x_eq family ax bx az bz setting regular,
    relative_z_eq family ax bx az bz setting regular]
  simp only [BlochProbe.response, SettingFamily.identified]
  field_simp [(mul_ne_zero_iff.mp regular.1).1, (mul_ne_zero_iff.mp regular.2).1]
  ring

theorem split_u_eq (family : SettingFamily) (ax bx az bz s₀ s₁ : Bool)
    (regular : RegularAt family ax bx az bz) (r₀ r₁ : BlochProbe)
    (independent : splitDeterminant family.identified ax bx az bz s₀ s₁ r₀ r₁ ≠ 0) :
    splitU family.identified ax bx az bz s₀ s₁ r₀ r₁
      (r₀.response (family.alice s₀)) (r₁.response (family.alice s₁)) = (family.alice ax).u := by
  apply (div_eq_iff independent).mpr
  rw [split_response_eq family ax bx az bz s₀ regular,
    split_response_eq family ax bx az bz s₁ regular]
  simp only [splitDeterminant]
  ring

theorem split_z_eq (family : SettingFamily) (ax bx az bz s₀ s₁ : Bool)
    (regular : RegularAt family ax bx az bz) (r₀ r₁ : BlochProbe)
    (independent : splitDeterminant family.identified ax bx az bz s₀ s₁ r₀ r₁ ≠ 0) :
    splitZ family.identified ax bx az bz s₀ s₁ r₀ r₁
      (r₀.response (family.alice s₀)) (r₁.response (family.alice s₁)) = (family.alice az).z := by
  apply (div_eq_iff independent).mpr
  rw [split_response_eq family ax bx az bz s₀ regular,
    split_response_eq family ax bx az bz s₁ regular]
  simp only [splitDeterminant]
  ring

/-- Split-setting reconstruction accepts only law readouts and the two observed means. -/
def reconstructSplit (law : IdentifiedCoordinates) (ax bx az bz s₀ s₁ : Bool)
    (r₀ r₁ : BlochProbe) (m₀ m₁ : ℝ) : FamilyCoordinates :=
  let anchorU := splitU law ax bx az bz s₀ s₁ r₀ r₁ m₀ m₁
  let anchorZ := splitZ law ax bx az bz s₀ s₁ r₀ r₁ m₀ m₁
  { alice := fun a =>
      ⟨law.aliceBias a, relativeX law ax bx a * anchorU, relativeZ law az bz a * anchorZ⟩
    bob := fun b =>
      ⟨law.bobBias b, law.productX ax b / anchorU, law.productZ az b / anchorZ⟩ }

theorem reconstruct_split_eq (family : SettingFamily) (ax bx az bz s₀ s₁ : Bool)
    (regular : RegularAt family ax bx az bz) (r₀ r₁ : BlochProbe)
    (independent : splitDeterminant family.recovered ax bx az bz s₀ s₁ r₀ r₁ ≠ 0) :
    reconstructSplit family.recovered ax bx az bz s₀ s₁ r₀ r₁
      (r₀.response (family.alice s₀)) (r₁.response (family.alice s₁)) = familyCoordinates family := by
  rw [family.recovered_eq_identified] at independent ⊢
  simp only [reconstructSplit, split_u_eq family ax bx az bz s₀ s₁ regular r₀ r₁ independent,
    split_z_eq family ax bx az bz s₀ s₁ regular r₀ r₁ independent]
  apply FamilyCoordinates.ext
  · funext a
    simp only [familyCoordinates, coordinates,
      relative_x_eq family ax bx az bz a regular, relative_z_eq family ax bx az bz a regular]
    apply EffectCoordinates.ext
    · rfl
    · field_simp [(mul_ne_zero_iff.mp regular.1).1]
    · field_simp [(mul_ne_zero_iff.mp regular.2).1]
  · funext b
    simp only [familyCoordinates, coordinates, SettingFamily.identified]
    apply EffectCoordinates.ext
    · rfl
    · field_simp [(mul_ne_zero_iff.mp regular.1).1]
    · field_simp [(mul_ne_zero_iff.mp regular.2).1]

theorem same_law_split_probes_unique (original other : SettingFamily)
    (ax bx az bz s₀ s₁ : Bool) (regular : RegularAt original ax bx az bz)
    (same : SameLaw other original) (r₀ r₁ : BlochProbe)
    (independent : splitDeterminant original.recovered ax bx az bz s₀ s₁ r₀ r₁ ≠ 0)
    (first_response : r₀.response (other.alice s₀) = r₀.response (original.alice s₀))
    (second_response : r₁.response (other.alice s₁) = r₁.response (original.alice s₁)) :
    other = original := by
  have law := (same_law_iff_identified other original).mp same
  have other_regular : RegularAt other ax bx az bz := by
    constructor
    · change other.identified.productX ax bx ≠ 0
      rw [law]
      exact regular.1
    · change other.identified.productZ az bz ≠ 0
      rw [law]
      exact regular.2
  have recovered_law : other.recovered = original.recovered := by
    rw [other.recovered_eq_identified, original.recovered_eq_identified, law]
  have other_independent : splitDeterminant other.recovered ax bx az bz s₀ s₁ r₀ r₁ ≠ 0 := by
    rw [recovered_law]
    exact independent
  apply familyCoordinates_injective
  rw [← reconstruct_split_eq other ax bx az bz s₀ s₁ other_regular r₀ r₁ other_independent,
    ← reconstruct_split_eq original ax bx az bz s₀ s₁ regular r₀ r₁ independent,
    recovered_law, first_response, second_response]

end
end SaturationMonoid.PhysicsCore.Stage10.Bell.ReadoutAnchors
