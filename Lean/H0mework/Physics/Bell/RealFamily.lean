import H0mework.Physics.Bell.Preparation

/-!
# Real-amplitude Born family

Subordinate mathematical producer on the existing eight-dimensional effect carrier.
Preparation is an explicit normalized real pair, not a new source occurrence.
The lower Dirac block is unoccupied in this representative; only Born readouts,
not vectors or source identities, are compared with the original phi preparation.
-/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.Bell.RealFamily

open Matrix Stage9DEF State
open scoped ComplexOrder

noncomputable section

/-- A normalized preparation coordinate, universally quantified by the final mouth. -/
structure Preparation where
  c : ℝ
  s : ℝ
  unit : c^2 + s^2 = 1

/-- Embed c|00⟩ + s|11⟩ in the original effect carrier without changing its source. -/
def vector (p : Preparation) : Source.Index → ℂ :=
  fun i => if i = (0, 0) then p.c else if i = (1, 1) then p.s else 0

/-- The local polarization and the real coherence are generated from the pair. -/
def delta (p : Preparation) : ℝ := p.c^2 - p.s^2
def chi (p : Preparation) : ℝ := 2 * p.c * p.s

theorem vector_normalized (p : Preparation) :
    (∑ i, star (vector p i) * vector p i) = 1 := by
  have h : (p.c : ℂ)^2 + (p.s : ℂ)^2 = 1 := by exact_mod_cast p.unit
  simpa [vector, Fintype.sum_prod_type, Fin.sum_univ_four,
    Fin.sum_univ_two, pow_two] using h

/-- Born evaluation of the unchanged joint effect, before outcome encoding. -/
theorem joint_born (p : Preparation) (ax az bx bz : ℝ)
    (aunit : ax^2 + az^2 = 1) (bunit : bx^2 + bz^2 = 1) :
    (vectorEvaluation (vector p) (jointEffect ax az bx bz aunit bunit).matrix).re =
      (1 + delta p * (az + bz) + az*bz + chi p*ax*bx) / 4 := by
  have h : (p.c : ℂ)^2 + (p.s : ℂ)^2 = 1 := by exact_mod_cast p.unit
  have value : vectorEvaluation (vector p) (jointEffect ax az bx bz aunit bunit).matrix =
      ((1 + delta p * (az + bz) + az*bz + chi p*ax*bx) / 4 : ℝ) := by
    simp [jointEffect, projectorEffect, vectorEvaluation, vector, Matrix.mulVec,
      dotProduct, Fintype.sum_prod_type, Fin.sum_univ_four, Fin.sum_univ_two,
      spinProjector, axisProjector, delta, chi]
    linear_combination (1 + (az : ℂ)*bz) / 4 * h
  exact congrArg Complex.re value

/-- The canonical phi-frame probability; no herald or fitted coordinate is implicit. -/
def probability (p : Preparation) (a b : Axis) (x y : Bool) : ℝ :=
  (1 + delta p * (sign x*a.z + sign y*b.z) +
    sign x*sign y*(a.z*b.z + chi p*a.x*b.x)) / 4

theorem born (p : Preparation) (a b : Axis) (x y : Bool) :
    (vectorEvaluation (vector p) (outcomeEffect a b x y).matrix).re =
      probability p a b x y := by
  rw [outcomeEffect, joint_born]
  simp only [Axis.signed, probability]
  ring

theorem nonnegative (p : Preparation) (a b : Axis) (x y : Bool) :
    0 ≤ probability p a b x y := by
  rw [← born]
  exact (Complex.nonneg_iff.mp
    (vectorEvaluation_positive _ _ (outcomeEffect a b x y).positive)).1

theorem le_one (p : Preparation) (a b : Axis) (x y : Bool) :
    probability p a b x y ≤ 1 := by
  have h := (Complex.nonneg_iff.mp (vectorEvaluation_positive (vector p) _
    (outcomeEffect a b x y).complement_positive)).1
  rw [map_sub, vectorEvaluation_one _ (vector_normalized p), Complex.sub_re,
    Complex.one_re, born] at h
  linarith

theorem normalized (p : Preparation) (a b : Axis) :
    ∑ x : Bool, ∑ y : Bool, probability p a b x y = 1 := by
  simp [probability, sign]
  ring

theorem left_marginal (p : Preparation) (a b : Axis) (x : Bool) :
    ∑ y : Bool, probability p a b x y = (1 + delta p * sign x * a.z) / 2 := by
  simp [probability, sign]; ring

theorem right_marginal (p : Preparation) (a b : Axis) (y : Bool) :
    ∑ x : Bool, probability p a b x y = (1 + delta p * sign y * b.z) / 2 := by
  simp [probability, sign]; ring

theorem correlation (p : Preparation) (a b : Axis) :
    (∑ x : Bool, ∑ y : Bool, sign x*sign y*probability p a b x y) =
      a.z*b.z + chi p*a.x*b.x := by
  simp [probability, sign]; ring

theorem left_mean (p : Preparation) (a b : Axis) :
    (∑ x : Bool, ∑ y : Bool, sign x*probability p a b x y) = delta p*a.z := by
  simp [probability, sign]; ring

theorem right_mean (p : Preparation) (a b : Axis) :
    (∑ x : Bool, ∑ y : Bool, sign y*probability p a b x y) = delta p*b.z := by
  simp [probability, sign]; ring

/-- The pair has no independent polarization/coherence fitting slots. -/
theorem shape (p : Preparation) : (delta p)^2 + (chi p)^2 = 1 := by
  dsimp [delta, chi]
  nlinarith [sq_nonneg (p.c^2 + p.s^2 - 1), p.unit]

/-- Equal amplitudes imply the original phi readout, not equality of source vectors. -/
theorem equal_amplitudes (p : Preparation) (h : p.c = p.s) :
    delta p = 0 ∧ chi p = 1 := by
  dsimp [delta, chi]
  constructor
  · rw [h]; ring
  · nlinarith [p.unit]

theorem phi_reduction (p : Preparation) (h : p.c = p.s) (a b : Axis) (x y : Bool) :
    probability p a b x y =
      Bell.probability a (heraldAxis true (colorXFrame b)) x y := by
  rcases equal_amplitudes p h with ⟨hd, hc⟩
  simp only [probability, hd, hc, Bell.probability, heraldAxis, if_true,
    Axis.reflected, colorXFrame]
  ring

theorem phi_born_reduction (p : Preparation) (h : p.c = p.s)
    (point : ProofFreeRicherAnholonomicSource.BasePoint) (a b : Axis) (x y : Bool) :
    probability p a b x y =
      (vectorEvaluation (phiVector point) (outcomeEffect a b x y).matrix).re := by
  rw [phi_from_fixed_family, phi_reduction p h]

/-- Exact bridge to the legacy psi+ predictor's Bob color-X convention. -/
theorem legacy_frame (p : Preparation) (h : p.c = p.s) (a b : Axis) (x y : Bool) :
    probability p a (colorXFrame b) x y = Bell.probability a (heraldAxis true b) x y := by
  rw [phi_reduction p h]
  simp [Bell.probability, heraldAxis, Axis.reflected, colorXFrame]

/-- Universal conditional Born output; deliberately no source-occurrence extension. -/
structure Prediction : Prop where
  vectorUnit : ∀ p, (∑ i, star (vector p i) * vector p i) = 1
  bornReadout : ∀ p a b x y,
    (vectorEvaluation (vector p) (outcomeEffect a b x y).matrix).re = probability p a b x y
  positive : ∀ p a b x y, 0 ≤ probability p a b x y
  bounded : ∀ p a b x y, probability p a b x y ≤ 1
  total : ∀ p a b, ∑ x : Bool, ∑ y : Bool, probability p a b x y = 1
  leftMarginal : ∀ p a b x,
    ∑ y : Bool, probability p a b x y = (1 + delta p * sign x * a.z) / 2
  rightMarginal : ∀ p a b y,
    ∑ x : Bool, probability p a b x y = (1 + delta p * sign y * b.z) / 2
  correlationReadout : ∀ p a b,
    (∑ x : Bool, ∑ y : Bool, sign x*sign y*probability p a b x y) =
      a.z*b.z + chi p*a.x*b.x
  leftMean : ∀ p a b,
    (∑ x : Bool, ∑ y : Bool, sign x*probability p a b x y) = delta p*a.z
  rightMean : ∀ p a b,
    (∑ x : Bool, ∑ y : Bool, sign y*probability p a b x y) = delta p*b.z
  generatedShape : ∀ p, (delta p)^2 + (chi p)^2 = 1
  phiReduction : ∀ p, p.c = p.s → ∀ a b x y,
    probability p a b x y = Bell.probability a (heraldAxis true (colorXFrame b)) x y
  legacyFrame : ∀ p, p.c = p.s → ∀ a b x y,
    probability p a (colorXFrame b) x y = Bell.probability a (heraldAxis true b) x y

/-- Closed total mouth: the pair is quantified inside, not fitted by a caller. -/
theorem prediction : Prediction where
  vectorUnit := vector_normalized
  bornReadout := born
  positive := nonnegative
  bounded := le_one
  total := normalized
  leftMarginal := left_marginal
  rightMarginal := right_marginal
  correlationReadout := correlation
  leftMean := left_mean
  rightMean := right_mean
  generatedShape := shape
  phiReduction := phi_reduction
  legacyFrame := legacy_frame

end
end SaturationMonoid.PhysicsCore.Stage10.Bell.RealFamily
