import H0mework.Physics.RunningSources.P392

/-!
# Proposition 393: running sigma as the independent RG coordinate

P392 names the strengthened coordinate producer: a coordinate must not be the
tautological `g(scale)^2` coordinate.

This file moves one step closer to the Standard-Model-facing RG producer.  P274
already identifies running sigma with gauge alpha,

`sigma(scale) = g(scale)^2 / fourPi`.

Therefore sigma itself is a natural scalar RG coordinate.  With `fourPi > 0`,
monotonicity in sigma is equivalent to monotonicity of `g^2`; with
`fourPi != 1` and one nonzero squared coupling, sigma is not the same
coordinate as `g^2`.

The remaining producer obligation is now concrete: supply the running-sigma
corridor from selected Yukawa scales to weak, and the elementary nondegeneracy
data that makes sigma an independent coordinate rather than the identity
coordinate.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Running-sigma coordinate producer data -/

/-- Producer data for using running sigma itself as the independent RG
coordinate.  The nondegeneracy fields ensure that this coordinate is not just
`g^2` in disguise. -/
structure RunningSigmaIndependentCoordinateWitness
    {Index A CKMCarrier : Type*} [AddCommGroup A]
    (Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier) where
  fourPi_pos : 0 < Z.running.fourPi
  fourPi_ne_one : Z.running.fourPi ≠ 1
  selected_yukawa_sigma_le_weak : SelectedYukawaSigmaBoundedByWeak Z
  nonzeroScale : StandardModelScaleCode
  gaugeCouplingSq_ne_zero :
    (Z.running.gaugeCoupling nonzeroScale) ^ (2 : Nat) ≠ 0

namespace RunningSigmaIndependentCoordinateWitness

variable {Index A CKMCarrier : Type*} [AddCommGroup A]
variable {Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier}

/-- THEOREM 1: because `sigma = g^2 / fourPi` with positive common
denominator, sigma-order implies `g^2`-order. -/
theorem gaugeCouplingSq_monotone_on_sigma
    (W : RunningSigmaIndependentCoordinateWitness Z)
    {a b : StandardModelScaleCode}
    (h : Z.running.sigma a ≤ Z.running.sigma b) :
    (Z.running.gaugeCoupling a) ^ (2 : Nat) ≤
      (Z.running.gaugeCoupling b) ^ (2 : Nat) := by
  have hdiv :
      (Z.running.gaugeCoupling a) ^ (2 : Nat) / Z.running.fourPi ≤
        (Z.running.gaugeCoupling b) ^ (2 : Nat) / Z.running.fourPi := by
    simpa [alphaFromGaugeCoupling, Z.running.sigma_eq_alpha a,
      Z.running.sigma_eq_alpha b] using h
  exact (div_le_div_iff_of_pos_right W.fourPi_pos).mp hdiv

/-- THEOREM 2: under the nondegeneracy fields, running sigma cannot be the
same coordinate function as `g^2`. -/
def sigmaCoordinate_nonTautological
    (W : RunningSigmaIndependentCoordinateWitness Z) :
    NonTautologicalRGCoordinateSemantics Z Z.running.sigma where
  witnessScale := W.nonzeroScale
  coordinate_ne_gaugeCouplingSq := by
    intro hsame
    let x : ℝ := (Z.running.gaugeCoupling W.nonzeroScale) ^ (2 : Nat)
    have hsigma :
        Z.running.sigma W.nonzeroScale =
          x / Z.running.fourPi := by
      simpa [x, alphaFromGaugeCoupling] using
        Z.running.sigma_eq_alpha W.nonzeroScale
    have hdiv_eq : x / Z.running.fourPi = x := hsigma.symm.trans hsame
    have hmul := congrArg (fun t : ℝ => t * Z.running.fourPi) hdiv_eq
    field_simp [ne_of_gt W.fourPi_pos] at hmul
    have hfactor : x * (Z.running.fourPi - 1) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hfactor with hx | hfour
    · exact W.gaugeCouplingSq_ne_zero (by simpa [x] using hx)
    · exact W.fourPi_ne_one (by
        nlinarith)

/-- Convert the running-sigma witness to P392's independent coordinate
producer. -/
def toIndependentRGCoordinateProducer
    (W : RunningSigmaIndependentCoordinateWitness Z) :
    IndependentRGCoordinateProducer Z :=
  { rgCoordinate := Z.running.sigma
    fourPi_pos := W.fourPi_pos
    selected_yukawa_coord_le_weak := W.selected_yukawa_sigma_le_weak
    gaugeCouplingSq_monotone_on_coordinate :=
      fun h => W.gaugeCouplingSq_monotone_on_sigma h
    nonTautological := W.sigmaCoordinate_nonTautological }

end RunningSigmaIndependentCoordinateWitness

/-- A zero-free certificate equipped with a running-sigma independent
coordinate witness. -/
def ExistsZeroFreeRunningSigmaIndependentCoordinateWitness
    (Index A CKMCarrier : Type*) [AddCommGroup A] : Prop :=
  ∃ Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier,
    Nonempty (RunningSigmaIndependentCoordinateWitness Z)

/-- THEOREM 3: a running-sigma independent coordinate witness supplies P392's
independent coordinate producer. -/
theorem existsZeroFreeIndependentRGCoordinateProducer_of_runningSigmaCoordinateWitness
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeRunningSigmaIndependentCoordinateWitness Index A CKMCarrier ->
      ExistsZeroFreeIndependentRGCoordinateProducer Index A CKMCarrier := by
  rintro ⟨Z, ⟨W⟩⟩
  exact ⟨Z, ⟨W.toIndependentRGCoordinateProducer⟩⟩

/-- THEOREM 4: consequently, the running-sigma coordinate witness constructs
the P384 grand-unification receipt. -/
theorem rgMonotonicityGrandUnificationReceipt_nonempty_of_runningSigmaCoordinateWitness
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeRunningSigmaIndependentCoordinateWitness Index A CKMCarrier ->
      Nonempty (RGMonotonicityGrandUnificationReceipt Index A CKMCarrier) :=
  rgMonotonicityGrandUnificationReceipt_nonempty_of_independentRGCoordinateProducer ∘
    existsZeroFreeIndependentRGCoordinateProducer_of_runningSigmaCoordinateWitness

/-- THEOREM 5: the running-sigma coordinate witness also supplies the
coordinate-certified nine-slot table normal form. -/
theorem existsZeroFreeCoordinateYukawaRGPathTableProducer_of_runningSigmaCoordinateWitness
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeRunningSigmaIndependentCoordinateWitness Index A CKMCarrier ->
      ExistsZeroFreeCoordinateYukawaRGPathTableProducer Index A CKMCarrier :=
  existsZeroFreeCoordinateYukawaRGPathTableProducer_of_independentRGCoordinateProducer ∘
    existsZeroFreeIndependentRGCoordinateProducer_of_runningSigmaCoordinateWitness

end StandardModelConstraint
end SaturationMonoid
