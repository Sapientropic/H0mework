import H0mework.Arithmetic.ZetaReadout.P324

/-!
# Proposition 325: arithmetic-admissible seven-facet domain for the Euler pullback

P324 identified the correct carrier shape after the product carrier failed:
an Euler-coupled pullback over a common prime shadow.  This file closes the
next domain boundary.

The original P318 `SevenFacetCarrier` has an unconstrained real `rate` field.
The P324 arithmetic projection, however, is the half-sigma exponent image, not
all of `R`.  Therefore the whole seven-facet carrier cannot be lifted into the
Euler pullback while preserving the rate coordinate.  The proof is concrete:
rate `2` is a legal seven-facet point, but every half-sigma exponent-image
rate is `< 1`.

The correct next domain is the arithmetic-admissible subcarrier: seven-facet
states whose rate is witnessed by a half-sigma arithmetic image point.  On this
subcarrier, any producer of the remaining shadow-equality law lifts uniquely
into the P324 pullback carrier, and any common shadow predicate synchronizes
the concrete Goldbach and H1 no-obstruction predicates under the explicit
projection-fidelity assumptions.

Boundary: this is still not Goldbach, RH, or a concrete prime-shadow producer.
It proves the necessary domain shrink and the exact adapter needed by such a
producer.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

open SatOrFieldAlgebra

/-! ## Half-sigma image rates stay below one -/

/-- THEOREM 1: every point of the nondegenerate sigma exponent image has rate
strictly below `1`. -/
theorem sigmaExponentImage_val_lt_one_of_mem_Ioo
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {σ : K} (_hσ0 : 0 < σ) (hσ1 : σ < 1)
    (r : SigmaExponentImage σ) :
    r.1 < 1 := by
  have hkeep_pos : 0 < (1 - σ) ^ SigmaExponentImage.exponent r :=
    pow_pos (sub_pos.mpr hσ1) _
  have hres : 1 - r.1 = (1 - σ) ^ SigmaExponentImage.exponent r := by
    calc
      1 - r.1 = 1 - iteratedRate σ (SigmaExponentImage.exponent r) := by
        rw [SigmaExponentImage.val_eq_iteratedRate_exponent r]
      _ = (1 - σ) ^ SigmaExponentImage.exponent r :=
        keep_iteratedRate σ (SigmaExponentImage.exponent r)
  have : 0 < 1 - r.1 := by
    simpa [hres] using hkeep_pos
  exact sub_pos.mp this

/-- THEOREM 2: at the self-dual point, every arithmetic-image rate is below
`1`. -/
theorem halfSigmaArithmeticImage_val_lt_one
    (r : HalfSigmaArithmeticImage) :
    r.1 < (1 : ℝ) :=
  sigmaExponentImage_val_lt_one_of_mem_Ioo
    halfSigma_mem_Ioo.1 halfSigma_mem_Ioo.2 r

/-! ## The full seven-facet carrier is too large -/

/-- A legal seven-facet point whose rate is outside the half-sigma arithmetic
image. -/
def outOfArithmeticImageSevenFacetPoint : SevenFacetCarrier (1 / 2 : ℝ) where
  facets := fun _ => True
  rate := 2
  phase := fun _ _ => 0
  analytic := 0

/-- THEOREM 3: the witness rate `2` is not the value of any half-sigma
arithmetic-image point. -/
theorem two_not_halfSigmaArithmeticImage_value
    (r : HalfSigmaArithmeticImage) :
    r.1 ≠ (2 : ℝ) := by
  intro h
  have hlt : r.1 < (1 : ℝ) := halfSigmaArithmeticImage_val_lt_one r
  linarith

/-- THEOREM 4: there is no rate-preserving lift from the entire seven-facet
carrier into the half-sigma arithmetic image.  Thus a concrete Euler pullback
producer must first restrict the domain to arithmetic-admissible states. -/
theorem no_global_rate_preserving_halfSigma_lift :
    Not
      (∃ arithOf : SevenFacetCarrier (1 / 2 : ℝ) -> HalfSigmaArithmeticImage,
        ∀ x : SevenFacetCarrier (1 / 2 : ℝ),
          (arithOf x).1 = x.rate) := by
  rintro ⟨arithOf, hrate⟩
  have htwo : (arithOf outOfArithmeticImageSevenFacetPoint).1 = (2 : ℝ) := by
    simpa [outOfArithmeticImageSevenFacetPoint] using
      hrate outOfArithmeticImageSevenFacetPoint
  exact two_not_halfSigmaArithmeticImage_value
    (arithOf outOfArithmeticImageSevenFacetPoint) htwo

/-! ## Arithmetic-admissible seven-facet subcarrier -/

/-- A seven-facet state is arithmetic-admissible when its real rate coordinate
is actually a point of the half-sigma arithmetic image. -/
def ArithmeticAdmissibleSevenFacet : Type :=
  { x : SevenFacetCarrier (1 / 2 : ℝ) //
      ∃ r : HalfSigmaArithmeticImage, r.1 = x.rate }

namespace ArithmeticAdmissibleSevenFacet

/-- The underlying seven-facet point. -/
def val (x : ArithmeticAdmissibleSevenFacet) :
    SevenFacetCarrier (1 / 2 : ℝ) :=
  x.1

/-- The chosen half-sigma arithmetic-image point witnessing admissibility. -/
def arithmetic (x : ArithmeticAdmissibleSevenFacet) :
    HalfSigmaArithmeticImage :=
  Classical.choose x.2

/-- THEOREM 5: the chosen arithmetic witness preserves the original rate. -/
theorem arithmetic_rate_eq (x : ArithmeticAdmissibleSevenFacet) :
    (arithmetic x).1 = x.val.rate :=
  Classical.choose_spec x.2

/-- The H1-spectral projection inherited from the seven-facet point. -/
def spectral (x : ArithmeticAdmissibleSevenFacet) :
    H1SpectralProjection (1 / 2 : ℝ) :=
  x.val.spectral

/-- THEOREM 6: named half-sigma exponent points are arithmetic-admissible. -/
def ofArithmetic
    (facets : Fin 7 -> Prop)
    (phase : ThreeCycleTime -> ThreeCycleTime -> ℝ)
    (analytic : ℂ)
    (r : HalfSigmaArithmeticImage) :
    ArithmeticAdmissibleSevenFacet :=
  ⟨SevenFacetCarrier.arithmeticEmbed facets phase analytic r, ⟨r, rfl⟩⟩

/-- THEOREM 7: the admissible embedding preserves the arithmetic rate. -/
theorem ofArithmetic_rate_eq
    (facets : Fin 7 -> Prop)
    (phase : ThreeCycleTime -> ThreeCycleTime -> ℝ)
    (analytic : ℂ)
    (r : HalfSigmaArithmeticImage) :
    (ofArithmetic facets phase analytic r).val.rate = r.1 :=
  rfl

/-! ## Lifting admissible states into the Euler pullback carrier -/

/-- Data saying the remaining prime-shadow producer is defined on the
arithmetic-admissible seven-facet domain. -/
structure EulerAdmissibleLiftData
    (P : EulerPrimeCouplingProducers) where
  shadow_eq :
    ∀ x : ArithmeticAdmissibleSevenFacet,
      P.arithmeticShadow x.arithmetic = P.spectralShadow x.spectral

namespace EulerAdmissibleLiftData

/-- The canonical lift of arithmetic-admissible seven-facet states into the
P324 Euler pullback carrier. -/
def lift {P : EulerPrimeCouplingProducers}
    (D : EulerAdmissibleLiftData P) :
    ArithmeticAdmissibleSevenFacet -> P.Carrier :=
  EulerPrimeCouplingProducers.Carrier.lift
    (P := P) arithmetic spectral D.shadow_eq

/-- THEOREM 8: the admissible lift preserves the arithmetic projection. -/
theorem lift_arithmetic {P : EulerPrimeCouplingProducers}
    (D : EulerAdmissibleLiftData P)
    (x : ArithmeticAdmissibleSevenFacet) :
    EulerPrimeCouplingProducers.Carrier.arithmetic (D.lift x) =
      x.arithmetic :=
  rfl

/-- THEOREM 9: the admissible lift preserves the H1-spectral projection. -/
theorem lift_spectral {P : EulerPrimeCouplingProducers}
    (D : EulerAdmissibleLiftData P)
    (x : ArithmeticAdmissibleSevenFacet) :
    EulerPrimeCouplingProducers.Carrier.spectral (D.lift x) =
      x.spectral :=
  rfl

/-- THEOREM 10: the admissible lift is unique among maps with the same two
projections. -/
theorem lift_unique {P : EulerPrimeCouplingProducers}
    (D : EulerAdmissibleLiftData P)
    (f : ArithmeticAdmissibleSevenFacet -> P.Carrier)
    (ha : ∀ x, EulerPrimeCouplingProducers.Carrier.arithmetic (f x) =
      x.arithmetic)
    (hs : ∀ x, EulerPrimeCouplingProducers.Carrier.spectral (f x) =
      x.spectral) :
    f = D.lift :=
  EulerPrimeCouplingProducers.Carrier.lift_unique
    arithmetic spectral D.shadow_eq f ha hs

end EulerAdmissibleLiftData

/-! ## Concrete synchronization on the admissible domain -/

/-- The remaining concrete admissible bridge: a common predicate on the
producer's prime shadow must pull back to concrete Goldbach on the arithmetic
image and to concrete H1 no-obstruction on the spectral side. -/
structure ConcreteAdmissiblePrimeShadowBridge
    (P : EulerPrimeCouplingProducers) extends EulerAdmissibleLiftData P where
  commonComplete : P.PrimeShadow -> Prop
  common_arithmetic :
    ∀ r : HalfSigmaArithmeticImage,
      commonComplete (P.arithmeticShadow r) ↔
        HalfSigmaImageGoldbachComplete r
  common_spectral :
    ∀ s : H1SpectralProjection (1 / 2 : ℝ),
      commonComplete (P.spectralShadow s) ↔
        H1SpectralNoObstructionComplete s

namespace ConcreteAdmissiblePrimeShadowBridge

/-- THEOREM 11: a concrete admissible prime-shadow bridge synchronizes the
Goldbach and H1 no-obstruction predicates on every admissible seven-facet
state. -/
theorem goldbach_iff_h1_no_obstruction
    {P : EulerPrimeCouplingProducers}
    (B : ConcreteAdmissiblePrimeShadowBridge P)
    (x : ArithmeticAdmissibleSevenFacet) :
    HalfSigmaImageGoldbachComplete x.arithmetic ↔
      H1SpectralNoObstructionComplete x.spectral := by
  have hcommon :=
    EulerPrimeCouplingProducers.Carrier.arithmetic_iff_spectral
      (P := P) B.commonComplete (B.toEulerAdmissibleLiftData.lift x)
  have harith :
      EulerPrimeCouplingProducers.Carrier.arithmetic
          (B.toEulerAdmissibleLiftData.lift x) = x.arithmetic := rfl
  have hspec :
      EulerPrimeCouplingProducers.Carrier.spectral
          (B.toEulerAdmissibleLiftData.lift x) = x.spectral := rfl
  rw [harith, hspec] at hcommon
  exact (B.common_arithmetic x.arithmetic).symm.trans
    (hcommon.trans (B.common_spectral x.spectral))

/-- THEOREM 12: using the rate witness, the same synchronization can be read
on the original real rate coordinate. -/
theorem rateGoldbach_iff_h1_no_obstruction
    {P : EulerPrimeCouplingProducers}
    (B : ConcreteAdmissiblePrimeShadowBridge P)
    (x : ArithmeticAdmissibleSevenFacet) :
    HalfSigmaRateGoldbachComplete x.val.rate ↔
      H1SpectralNoObstructionComplete x.spectral := by
  have hrateImage := halfSigmaRateGoldbachComplete_of_image x.arithmetic
  have hrate : (x.arithmetic).1 = x.val.rate := arithmetic_rate_eq x
  have hrate' :
      HalfSigmaRateGoldbachComplete x.val.rate ↔
        HalfSigmaImageGoldbachComplete x.arithmetic := by
    rw [← hrate]
    exact hrateImage
  exact hrate'.trans (B.goldbach_iff_h1_no_obstruction x)

end ConcreteAdmissiblePrimeShadowBridge

end ArithmeticAdmissibleSevenFacet

/-! ## Packaged domain certificate -/

/-- The domain-shrink certificate forced by P324. -/
structure ArithmeticAdmissibleDomainCertificate where
  image_rates_below_one :
    ∀ r : HalfSigmaArithmeticImage, r.1 < (1 : ℝ)
  out_of_image_point : SevenFacetCarrier (1 / 2 : ℝ)
  out_of_image_point_rate : out_of_image_point.rate = (2 : ℝ)
  no_global_rate_preserving_lift :
    Not
      (∃ arithOf : SevenFacetCarrier (1 / 2 : ℝ) -> HalfSigmaArithmeticImage,
        ∀ x : SevenFacetCarrier (1 / 2 : ℝ),
          (arithOf x).1 = x.rate)
  admissible_carrier : Type
  admissible_underlying :
    admissible_carrier -> SevenFacetCarrier (1 / 2 : ℝ)
  admissible_rate_witness :
    admissible_carrier -> HalfSigmaArithmeticImage
  admissible_rate_eq :
    ∀ x : admissible_carrier,
      (admissible_rate_witness x).1 =
        (admissible_underlying x).rate

/-- THEOREM 13: the canonical arithmetic-admissible domain certificate. -/
def arithmeticAdmissibleDomainCertificate :
    ArithmeticAdmissibleDomainCertificate where
  image_rates_below_one := halfSigmaArithmeticImage_val_lt_one
  out_of_image_point := outOfArithmeticImageSevenFacetPoint
  out_of_image_point_rate := rfl
  no_global_rate_preserving_lift := no_global_rate_preserving_halfSigma_lift
  admissible_carrier := ArithmeticAdmissibleSevenFacet
  admissible_underlying := ArithmeticAdmissibleSevenFacet.val
  admissible_rate_witness := ArithmeticAdmissibleSevenFacet.arithmetic
  admissible_rate_eq := ArithmeticAdmissibleSevenFacet.arithmetic_rate_eq

end AffineRelaxation
end SaturationMonoid
