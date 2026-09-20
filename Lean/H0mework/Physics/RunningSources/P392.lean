import H0mework.Physics.RunningSources.P391

/-!
# Proposition 392: independent RG coordinates exclude the tautological normal form

P391 proves the exact boundary of the current coordinate RG surface: because
`CoordinateRGMonotonicityProducer` does not require an independent physical
scale coordinate, every P383 corridor can be normalized by taking the coordinate
to be `g(scale)^2` itself.

This file names the stronger object needed for a non-tautological RG witness.
It adds one semantic side condition: the coordinate must differ from the
canonical `g^2` coordinate at some scale.  The new producer still implies the
P384 grand-unification receipt, but P391's canonical coordinate is rejected.

Thus the current "grand-unification holy grail" obligation is sharpened:
provide a real coordinate / threshold semantics witness, not merely the
identity coordinate in disguise.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Non-tautological coordinate semantics -/

/-- A coordinate is non-tautological when it is not definitionally just the
squared gauge coupling.  The witness is intentionally concrete: one scale where
the coordinate differs from `g(scale)^2`. -/
structure NonTautologicalRGCoordinateSemantics
    {Index A CKMCarrier : Type*} [AddCommGroup A]
    (Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier)
    (coord : StandardModelScaleCode -> ℝ) where
  witnessScale : StandardModelScaleCode
  coordinate_ne_gaugeCouplingSq :
    coord witnessScale ≠ (Z.running.gaugeCoupling witnessScale) ^ (2 : Nat)

namespace NonTautologicalRGCoordinateSemantics

variable {Index A CKMCarrier : Type*} [AddCommGroup A]
variable {Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier}
variable {coord : StandardModelScaleCode -> ℝ}

/-- THEOREM 1: a pointwise non-tautology witness proves the whole coordinate
function is not the canonical `g^2` function. -/
theorem coord_ne_gaugeCouplingSq_fun
    (S : NonTautologicalRGCoordinateSemantics Z coord) :
    coord ≠ fun a => (Z.running.gaugeCoupling a) ^ (2 : Nat) := by
  intro h
  exact S.coordinate_ne_gaugeCouplingSq
    (congrArg (fun f : StandardModelScaleCode -> ℝ => f S.witnessScale) h)

end NonTautologicalRGCoordinateSemantics

/-- THEOREM 2: the canonical `g^2` coordinate cannot satisfy the strengthened
non-tautological semantics. -/
theorem no_nonTautological_gaugeCouplingSqCoordinate
    {Index A CKMCarrier : Type*} [AddCommGroup A]
    (Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier) :
    ¬ Nonempty
        (NonTautologicalRGCoordinateSemantics Z
          (fun a => (Z.running.gaugeCoupling a) ^ (2 : Nat))) := by
  rintro ⟨S⟩
  exact S.coordinate_ne_gaugeCouplingSq rfl

/-- THEOREM 3: in particular, P391's canonical coordinate normalization is
rejected by the strengthened semantics. -/
theorem gaugeCouplingSqCoordinateRGProducer_not_nonTautological
    {Index A CKMCarrier : Type*} [AddCommGroup A]
    {Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier}
    (C : SelectedYukawaRGMonotonicityCertificate Z) :
    ¬ Nonempty
        (NonTautologicalRGCoordinateSemantics Z
          C.toGaugeCouplingSqCoordinateRGProducer.rgCoordinate) := by
  simpa
    [SelectedYukawaRGMonotonicityCertificate.toGaugeCouplingSqCoordinateRGProducer]
    using no_nonTautological_gaugeCouplingSqCoordinate (Z := Z)

/-! ## Independent coordinate producer -/

/-- A scalar-coordinate RG producer strengthened with an explicit independence
condition.  This is the producer a physical RG / threshold calculation must now
fill if it wants to avoid P391's tautological `coord = g^2` normalization. -/
structure IndependentRGCoordinateProducer
    {Index A CKMCarrier : Type*} [AddCommGroup A]
    (Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier) where
  rgCoordinate : StandardModelScaleCode -> ℝ
  fourPi_pos : 0 < Z.running.fourPi
  selected_yukawa_coord_le_weak :
    ∀ y : YukawaParameter,
      rgCoordinate (StandardModelScaleCode.yukawa y) ≤
        rgCoordinate StandardModelScaleCode.weak
  gaugeCouplingSq_monotone_on_coordinate :
    ∀ {a b : StandardModelScaleCode}, rgCoordinate a ≤ rgCoordinate b ->
      (Z.running.gaugeCoupling a) ^ (2 : Nat) ≤
        (Z.running.gaugeCoupling b) ^ (2 : Nat)
  nonTautological :
    NonTautologicalRGCoordinateSemantics Z rgCoordinate

namespace IndependentRGCoordinateProducer

variable {Index A CKMCarrier : Type*} [AddCommGroup A]
variable {Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier}

/-- Forget the independence side condition and recover P385's coordinate
producer. -/
def toCoordinateRGMonotonicityProducer
    (C : IndependentRGCoordinateProducer Z) :
    CoordinateRGMonotonicityProducer Z :=
  { rgCoordinate := C.rgCoordinate
    fourPi_pos := C.fourPi_pos
    selected_yukawa_coord_le_weak := C.selected_yukawa_coord_le_weak
    gaugeCouplingSq_monotone_on_coordinate :=
      C.gaugeCouplingSq_monotone_on_coordinate }

/-- THEOREM 4: an independent producer really excludes the canonical `g^2`
coordinate as a function. -/
theorem coordinate_ne_gaugeCouplingSq
    (C : IndependentRGCoordinateProducer Z) :
    C.rgCoordinate ≠ fun a => (Z.running.gaugeCoupling a) ^ (2 : Nat) :=
  C.nonTautological.coord_ne_gaugeCouplingSq_fun

/-- Transport the independent coordinate producer to P388's finite coordinate
step normal form. -/
def toCoordinateRGStepPathProducer
    (C : IndependentRGCoordinateProducer Z) :
    CoordinateRGStepPathProducer Z :=
  C.toCoordinateRGMonotonicityProducer.toCoordinateRGStepPathProducer

/-- Transport the independent coordinate producer to P389's coordinate
nine-slot Yukawa table normal form. -/
def toCoordinateYukawaRGPathTableProducer
    (C : IndependentRGCoordinateProducer Z) :
    CoordinateYukawaRGPathTableProducer Z :=
  C.toCoordinateRGStepPathProducer.toCoordinateYukawaRGPathTableProducer

end IndependentRGCoordinateProducer

/-- A zero-free certificate equipped with a non-tautological scalar-coordinate
RG producer. -/
def ExistsZeroFreeIndependentRGCoordinateProducer
    (Index A CKMCarrier : Type*) [AddCommGroup A] : Prop :=
  ∃ Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier,
    Nonempty (IndependentRGCoordinateProducer Z)

/-- THEOREM 5: the independent producer forgets to P385's coordinate producer. -/
theorem existsZeroFreeCoordinateRGProducer_of_independentRGCoordinateProducer
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeIndependentRGCoordinateProducer Index A CKMCarrier ->
      ExistsZeroFreeCoordinateRGProducer Index A CKMCarrier := by
  rintro ⟨Z, ⟨C⟩⟩
  exact ⟨Z, ⟨C.toCoordinateRGMonotonicityProducer⟩⟩

/-- THEOREM 6: the independent producer therefore supplies P383's RG
monotonicity corridor. -/
theorem existsZeroFreeRGMonotonicityCorridor_of_independentRGCoordinateProducer
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeIndependentRGCoordinateProducer Index A CKMCarrier ->
      ExistsZeroFreeRGMonotonicityCorridor Index A CKMCarrier :=
  existsZeroFreeRGMonotonicityCorridor_of_coordinateRGProducer ∘
    existsZeroFreeCoordinateRGProducer_of_independentRGCoordinateProducer

/-- THEOREM 7: the independent producer constructs the P384 grand-unification
receipt. -/
theorem rgMonotonicityGrandUnificationReceipt_nonempty_of_independentRGCoordinateProducer
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeIndependentRGCoordinateProducer Index A CKMCarrier ->
      Nonempty (RGMonotonicityGrandUnificationReceipt Index A CKMCarrier) :=
  rgMonotonicityGrandUnificationReceipt_nonempty_of_coordinateRGProducer ∘
    existsZeroFreeCoordinateRGProducer_of_independentRGCoordinateProducer

/-- THEOREM 8: the independent producer supplies the coordinate-certified
nine-slot Yukawa table. -/
theorem existsZeroFreeCoordinateYukawaRGPathTableProducer_of_independentRGCoordinateProducer
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeIndependentRGCoordinateProducer Index A CKMCarrier ->
      ExistsZeroFreeCoordinateYukawaRGPathTableProducer Index A CKMCarrier := by
  intro h
  exact
    (existsZeroFreeCoordinateYukawaRGPathTableProducer_iff_coordinateRGProducer).2
      (existsZeroFreeCoordinateRGProducer_of_independentRGCoordinateProducer h)

/-- THEOREM 9: the strengthened surface is exactly P385's coordinate producer
plus one additional non-tautological semantics witness.  This is the precise
extra obligation left after P391. -/
theorem existsZeroFreeIndependentRGCoordinateProducer_iff_coordinateRGProducer_with_nonTautological
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeIndependentRGCoordinateProducer Index A CKMCarrier ↔
      ∃ Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier,
        ∃ C : CoordinateRGMonotonicityProducer Z,
          Nonempty (NonTautologicalRGCoordinateSemantics Z C.rgCoordinate) := by
  constructor
  · rintro ⟨Z, ⟨C⟩⟩
    exact ⟨Z, C.toCoordinateRGMonotonicityProducer, ⟨C.nonTautological⟩⟩
  · rintro ⟨Z, C, ⟨S⟩⟩
    exact
      ⟨Z,
        ⟨{ rgCoordinate := C.rgCoordinate
           fourPi_pos := C.fourPi_pos
           selected_yukawa_coord_le_weak := C.selected_yukawa_coord_le_weak
           gaugeCouplingSq_monotone_on_coordinate :=
             C.gaugeCouplingSq_monotone_on_coordinate
           nonTautological := S }⟩⟩

end StandardModelConstraint
end SaturationMonoid
