import H0mework.Physics.RunningSources.P384

/-!
# Proposition 385: coordinate RG producer for the grand-unification receipt

P383 names the remaining RG/threshold obligation as an abstract scale relation
plus monotonicity of `g^2` along that relation.  P384 packages the whole
Standard-Model-facing receipt once that producer is available.

This file lowers the producer one step: it is enough to provide a single real
RG coordinate on the finite scale-code carrier.  The relation is then the
canonical coordinate order `coord a <= coord b`, and the P383 producer is
generated automatically.

Boundary: the coordinate itself, its physical orientation, and the beta /
threshold proof that `g^2` is monotone in that coordinate are still producer
data.  The gain here is that the remaining physical obligation now has the
shape of a scalar monotonicity theorem, rather than an arbitrary relation.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Coordinate RG producer -/

/-- A scalar-coordinate version of the P383 RG monotonicity producer.

Future RG work should aim to fill this object from an actual scale coordinate
and a beta/threshold monotonicity theorem. -/
structure CoordinateRGMonotonicityProducer
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

namespace CoordinateRGMonotonicityProducer

variable {Index A CKMCarrier : Type*} [AddCommGroup A]
variable {Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier}

/-- THEOREM 1: the coordinate order is reflexive. -/
theorem scaleLe_refl
    (C : CoordinateRGMonotonicityProducer Z)
    (a : StandardModelScaleCode) :
    C.rgCoordinate a ≤ C.rgCoordinate a :=
  le_rfl

/-- THEOREM 2: the coordinate order is transitive. -/
theorem scaleLe_trans
    (C : CoordinateRGMonotonicityProducer Z)
    {a b c : StandardModelScaleCode}
    (hab : C.rgCoordinate a ≤ C.rgCoordinate b)
    (hbc : C.rgCoordinate b ≤ C.rgCoordinate c) :
    C.rgCoordinate a ≤ C.rgCoordinate c :=
  le_trans hab hbc

/-- A coordinate producer generates the P383 RG monotonicity
certificate by taking `scaleLe a b` to mean `coord a <= coord b`. -/
def toSelectedYukawaRGMonotonicityCertificate
    (C : CoordinateRGMonotonicityProducer Z) :
    SelectedYukawaRGMonotonicityCertificate Z :=
  { scaleLe := fun a b => C.rgCoordinate a ≤ C.rgCoordinate b
    fourPi_pos := C.fourPi_pos
    selected_yukawa_le_weak := C.selected_yukawa_coord_le_weak
    gaugeCouplingSq_monotone :=
      fun h => C.gaugeCouplingSq_monotone_on_coordinate h }

/-- THEOREM 4: therefore a coordinate producer gives P382's gauge weak
corridor. -/
theorem toSelectedYukawaGaugeCouplingsBoundedByWeak
    (C : CoordinateRGMonotonicityProducer Z) :
    SelectedYukawaGaugeCouplingsBoundedByWeak Z :=
  selectedYukawaGaugeCouplingsBoundedByWeak_of_rgMonotonicity Z
    C.toSelectedYukawaRGMonotonicityCertificate

end CoordinateRGMonotonicityProducer

/-- A zero-free certificate equipped with a scalar-coordinate RG producer. -/
def ExistsZeroFreeCoordinateRGProducer
    (Index A CKMCarrier : Type*) [AddCommGroup A] : Prop :=
  ∃ Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier,
    Nonempty (CoordinateRGMonotonicityProducer Z)

/-- THEOREM 5: the scalar-coordinate producer supplies P383's RG monotonicity
corridor. -/
theorem existsZeroFreeRGMonotonicityCorridor_of_coordinateRGProducer
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeCoordinateRGProducer Index A CKMCarrier ->
      ExistsZeroFreeRGMonotonicityCorridor Index A CKMCarrier := by
  rintro ⟨Z, ⟨C⟩⟩
  exact ⟨Z, ⟨C.toSelectedYukawaRGMonotonicityCertificate⟩⟩

/-- THEOREM 6: a scalar-coordinate RG producer constructs the full P384
grand-unification receipt. -/
theorem rgMonotonicityGrandUnificationReceipt_nonempty_of_coordinateRGProducer
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeCoordinateRGProducer Index A CKMCarrier ->
      Nonempty (RGMonotonicityGrandUnificationReceipt Index A CKMCarrier) := by
  intro h
  exact
    rgMonotonicityGrandUnificationReceipt_nonempty_of_exists
      (existsZeroFreeRGMonotonicityCorridor_of_coordinateRGProducer h)

/-- THEOREM 7: hence the P374 unified-formula spine is available from the
coordinate RG producer. -/
theorem unifiedFormulaSpine_nonempty_of_coordinateRGProducer
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeCoordinateRGProducer Index A CKMCarrier ->
      Nonempty (StandardModelUnifiedFormulaSpineCertificate Index A CKMCarrier) := by
  intro h
  exact
    unifiedFormulaSpine_nonempty_iff_rgMonotonicityReceipt_nonempty
      (rgMonotonicityGrandUnificationReceipt_nonempty_of_coordinateRGProducer h)

/-- THEOREM 8: and the primitive producer atoms are available from the same
coordinate RG producer. -/
theorem primitiveProducerAtoms_nonempty_of_coordinateRGProducer
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeCoordinateRGProducer Index A CKMCarrier ->
      Nonempty (GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier) := by
  intro h
  exact
    primitiveProducerAtoms_nonempty_iff_rgMonotonicityReceipt_nonempty
      (rgMonotonicityGrandUnificationReceipt_nonempty_of_coordinateRGProducer h)

end StandardModelConstraint
end SaturationMonoid
