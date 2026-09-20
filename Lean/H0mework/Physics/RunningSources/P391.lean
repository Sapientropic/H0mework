import H0mework.Physics.RunningSources.P390

/-!
# Proposition 391: coordinate RG normal forms have no extra existence content

P385 introduced a scalar-coordinate RG producer.  P388/P389 then made that
coordinate producer look more implementation-facing by adding finite local
steps and an explicit nine-slot table.

This file proves the exact existence-level status of those coordinate surfaces.
With the current P385 definition, a P383 RG monotonicity corridor can always be
coordinate-normalized by taking the coordinate to be `g(scale)^2` itself.  In
that coordinate, selected Yukawa points lie below the weak endpoint by P383's
monotonicity field, and coordinate monotonicity implies `g^2` monotonicity by
identity.

Therefore the current coordinate producer, coordinate step producer, and
coordinate nine-slot table add no producer-existence content over P383/P384.
They are useful normal forms, but not yet an independent physical RG-scale
certificate.  A future physically stronger theorem must add a real scale
semantics / independence condition to the coordinate field.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Abstract corridor to the canonical `g^2` coordinate -/

namespace SelectedYukawaRGMonotonicityCertificate

variable {Index A CKMCarrier : Type*} [AddCommGroup A]
variable {Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier}

/-- Canonical coordinate-normalization of a P383 corridor: use the squared
gauge coupling itself as the scalar coordinate.  This is mathematically exact
but intentionally exposes the semantic boundary: the current coordinate field
does not yet enforce an independent physical RG-scale coordinate. -/
def toGaugeCouplingSqCoordinateRGProducer
    (C : SelectedYukawaRGMonotonicityCertificate Z) :
    CoordinateRGMonotonicityProducer Z :=
  { rgCoordinate := fun a => (Z.running.gaugeCoupling a) ^ (2 : Nat)
    fourPi_pos := C.fourPi_pos
    selected_yukawa_coord_le_weak := by
      intro y
      exact C.gaugeCouplingSq_monotone (C.selected_yukawa_le_weak y)
    gaugeCouplingSq_monotone_on_coordinate := fun h => h }

end SelectedYukawaRGMonotonicityCertificate

/-- THEOREM 1: every P383 RG monotonicity corridor supplies a P385 coordinate
RG producer by choosing coordinate `g^2`. -/
theorem existsZeroFreeCoordinateRGProducer_of_rgMonotonicityCorridor
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeRGMonotonicityCorridor Index A CKMCarrier ->
      ExistsZeroFreeCoordinateRGProducer Index A CKMCarrier := by
  rintro ⟨Z, ⟨C⟩⟩
  exact ⟨Z, ⟨C.toGaugeCouplingSqCoordinateRGProducer⟩⟩

/-- THEOREM 2: P385's coordinate RG producer is existence-equivalent to P383's
RG monotonicity corridor. -/
theorem existsZeroFreeCoordinateRGProducer_iff_rgMonotonicityCorridor
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeCoordinateRGProducer Index A CKMCarrier ↔
      ExistsZeroFreeRGMonotonicityCorridor Index A CKMCarrier := by
  constructor
  · exact existsZeroFreeRGMonotonicityCorridor_of_coordinateRGProducer
  · exact existsZeroFreeCoordinateRGProducer_of_rgMonotonicityCorridor

/-! ## Coordinate producer and coordinate step producer are equivalent -/

namespace CoordinateRGMonotonicityProducer

variable {Index A CKMCarrier : Type*} [AddCommGroup A]
variable {Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier}

/-- Convert a coordinate RG producer to a coordinate-certified finite step
producer by taking the local step relation to be coordinate order itself. -/
def toCoordinateRGStepPathProducer
    (C : CoordinateRGMonotonicityProducer Z) :
    CoordinateRGStepPathProducer Z :=
  { rgCoordinate := C.rgCoordinate
    step := fun a b => C.rgCoordinate a ≤ C.rgCoordinate b
    fourPi_pos := C.fourPi_pos
    selected_yukawa_reaches_weak := by
      intro y
      exact
        RGStepReach.tail
          (RGStepReach.refl (StandardModelScaleCode.yukawa y))
          (C.selected_yukawa_coord_le_weak y)
    step_coord_monotone := fun h => h
    gaugeCouplingSq_monotone_on_coordinate :=
      C.gaugeCouplingSq_monotone_on_coordinate }

end CoordinateRGMonotonicityProducer

namespace RGStepReach

variable {step : StandardModelScaleCode -> StandardModelScaleCode -> Prop}

/-- Local coordinate monotonicity extends over finite RG-step reachability. -/
theorem coordinate_monotone
    (coord : StandardModelScaleCode -> ℝ)
    (hstep :
      ∀ {a b : StandardModelScaleCode}, step a b -> coord a ≤ coord b)
    {a b : StandardModelScaleCode} :
    RGStepReach step a b -> coord a ≤ coord b := by
  intro h
  induction h with
  | refl =>
      exact le_rfl
  | tail hreach hbc ih =>
      exact le_trans ih (hstep hbc)

end RGStepReach

namespace CoordinateRGStepPathProducer

variable {Index A CKMCarrier : Type*} [AddCommGroup A]
variable {Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier}

/-- Convert a coordinate-certified finite step producer back to the global
coordinate RG producer by extending local coordinate monotonicity along the
selected finite paths. -/
def toCoordinateRGMonotonicityProducer
    (C : CoordinateRGStepPathProducer Z) :
    CoordinateRGMonotonicityProducer Z :=
  { rgCoordinate := C.rgCoordinate
    fourPi_pos := C.fourPi_pos
    selected_yukawa_coord_le_weak := by
      intro y
      exact
        RGStepReach.coordinate_monotone C.rgCoordinate
          C.step_coord_monotone (C.selected_yukawa_reaches_weak y)
    gaugeCouplingSq_monotone_on_coordinate :=
      C.gaugeCouplingSq_monotone_on_coordinate }

end CoordinateRGStepPathProducer

/-- THEOREM 3: P385's coordinate RG producer supplies P388's coordinate step
producer. -/
theorem existsZeroFreeCoordinateRGStepPathProducer_of_coordinateRGProducer
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeCoordinateRGProducer Index A CKMCarrier ->
      ExistsZeroFreeCoordinateRGStepPathProducer Index A CKMCarrier := by
  rintro ⟨Z, ⟨C⟩⟩
  exact ⟨Z, ⟨C.toCoordinateRGStepPathProducer⟩⟩

/-- THEOREM 4: P388's coordinate step producer supplies P385's global
coordinate RG producer. -/
theorem existsZeroFreeCoordinateRGProducer_of_coordinateStepPath
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeCoordinateRGStepPathProducer Index A CKMCarrier ->
      ExistsZeroFreeCoordinateRGProducer Index A CKMCarrier := by
  rintro ⟨Z, ⟨C⟩⟩
  exact ⟨Z, ⟨C.toCoordinateRGMonotonicityProducer⟩⟩

/-- THEOREM 5: P385's coordinate RG producer and P388's coordinate finite-step
producer are exact normal forms of each other at producer-existence level. -/
theorem existsZeroFreeCoordinateRGStepPathProducer_iff_coordinateRGProducer
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeCoordinateRGStepPathProducer Index A CKMCarrier ↔
      ExistsZeroFreeCoordinateRGProducer Index A CKMCarrier := by
  constructor
  · exact existsZeroFreeCoordinateRGProducer_of_coordinateStepPath
  · exact existsZeroFreeCoordinateRGStepPathProducer_of_coordinateRGProducer

/-! ## Coordinate nine-slot table exact normal forms -/

/-- THEOREM 6: the coordinate-certified nine-slot table is equivalent to the
global coordinate RG producer. -/
theorem existsZeroFreeCoordinateYukawaRGPathTableProducer_iff_coordinateRGProducer
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeCoordinateYukawaRGPathTableProducer Index A CKMCarrier ↔
      ExistsZeroFreeCoordinateRGProducer Index A CKMCarrier := by
  constructor
  · intro h
    exact
      existsZeroFreeCoordinateRGProducer_of_coordinateStepPath
        ((existsZeroFreeCoordinateYukawaRGPathTableProducer_iff_coordinateStepPath).1 h)
  · intro h
    exact
      (existsZeroFreeCoordinateYukawaRGPathTableProducer_iff_coordinateStepPath).2
        (existsZeroFreeCoordinateRGStepPathProducer_of_coordinateRGProducer h)

/-- THEOREM 7: the coordinate-certified nine-slot table has exactly the same
existence content as P383's RG monotonicity corridor. -/
theorem existsZeroFreeCoordinateYukawaRGPathTableProducer_iff_rgMonotonicityCorridor
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeCoordinateYukawaRGPathTableProducer Index A CKMCarrier ↔
      ExistsZeroFreeRGMonotonicityCorridor Index A CKMCarrier := by
  constructor
  · intro h
    exact
      (existsZeroFreeCoordinateRGProducer_iff_rgMonotonicityCorridor).1
        ((existsZeroFreeCoordinateYukawaRGPathTableProducer_iff_coordinateRGProducer).1 h)
  · intro h
    exact
      (existsZeroFreeCoordinateYukawaRGPathTableProducer_iff_coordinateRGProducer).2
        ((existsZeroFreeCoordinateRGProducer_iff_rgMonotonicityCorridor).2 h)

/-- THEOREM 8: P384's current grand-unification receipt exists exactly when
the coordinate-certified nine-slot table exists. -/
theorem rgMonotonicityGrandUnificationReceipt_nonempty_iff_coordinateYukawaRGPathTable
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    Nonempty (RGMonotonicityGrandUnificationReceipt Index A CKMCarrier) ↔
      ExistsZeroFreeCoordinateYukawaRGPathTableProducer Index A CKMCarrier := by
  constructor
  · intro h
    exact
      (existsZeroFreeCoordinateYukawaRGPathTableProducer_iff_rgMonotonicityCorridor).2
        ((rgMonotonicityGrandUnificationReceipt_nonempty_iff_exists).1 h)
  · intro h
    exact
      (rgMonotonicityGrandUnificationReceipt_nonempty_iff_exists).2
        ((existsZeroFreeCoordinateYukawaRGPathTableProducer_iff_rgMonotonicityCorridor).1 h)

end StandardModelConstraint
end SaturationMonoid
