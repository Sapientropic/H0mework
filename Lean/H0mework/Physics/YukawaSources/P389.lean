import H0mework.Physics.RunningSources.P388

/-!
# Proposition 389: coordinate-certified nine-slot Yukawa RG path table

P387 names the finite nine-slot Yukawa path table.  P388 names the local
coordinate-certified RG-step producer.  This file fuses those two producer
shapes.

A physics-side producer now has a concrete acceptance surface:

* one finite RG step relation;
* one scalar RG coordinate;
* nine named path witnesses from the selected Yukawa slots to the weak endpoint;
* local coordinate monotonicity on every step;
* one theorem that coordinate monotonicity implies `g^2` monotonicity.

Lean then derives both existing producer shapes (P387 and P388), hence the P384
grand-unification receipt, unified-formula spine, and primitive producer atoms.

Boundary: the RG graph, coordinate, and physics proof of the coordinate order
are still producer data.  This file proves that this is now the precise finite
table a concrete RG/threshold calculation must fill.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Coordinate-certified nine-slot table -/

/-- Explicit nine-slot RG path table whose local edges are certified through a
scalar RG coordinate. -/
structure CoordinateYukawaRGPathTableProducer
    {Index A CKMCarrier : Type*} [AddCommGroup A]
    (Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier) where
  rgCoordinate : StandardModelScaleCode -> ℝ
  step : StandardModelScaleCode -> StandardModelScaleCode -> Prop
  fourPi_pos : 0 < Z.running.fourPi
  up_reaches_weak :
    RGStepReach step (StandardModelScaleCode.yukawa YukawaParameter.up)
      StandardModelScaleCode.weak
  charm_reaches_weak :
    RGStepReach step (StandardModelScaleCode.yukawa YukawaParameter.charm)
      StandardModelScaleCode.weak
  top_reaches_weak :
    RGStepReach step (StandardModelScaleCode.yukawa YukawaParameter.top)
      StandardModelScaleCode.weak
  down_reaches_weak :
    RGStepReach step (StandardModelScaleCode.yukawa YukawaParameter.down)
      StandardModelScaleCode.weak
  strange_reaches_weak :
    RGStepReach step (StandardModelScaleCode.yukawa YukawaParameter.strange)
      StandardModelScaleCode.weak
  bottom_reaches_weak :
    RGStepReach step (StandardModelScaleCode.yukawa YukawaParameter.bottom)
      StandardModelScaleCode.weak
  electron_reaches_weak :
    RGStepReach step (StandardModelScaleCode.yukawa YukawaParameter.electron)
      StandardModelScaleCode.weak
  muon_reaches_weak :
    RGStepReach step (StandardModelScaleCode.yukawa YukawaParameter.muon)
      StandardModelScaleCode.weak
  tau_reaches_weak :
    RGStepReach step (StandardModelScaleCode.yukawa YukawaParameter.tau)
      StandardModelScaleCode.weak
  step_coord_monotone :
    ∀ {a b : StandardModelScaleCode}, step a b ->
      rgCoordinate a ≤ rgCoordinate b
  gaugeCouplingSq_monotone_on_coordinate :
    ∀ {a b : StandardModelScaleCode}, rgCoordinate a ≤ rgCoordinate b ->
      (Z.running.gaugeCoupling a) ^ (2 : Nat) ≤
        (Z.running.gaugeCoupling b) ^ (2 : Nat)

namespace CoordinateYukawaRGPathTableProducer

variable {Index A CKMCarrier : Type*} [AddCommGroup A]
variable {Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier}

/-- THEOREM 1: the explicit nine-row table fills the all-Yukawa path field. -/
theorem selected_yukawa_reaches_weak
    (C : CoordinateYukawaRGPathTableProducer Z) :
    ∀ y : YukawaParameter,
      RGStepReach C.step (StandardModelScaleCode.yukawa y)
        StandardModelScaleCode.weak := by
  intro y
  cases y with
  | up => exact C.up_reaches_weak
  | charm => exact C.charm_reaches_weak
  | top => exact C.top_reaches_weak
  | down => exact C.down_reaches_weak
  | strange => exact C.strange_reaches_weak
  | bottom => exact C.bottom_reaches_weak
  | electron => exact C.electron_reaches_weak
  | muon => exact C.muon_reaches_weak
  | tau => exact C.tau_reaches_weak

/-- THEOREM 2: coordinate monotonicity on each local edge gives adjacent `g^2`
monotonicity on that edge. -/
theorem gaugeCouplingSq_step_monotone
    (C : CoordinateYukawaRGPathTableProducer Z)
    {a b : StandardModelScaleCode}
    (h : C.step a b) :
    (Z.running.gaugeCoupling a) ^ (2 : Nat) ≤
      (Z.running.gaugeCoupling b) ^ (2 : Nat) :=
  C.gaugeCouplingSq_monotone_on_coordinate (C.step_coord_monotone h)

/-- Convert the coordinate-certified nine-slot table to P388's coordinate
step-path producer. -/
def toCoordinateRGStepPathProducer
    (C : CoordinateYukawaRGPathTableProducer Z) :
    CoordinateRGStepPathProducer Z :=
  { rgCoordinate := C.rgCoordinate
    step := C.step
    fourPi_pos := C.fourPi_pos
    selected_yukawa_reaches_weak := C.selected_yukawa_reaches_weak
    step_coord_monotone := C.step_coord_monotone
    gaugeCouplingSq_monotone_on_coordinate :=
      C.gaugeCouplingSq_monotone_on_coordinate }

/-- Convert the same table to P387's nine-slot path producer. -/
def toYukawaRGPathTableProducer
    (C : CoordinateYukawaRGPathTableProducer Z) :
    YukawaRGPathTableProducer Z :=
  { step := C.step
    fourPi_pos := C.fourPi_pos
    up_reaches_weak := C.up_reaches_weak
    charm_reaches_weak := C.charm_reaches_weak
    top_reaches_weak := C.top_reaches_weak
    down_reaches_weak := C.down_reaches_weak
    strange_reaches_weak := C.strange_reaches_weak
    bottom_reaches_weak := C.bottom_reaches_weak
    electron_reaches_weak := C.electron_reaches_weak
    muon_reaches_weak := C.muon_reaches_weak
    tau_reaches_weak := C.tau_reaches_weak
    gaugeCouplingSq_step_monotone := C.gaugeCouplingSq_step_monotone }

/-- THEOREM 5: hence the coordinate-certified nine-slot table gives P382's
gauge weak corridor. -/
theorem toSelectedYukawaGaugeCouplingsBoundedByWeak
    (C : CoordinateYukawaRGPathTableProducer Z) :
    SelectedYukawaGaugeCouplingsBoundedByWeak Z :=
  C.toCoordinateRGStepPathProducer.toSelectedYukawaGaugeCouplingsBoundedByWeak

end CoordinateYukawaRGPathTableProducer

namespace CoordinateRGStepPathProducer

variable {Index A CKMCarrier : Type*} [AddCommGroup A]
variable {Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier}

/-- Convert P388's all-Yukawa coordinate step-path producer back into the
explicit nine-slot table.  This is the exact reverse of the "open the finite
surface" move: each named row is just the `∀ y` field projected at one
constructor of `YukawaParameter`. -/
def toCoordinateYukawaRGPathTableProducer
    (C : CoordinateRGStepPathProducer Z) :
    CoordinateYukawaRGPathTableProducer Z :=
  { rgCoordinate := C.rgCoordinate
    step := C.step
    fourPi_pos := C.fourPi_pos
    up_reaches_weak := C.selected_yukawa_reaches_weak YukawaParameter.up
    charm_reaches_weak := C.selected_yukawa_reaches_weak YukawaParameter.charm
    top_reaches_weak := C.selected_yukawa_reaches_weak YukawaParameter.top
    down_reaches_weak := C.selected_yukawa_reaches_weak YukawaParameter.down
    strange_reaches_weak := C.selected_yukawa_reaches_weak YukawaParameter.strange
    bottom_reaches_weak := C.selected_yukawa_reaches_weak YukawaParameter.bottom
    electron_reaches_weak :=
      C.selected_yukawa_reaches_weak YukawaParameter.electron
    muon_reaches_weak := C.selected_yukawa_reaches_weak YukawaParameter.muon
    tau_reaches_weak := C.selected_yukawa_reaches_weak YukawaParameter.tau
    step_coord_monotone := C.step_coord_monotone
    gaugeCouplingSq_monotone_on_coordinate :=
      C.gaugeCouplingSq_monotone_on_coordinate }

end CoordinateRGStepPathProducer

/-- A zero-free certificate equipped with a coordinate-certified explicit
nine-slot RG path table. -/
def ExistsZeroFreeCoordinateYukawaRGPathTableProducer
    (Index A CKMCarrier : Type*) [AddCommGroup A] : Prop :=
  ∃ Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier,
    Nonempty (CoordinateYukawaRGPathTableProducer Z)

/-- THEOREM 6: the coordinate-certified nine-slot table supplies P388's
coordinate step-path producer. -/
theorem existsZeroFreeCoordinateRGStepPathProducer_of_coordinateYukawaRGPathTable
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeCoordinateYukawaRGPathTableProducer Index A CKMCarrier ->
      ExistsZeroFreeCoordinateRGStepPathProducer Index A CKMCarrier := by
  rintro ⟨Z, ⟨C⟩⟩
  exact ⟨Z, ⟨C.toCoordinateRGStepPathProducer⟩⟩

/-- THEOREM 7: the same table also supplies P387's nine-slot path producer. -/
theorem existsZeroFreeYukawaRGPathTableProducer_of_coordinateYukawaRGPathTable
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeCoordinateYukawaRGPathTableProducer Index A CKMCarrier ->
      ExistsZeroFreeYukawaRGPathTableProducer Index A CKMCarrier := by
  rintro ⟨Z, ⟨C⟩⟩
  exact ⟨Z, ⟨C.toYukawaRGPathTableProducer⟩⟩

/-- THEOREM 8: P388's coordinate step-path producer supplies the explicit
nine-slot table by projecting the all-Yukawa path field. -/
theorem existsZeroFreeCoordinateYukawaRGPathTableProducer_of_coordinateStepPath
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeCoordinateRGStepPathProducer Index A CKMCarrier ->
      ExistsZeroFreeCoordinateYukawaRGPathTableProducer Index A CKMCarrier := by
  rintro ⟨Z, ⟨C⟩⟩
  exact ⟨Z, ⟨C.toCoordinateYukawaRGPathTableProducer⟩⟩

/-- THEOREM 9: the coordinate-certified nine-slot table is exactly equivalent
to P388's coordinate step-path producer at the producer-existence level. -/
theorem existsZeroFreeCoordinateYukawaRGPathTableProducer_iff_coordinateStepPath
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeCoordinateYukawaRGPathTableProducer Index A CKMCarrier ↔
      ExistsZeroFreeCoordinateRGStepPathProducer Index A CKMCarrier := by
  constructor
  · exact existsZeroFreeCoordinateRGStepPathProducer_of_coordinateYukawaRGPathTable
  · exact existsZeroFreeCoordinateYukawaRGPathTableProducer_of_coordinateStepPath

/-- THEOREM 10: the coordinate-certified nine-slot table constructs the P384
grand-unification receipt. -/
theorem rgMonotonicityGrandUnificationReceipt_nonempty_of_coordinateYukawaRGPathTable
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeCoordinateYukawaRGPathTableProducer Index A CKMCarrier ->
      Nonempty (RGMonotonicityGrandUnificationReceipt Index A CKMCarrier) := by
  intro h
  exact
    rgMonotonicityGrandUnificationReceipt_nonempty_of_coordinateStepPath
      (existsZeroFreeCoordinateRGStepPathProducer_of_coordinateYukawaRGPathTable h)

/-- THEOREM 11: the coordinate-certified nine-slot table therefore provides the
P374 unified-formula spine. -/
theorem unifiedFormulaSpine_nonempty_of_coordinateYukawaRGPathTable
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeCoordinateYukawaRGPathTableProducer Index A CKMCarrier ->
      Nonempty (StandardModelUnifiedFormulaSpineCertificate Index A CKMCarrier) := by
  intro h
  exact
    unifiedFormulaSpine_nonempty_iff_rgMonotonicityReceipt_nonempty
      (rgMonotonicityGrandUnificationReceipt_nonempty_of_coordinateYukawaRGPathTable h)

/-- THEOREM 12: the coordinate-certified nine-slot table also provides the
primitive producer atoms. -/
theorem primitiveProducerAtoms_nonempty_of_coordinateYukawaRGPathTable
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeCoordinateYukawaRGPathTableProducer Index A CKMCarrier ->
      Nonempty (GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier) := by
  intro h
  exact
    primitiveProducerAtoms_nonempty_iff_rgMonotonicityReceipt_nonempty
      (rgMonotonicityGrandUnificationReceipt_nonempty_of_coordinateYukawaRGPathTable h)

end StandardModelConstraint
end SaturationMonoid
