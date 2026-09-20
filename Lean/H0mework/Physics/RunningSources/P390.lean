import H0mework.Physics.YukawaSources.P389

/-!
# Proposition 390: exact RG-path normal forms

P386 and P387 introduced finite RG-step paths and an explicit nine-slot Yukawa
path table as concrete producer surfaces for the P383 RG monotonicity corridor.
Earlier files used them in the forward direction: table -> finite paths ->
RG corridor -> P384 receipt.

This file proves the reverse direction for the non-coordinate surfaces.  Any
P383 RG monotonicity corridor itself can be used as the local step relation;
then each selected Yukawa slot reaches the weak endpoint in one step and the
local step monotonicity is exactly P383's monotonicity field.  Since
`YukawaParameter` is finite, the all-Yukawa field and the nine named rows are
existence-equivalent.

Boundary: this is an exact Lean normal-form theorem, not a physics instance.
The physical producer still has to construct the zero-free certificate and a
real RG/threshold relation satisfying the corridor.  P388/P389's coordinate
surfaces remain stronger, coordinate-certified acceptance surfaces.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## From the abstract RG corridor back to finite local steps -/

namespace SelectedYukawaRGMonotonicityCertificate

variable {Index A CKMCarrier : Type*} [AddCommGroup A]
variable {Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier}

/-- Convert P383's relation-shaped RG corridor to P386's finite step-path
producer by taking the local step relation to be the corridor relation itself.
Each selected Yukawa endpoint then reaches `weak` in one certified step. -/
def toRGStepPathProducer
    (C : SelectedYukawaRGMonotonicityCertificate Z) :
    RGStepPathProducer Z :=
  { step := C.scaleLe
    fourPi_pos := C.fourPi_pos
    selected_yukawa_reaches_weak := by
      intro y
      exact
        RGStepReach.tail
          (RGStepReach.refl (StandardModelScaleCode.yukawa y))
          (C.selected_yukawa_le_weak y)
    gaugeCouplingSq_step_monotone := fun h => C.gaugeCouplingSq_monotone h }

end SelectedYukawaRGMonotonicityCertificate

/-- THEOREM 1: the P383 RG monotonicity corridor supplies P386's finite
step-path producer. -/
theorem existsZeroFreeRGStepPathProducer_of_rgMonotonicityCorridor
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeRGMonotonicityCorridor Index A CKMCarrier ->
      ExistsZeroFreeRGStepPathProducer Index A CKMCarrier := by
  rintro ⟨Z, ⟨C⟩⟩
  exact ⟨Z, ⟨C.toRGStepPathProducer⟩⟩

/-- THEOREM 2: P386's finite step-path producer is an exact normal form for
P383's RG monotonicity corridor at producer-existence level. -/
theorem existsZeroFreeRGStepPathProducer_iff_rgMonotonicityCorridor
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeRGStepPathProducer Index A CKMCarrier ↔
      ExistsZeroFreeRGMonotonicityCorridor Index A CKMCarrier := by
  constructor
  · exact existsZeroFreeRGMonotonicityCorridor_of_stepPathProducer
  · exact existsZeroFreeRGStepPathProducer_of_rgMonotonicityCorridor

/-! ## From finite local steps back to the explicit nine-slot table -/

namespace RGStepPathProducer

variable {Index A CKMCarrier : Type*} [AddCommGroup A]
variable {Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier}

/-- Convert P386's all-Yukawa step-path producer to P387's explicit nine-row
table by projecting the `∀ y` field at each constructor. -/
def toYukawaRGPathTableProducer
    (C : RGStepPathProducer Z) :
    YukawaRGPathTableProducer Z :=
  { step := C.step
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
    gaugeCouplingSq_step_monotone := C.gaugeCouplingSq_step_monotone }

end RGStepPathProducer

/-- THEOREM 3: P386's finite step-path producer supplies P387's explicit
nine-slot table. -/
theorem existsZeroFreeYukawaRGPathTableProducer_of_stepPathProducer
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeRGStepPathProducer Index A CKMCarrier ->
      ExistsZeroFreeYukawaRGPathTableProducer Index A CKMCarrier := by
  rintro ⟨Z, ⟨C⟩⟩
  exact ⟨Z, ⟨C.toYukawaRGPathTableProducer⟩⟩

/-- THEOREM 4: P387's explicit nine-slot table is exactly equivalent to P386's
all-Yukawa finite step-path producer at producer-existence level. -/
theorem existsZeroFreeYukawaRGPathTableProducer_iff_stepPathProducer
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeYukawaRGPathTableProducer Index A CKMCarrier ↔
      ExistsZeroFreeRGStepPathProducer Index A CKMCarrier := by
  constructor
  · exact existsZeroFreeRGStepPathProducer_of_yukawaRGPathTable
  · exact existsZeroFreeYukawaRGPathTableProducer_of_stepPathProducer

/-- THEOREM 5: the explicit nine-slot Yukawa RG path table is an exact normal
form for P383's RG monotonicity corridor. -/
theorem existsZeroFreeYukawaRGPathTableProducer_iff_rgMonotonicityCorridor
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeYukawaRGPathTableProducer Index A CKMCarrier ↔
      ExistsZeroFreeRGMonotonicityCorridor Index A CKMCarrier := by
  constructor
  · intro h
    exact
      existsZeroFreeRGMonotonicityCorridor_of_stepPathProducer
        (existsZeroFreeRGStepPathProducer_of_yukawaRGPathTable h)
  · intro h
    exact
      existsZeroFreeYukawaRGPathTableProducer_of_stepPathProducer
        (existsZeroFreeRGStepPathProducer_of_rgMonotonicityCorridor h)

/-- THEOREM 6: P384's grand-unification receipt exists exactly when the
explicit nine-slot Yukawa RG path table exists. -/
theorem rgMonotonicityGrandUnificationReceipt_nonempty_iff_yukawaRGPathTable
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    Nonempty (RGMonotonicityGrandUnificationReceipt Index A CKMCarrier) ↔
      ExistsZeroFreeYukawaRGPathTableProducer Index A CKMCarrier := by
  constructor
  · intro h
    exact
      (existsZeroFreeYukawaRGPathTableProducer_iff_rgMonotonicityCorridor).2
        ((rgMonotonicityGrandUnificationReceipt_nonempty_iff_exists).1 h)
  · intro h
    exact
      (rgMonotonicityGrandUnificationReceipt_nonempty_iff_exists).2
        ((existsZeroFreeYukawaRGPathTableProducer_iff_rgMonotonicityCorridor).1 h)

/-- THEOREM 7: the explicit nine-slot Yukawa RG path table still supplies the
current P374 unified-formula spine.  This is intentionally a one-way theorem:
the P374 spine can be produced by weaker kernels than an RG table. -/
theorem unifiedFormulaSpine_nonempty_of_yukawaRGPathTable_normalForm
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeYukawaRGPathTableProducer Index A CKMCarrier ->
      Nonempty (StandardModelUnifiedFormulaSpineCertificate Index A CKMCarrier) := by
  intro h
  exact unifiedFormulaSpine_nonempty_of_yukawaRGPathTable h

/-- THEOREM 8: the explicit nine-slot Yukawa RG path table also supplies the
primitive producer atoms.  This is likewise one-way for the same reason as
THEOREM 7. -/
theorem primitiveProducerAtoms_nonempty_of_yukawaRGPathTable_normalForm
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeYukawaRGPathTableProducer Index A CKMCarrier ->
      Nonempty (GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier) := by
  intro h
  exact primitiveProducerAtoms_nonempty_of_yukawaRGPathTable h

end StandardModelConstraint
end SaturationMonoid
