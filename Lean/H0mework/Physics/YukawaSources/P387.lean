import H0mework.Physics.RunningSources.P386

/-!
# Proposition 387: nine-slot Yukawa RG path table

P386 makes the remaining RG/threshold producer a finite path problem:
selected Yukawa scales must reach the weak endpoint through certified local
steps, with adjacent `g^2` monotonicity.

This file removes one more hiding place.  The nine Yukawa slots are a concrete
finite surface (`u,c,t,d,s,b,e,mu,tau`), so a runtime / physics producer can be
asked for a named path witness for each slot rather than an opaque function
`∀ y`.  The table is then folded back into the P386 step-path producer, hence
into the P384 grand-unification receipt.

Boundary: the table entries are still producer data.  This file proves only
that those nine named entries are exactly enough to fill the all-Yukawa path
field used by P386.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-- Explicit nine-slot RG path table for the selected Yukawa scales. -/
structure YukawaRGPathTableProducer
    {Index A CKMCarrier : Type*} [AddCommGroup A]
    (Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier) where
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
  gaugeCouplingSq_step_monotone :
    ∀ {a b : StandardModelScaleCode}, step a b ->
      (Z.running.gaugeCoupling a) ^ (2 : Nat) ≤
        (Z.running.gaugeCoupling b) ^ (2 : Nat)

namespace YukawaRGPathTableProducer

variable {Index A CKMCarrier : Type*} [AddCommGroup A]
variable {Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier}

/-- THEOREM 1: the explicit nine-row table is equivalent to the all-Yukawa path
field needed by P386. -/
theorem selected_yukawa_reaches_weak
    (C : YukawaRGPathTableProducer Z) :
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

/-- Convert the nine-slot table to P386's step-path producer. -/
def toRGStepPathProducer
    (C : YukawaRGPathTableProducer Z) :
    RGStepPathProducer Z :=
  { step := C.step
    fourPi_pos := C.fourPi_pos
    selected_yukawa_reaches_weak := C.selected_yukawa_reaches_weak
    gaugeCouplingSq_step_monotone := C.gaugeCouplingSq_step_monotone }

/-- THEOREM 3: a nine-slot table gives P382's gauge weak corridor. -/
theorem toSelectedYukawaGaugeCouplingsBoundedByWeak
    (C : YukawaRGPathTableProducer Z) :
    SelectedYukawaGaugeCouplingsBoundedByWeak Z :=
  C.toRGStepPathProducer.toSelectedYukawaGaugeCouplingsBoundedByWeak

end YukawaRGPathTableProducer

/-- A zero-free certificate equipped with the explicit nine-slot RG path table. -/
def ExistsZeroFreeYukawaRGPathTableProducer
    (Index A CKMCarrier : Type*) [AddCommGroup A] : Prop :=
  ∃ Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier,
    Nonempty (YukawaRGPathTableProducer Z)

/-- THEOREM 4: the explicit nine-slot table supplies P386's finite RG-step
producer. -/
theorem existsZeroFreeRGStepPathProducer_of_yukawaRGPathTable
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeYukawaRGPathTableProducer Index A CKMCarrier ->
      ExistsZeroFreeRGStepPathProducer Index A CKMCarrier := by
  rintro ⟨Z, ⟨C⟩⟩
  exact ⟨Z, ⟨C.toRGStepPathProducer⟩⟩

/-- THEOREM 5: the explicit nine-slot table constructs the P384
grand-unification receipt. -/
theorem rgMonotonicityGrandUnificationReceipt_nonempty_of_yukawaRGPathTable
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeYukawaRGPathTableProducer Index A CKMCarrier ->
      Nonempty (RGMonotonicityGrandUnificationReceipt Index A CKMCarrier) := by
  intro h
  exact
    rgMonotonicityGrandUnificationReceipt_nonempty_of_stepPathProducer
      (existsZeroFreeRGStepPathProducer_of_yukawaRGPathTable h)

/-- THEOREM 6: the explicit nine-slot table therefore provides the P374
unified-formula spine. -/
theorem unifiedFormulaSpine_nonempty_of_yukawaRGPathTable
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeYukawaRGPathTableProducer Index A CKMCarrier ->
      Nonempty (StandardModelUnifiedFormulaSpineCertificate Index A CKMCarrier) := by
  intro h
  exact
    unifiedFormulaSpine_nonempty_iff_rgMonotonicityReceipt_nonempty
      (rgMonotonicityGrandUnificationReceipt_nonempty_of_yukawaRGPathTable h)

/-- THEOREM 7: the explicit nine-slot table also provides the primitive
producer atoms. -/
theorem primitiveProducerAtoms_nonempty_of_yukawaRGPathTable
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeYukawaRGPathTableProducer Index A CKMCarrier ->
      Nonempty (GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier) := by
  intro h
  exact
    primitiveProducerAtoms_nonempty_iff_rgMonotonicityReceipt_nonempty
      (rgMonotonicityGrandUnificationReceipt_nonempty_of_yukawaRGPathTable h)

end StandardModelConstraint
end SaturationMonoid
