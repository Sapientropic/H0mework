import H0mework.Physics.RunningSources.P393

/-!
# Proposition 394: finite running-sigma RG path table

P393 makes running sigma itself the non-tautological RG coordinate.  This file
lowers that producer to the shape a concrete RG / threshold calculation should
output:

* one finite RG step relation;
* nine named path witnesses from selected Yukawa scales to the weak endpoint;
* local monotonicity of running sigma along every step;
* the elementary nondegeneracy data that makes sigma independent of `g^2`.

Lean then derives the selected-Yukawa sigma corridor, the P393 running-sigma
independent coordinate witness, the P392 independent coordinate producer, the
P389 coordinate-certified nine-slot table, and therefore the P384
grand-unification receipt.

Boundary: this is still not a beta-function or threshold calculation.  It is
the finite certificate surface that such a calculation must fill.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Running-sigma finite path table -/

/-- A concrete nine-slot RG path table whose local edges are certified directly
by monotonicity of P274 running sigma. -/
structure RunningSigmaYukawaRGPathTableProducer
    {Index A CKMCarrier : Type*} [AddCommGroup A]
    (Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier) where
  step : StandardModelScaleCode -> StandardModelScaleCode -> Prop
  fourPi_pos : 0 < Z.running.fourPi
  fourPi_ne_one : Z.running.fourPi ≠ 1
  nonzeroScale : StandardModelScaleCode
  gaugeCouplingSq_ne_zero :
    (Z.running.gaugeCoupling nonzeroScale) ^ (2 : Nat) ≠ 0
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
  step_sigma_monotone :
    ∀ {a b : StandardModelScaleCode}, step a b ->
      Z.running.sigma a ≤ Z.running.sigma b

namespace RunningSigmaYukawaRGPathTableProducer

variable {Index A CKMCarrier : Type*} [AddCommGroup A]
variable {Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier}

/-- THEOREM 1: the explicit nine rows fill the all-Yukawa path field. -/
theorem selected_yukawa_reaches_weak
    (C : RunningSigmaYukawaRGPathTableProducer Z) :
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

/-- THEOREM 2: local sigma monotonicity extends along finite RG reachability. -/
theorem sigma_monotone_of_reach
    (C : RunningSigmaYukawaRGPathTableProducer Z)
    {a b : StandardModelScaleCode} :
    RGStepReach C.step a b ->
      Z.running.sigma a ≤ Z.running.sigma b := by
  intro h
  induction h with
  | refl =>
      exact le_rfl
  | tail hreach hbc ih =>
      exact le_trans ih (C.step_sigma_monotone hbc)

/-- THEOREM 3: the finite sigma path table supplies the P381 selected-Yukawa
running-sigma corridor. -/
theorem selected_yukawa_sigma_le_weak
    (C : RunningSigmaYukawaRGPathTableProducer Z) :
    SelectedYukawaSigmaBoundedByWeak Z := by
  intro y
  exact C.sigma_monotone_of_reach (C.selected_yukawa_reaches_weak y)

/-- Convert the finite sigma path table to P393's running-sigma independent
coordinate witness. -/
def toRunningSigmaIndependentCoordinateWitness
    (C : RunningSigmaYukawaRGPathTableProducer Z) :
    RunningSigmaIndependentCoordinateWitness Z :=
  { fourPi_pos := C.fourPi_pos
    fourPi_ne_one := C.fourPi_ne_one
    selected_yukawa_sigma_le_weak := C.selected_yukawa_sigma_le_weak
    nonzeroScale := C.nonzeroScale
    gaugeCouplingSq_ne_zero := C.gaugeCouplingSq_ne_zero }

/-- Convert the same table to P392's independent coordinate producer. -/
def toIndependentRGCoordinateProducer
    (C : RunningSigmaYukawaRGPathTableProducer Z) :
    IndependentRGCoordinateProducer Z :=
  C.toRunningSigmaIndependentCoordinateWitness.toIndependentRGCoordinateProducer

/-- Convert the same table to P389's coordinate-certified nine-slot surface,
with `rgCoordinate = running sigma`. -/
def toCoordinateYukawaRGPathTableProducer
    (C : RunningSigmaYukawaRGPathTableProducer Z) :
    CoordinateYukawaRGPathTableProducer Z :=
  { rgCoordinate := Z.running.sigma
    step := C.step
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
    step_coord_monotone := C.step_sigma_monotone
    gaugeCouplingSq_monotone_on_coordinate :=
      C.toRunningSigmaIndependentCoordinateWitness.gaugeCouplingSq_monotone_on_sigma }

end RunningSigmaYukawaRGPathTableProducer

/-- A zero-free certificate equipped with the finite running-sigma nine-slot
path table. -/
def ExistsZeroFreeRunningSigmaYukawaRGPathTableProducer
    (Index A CKMCarrier : Type*) [AddCommGroup A] : Prop :=
  ∃ Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier,
    Nonempty (RunningSigmaYukawaRGPathTableProducer Z)

/-- THEOREM 7: a finite running-sigma table supplies the P393 coordinate
witness. -/
theorem existsZeroFreeRunningSigmaIndependentCoordinateWitness_of_runningSigmaYukawaRGPathTable
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeRunningSigmaYukawaRGPathTableProducer Index A CKMCarrier ->
      ExistsZeroFreeRunningSigmaIndependentCoordinateWitness Index A CKMCarrier := by
  rintro ⟨Z, ⟨C⟩⟩
  exact ⟨Z, ⟨C.toRunningSigmaIndependentCoordinateWitness⟩⟩

/-- THEOREM 8: a finite running-sigma table supplies P392's independent
coordinate producer. -/
theorem existsZeroFreeIndependentRGCoordinateProducer_of_runningSigmaYukawaRGPathTable
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeRunningSigmaYukawaRGPathTableProducer Index A CKMCarrier ->
      ExistsZeroFreeIndependentRGCoordinateProducer Index A CKMCarrier := by
  rintro ⟨Z, ⟨C⟩⟩
  exact ⟨Z, ⟨C.toIndependentRGCoordinateProducer⟩⟩

/-- THEOREM 9: the same table supplies P389's coordinate-certified nine-slot
normal form. -/
theorem existsZeroFreeCoordinateYukawaRGPathTableProducer_of_runningSigmaYukawaRGPathTable
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeRunningSigmaYukawaRGPathTableProducer Index A CKMCarrier ->
      ExistsZeroFreeCoordinateYukawaRGPathTableProducer Index A CKMCarrier := by
  rintro ⟨Z, ⟨C⟩⟩
  exact ⟨Z, ⟨C.toCoordinateYukawaRGPathTableProducer⟩⟩

/-- THEOREM 10: therefore a finite running-sigma table constructs the P384
grand-unification receipt. -/
theorem rgMonotonicityGrandUnificationReceipt_nonempty_of_runningSigmaYukawaRGPathTable
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeRunningSigmaYukawaRGPathTableProducer Index A CKMCarrier ->
      Nonempty (RGMonotonicityGrandUnificationReceipt Index A CKMCarrier) :=
  rgMonotonicityGrandUnificationReceipt_nonempty_of_runningSigmaCoordinateWitness ∘
    existsZeroFreeRunningSigmaIndependentCoordinateWitness_of_runningSigmaYukawaRGPathTable

end StandardModelConstraint
end SaturationMonoid
