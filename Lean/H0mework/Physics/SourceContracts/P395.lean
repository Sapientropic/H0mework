import H0mework.Physics.RunningSources.P394

/-!
# Proposition 395: weak-endpoint nondegeneracy for running sigma

P393/P394 still carried one elementary nondegeneracy field by hand: some
running gauge coupling squared must be nonzero, otherwise `sigma` could collapse
to the tautological zero coordinate.

For zero-free Standard-Model certificates this field is not external.  P274/P276
pin the weak endpoint to

`sigma(weak) = 81/500`

and P274 reads sigma as `g(scale)^2 / fourPi`.  If the weak-scale squared
coupling were zero, the weak sigma would be zero, contradicting the pinned
endpoint.  This file removes that producer burden and lowers P394 to the exact
finite running-sigma table plus the remaining `fourPi` nonidentity condition.

Boundary: `fourPi != 1` and the actual RG/threshold path table remain physical
producer obligations.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Weak endpoint forces nonzero squared coupling -/

/-- THEOREM 1: the pinned weak endpoint forces the weak-scale squared gauge
coupling to be nonzero. -/
theorem gaugeCouplingSq_weak_ne_zero_of_pinnedWeakSigma
    {Index A CKMCarrier : Type*} [AddCommGroup A]
    (Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier) :
    (Z.running.gaugeCoupling StandardModelScaleCode.weak) ^ (2 : Nat) ≠ 0 := by
  intro hzero
  have hsigma_zero :
      Z.running.sigma StandardModelScaleCode.weak = 0 := by
    rw [Z.running.sigma_eq_alpha StandardModelScaleCode.weak]
    simp [alphaFromGaugeCoupling, hzero]
  have hsigma_nominal :
      Z.running.sigma StandardModelScaleCode.weak = sigmaWeakNominal ℝ :=
    ZeroContinuousFreeStandardModelCertificate.sigma_weak_code_eq_nominal Z
  have hnominal_zero : sigmaWeakNominal ℝ = 0 := by
    rw [← hsigma_nominal]
    exact hsigma_zero
  norm_num [sigmaWeakNominal] at hnominal_zero

/-! ## Reduced running-sigma coordinate witness -/

/-- P393's running-sigma witness with the nonzero-coupling field discharged by
the pinned weak endpoint. -/
structure WeakEndpointRunningSigmaIndependentCoordinateWitness
    {Index A CKMCarrier : Type*} [AddCommGroup A]
    (Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier) where
  fourPi_pos : 0 < Z.running.fourPi
  fourPi_ne_one : Z.running.fourPi ≠ 1
  selected_yukawa_sigma_le_weak : SelectedYukawaSigmaBoundedByWeak Z

namespace WeakEndpointRunningSigmaIndependentCoordinateWitness

variable {Index A CKMCarrier : Type*} [AddCommGroup A]
variable {Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier}

/-- Convert the reduced weak-endpoint witness to P393's full witness, using
`weak` as the canonical nonzero scale. -/
def toRunningSigmaIndependentCoordinateWitness
    (W : WeakEndpointRunningSigmaIndependentCoordinateWitness Z) :
    RunningSigmaIndependentCoordinateWitness Z :=
  { fourPi_pos := W.fourPi_pos
    fourPi_ne_one := W.fourPi_ne_one
    selected_yukawa_sigma_le_weak := W.selected_yukawa_sigma_le_weak
    nonzeroScale := StandardModelScaleCode.weak
    gaugeCouplingSq_ne_zero :=
      gaugeCouplingSq_weak_ne_zero_of_pinnedWeakSigma Z }

/-- Convert the reduced weak-endpoint witness to P392's independent coordinate
producer. -/
def toIndependentRGCoordinateProducer
    (W : WeakEndpointRunningSigmaIndependentCoordinateWitness Z) :
    IndependentRGCoordinateProducer Z :=
  W.toRunningSigmaIndependentCoordinateWitness.toIndependentRGCoordinateProducer

end WeakEndpointRunningSigmaIndependentCoordinateWitness

/-- A zero-free certificate equipped with the reduced weak-endpoint running
sigma witness. -/
def ExistsZeroFreeWeakEndpointRunningSigmaIndependentCoordinateWitness
    (Index A CKMCarrier : Type*) [AddCommGroup A] : Prop :=
  ∃ Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier,
    Nonempty (WeakEndpointRunningSigmaIndependentCoordinateWitness Z)

/-- THEOREM 4: the reduced weak-endpoint witness supplies P393's full
running-sigma coordinate witness. -/
theorem existsZeroFreeRunningSigmaIndependentCoordinateWitness_of_weakEndpointWitness
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeWeakEndpointRunningSigmaIndependentCoordinateWitness
      Index A CKMCarrier ->
      ExistsZeroFreeRunningSigmaIndependentCoordinateWitness Index A CKMCarrier := by
  rintro ⟨Z, ⟨W⟩⟩
  exact ⟨Z, ⟨W.toRunningSigmaIndependentCoordinateWitness⟩⟩

/-- THEOREM 5: the reduced weak-endpoint witness supplies the P392 independent
coordinate producer. -/
theorem existsZeroFreeIndependentRGCoordinateProducer_of_weakEndpointWitness
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeWeakEndpointRunningSigmaIndependentCoordinateWitness
      Index A CKMCarrier ->
      ExistsZeroFreeIndependentRGCoordinateProducer Index A CKMCarrier :=
  existsZeroFreeIndependentRGCoordinateProducer_of_runningSigmaCoordinateWitness ∘
    existsZeroFreeRunningSigmaIndependentCoordinateWitness_of_weakEndpointWitness

/-- THEOREM 6: the reduced weak-endpoint witness constructs the P384
grand-unification receipt. -/
theorem rgMonotonicityGrandUnificationReceipt_nonempty_of_weakEndpointWitness
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeWeakEndpointRunningSigmaIndependentCoordinateWitness
      Index A CKMCarrier ->
      Nonempty (RGMonotonicityGrandUnificationReceipt Index A CKMCarrier) :=
  rgMonotonicityGrandUnificationReceipt_nonempty_of_runningSigmaCoordinateWitness ∘
    existsZeroFreeRunningSigmaIndependentCoordinateWitness_of_weakEndpointWitness

/-! ## Reduced finite running-sigma path table -/

/-- P394's finite running-sigma path table with weak-endpoint nonzero
coupling derived internally rather than carried as a producer field. -/
structure WeakEndpointRunningSigmaYukawaRGPathTableProducer
    {Index A CKMCarrier : Type*} [AddCommGroup A]
    (Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier) where
  step : StandardModelScaleCode -> StandardModelScaleCode -> Prop
  fourPi_pos : 0 < Z.running.fourPi
  fourPi_ne_one : Z.running.fourPi ≠ 1
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

namespace WeakEndpointRunningSigmaYukawaRGPathTableProducer

variable {Index A CKMCarrier : Type*} [AddCommGroup A]
variable {Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier}

/-- Convert the reduced path table to P394's full finite running-sigma table. -/
def toRunningSigmaYukawaRGPathTableProducer
    (C : WeakEndpointRunningSigmaYukawaRGPathTableProducer Z) :
    RunningSigmaYukawaRGPathTableProducer Z :=
  { step := C.step
    fourPi_pos := C.fourPi_pos
    fourPi_ne_one := C.fourPi_ne_one
    nonzeroScale := StandardModelScaleCode.weak
    gaugeCouplingSq_ne_zero :=
      gaugeCouplingSq_weak_ne_zero_of_pinnedWeakSigma Z
    up_reaches_weak := C.up_reaches_weak
    charm_reaches_weak := C.charm_reaches_weak
    top_reaches_weak := C.top_reaches_weak
    down_reaches_weak := C.down_reaches_weak
    strange_reaches_weak := C.strange_reaches_weak
    bottom_reaches_weak := C.bottom_reaches_weak
    electron_reaches_weak := C.electron_reaches_weak
    muon_reaches_weak := C.muon_reaches_weak
    tau_reaches_weak := C.tau_reaches_weak
    step_sigma_monotone := C.step_sigma_monotone }

/-- The reduced path table supplies the reduced weak-endpoint coordinate
witness. -/
theorem toWeakEndpointRunningSigmaIndependentCoordinateWitness
    (C : WeakEndpointRunningSigmaYukawaRGPathTableProducer Z) :
    WeakEndpointRunningSigmaIndependentCoordinateWitness Z := by
  exact
    { fourPi_pos := C.fourPi_pos
      fourPi_ne_one := C.fourPi_ne_one
      selected_yukawa_sigma_le_weak :=
        C.toRunningSigmaYukawaRGPathTableProducer.selected_yukawa_sigma_le_weak }

/-- Convert the reduced path table directly to P392's independent coordinate
producer. -/
def toIndependentRGCoordinateProducer
    (C : WeakEndpointRunningSigmaYukawaRGPathTableProducer Z) :
    IndependentRGCoordinateProducer Z :=
  C.toWeakEndpointRunningSigmaIndependentCoordinateWitness
    |>.toIndependentRGCoordinateProducer

end WeakEndpointRunningSigmaYukawaRGPathTableProducer

/-- A zero-free certificate equipped with the reduced weak-endpoint finite
running-sigma table. -/
def ExistsZeroFreeWeakEndpointRunningSigmaYukawaRGPathTableProducer
    (Index A CKMCarrier : Type*) [AddCommGroup A] : Prop :=
  ∃ Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier,
    Nonempty (WeakEndpointRunningSigmaYukawaRGPathTableProducer Z)

/-- THEOREM 10: the reduced path table supplies P394's full finite
running-sigma table. -/
theorem existsZeroFreeRunningSigmaYukawaRGPathTableProducer_of_weakEndpointPathTable
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeWeakEndpointRunningSigmaYukawaRGPathTableProducer
      Index A CKMCarrier ->
      ExistsZeroFreeRunningSigmaYukawaRGPathTableProducer Index A CKMCarrier := by
  rintro ⟨Z, ⟨C⟩⟩
  exact ⟨Z, ⟨C.toRunningSigmaYukawaRGPathTableProducer⟩⟩

/-- THEOREM 11: the reduced path table supplies the reduced weak-endpoint
coordinate witness. -/
theorem existsZeroFreeWeakEndpointRunningSigmaIndependentCoordinateWitness_of_pathTable
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeWeakEndpointRunningSigmaYukawaRGPathTableProducer
      Index A CKMCarrier ->
      ExistsZeroFreeWeakEndpointRunningSigmaIndependentCoordinateWitness
        Index A CKMCarrier := by
  rintro ⟨Z, ⟨C⟩⟩
  exact ⟨Z, ⟨C.toWeakEndpointRunningSigmaIndependentCoordinateWitness⟩⟩

/-- THEOREM 12: therefore the reduced path table constructs the P384
grand-unification receipt. -/
theorem rgMonotonicityGrandUnificationReceipt_nonempty_of_weakEndpointPathTable
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeWeakEndpointRunningSigmaYukawaRGPathTableProducer
      Index A CKMCarrier ->
      Nonempty (RGMonotonicityGrandUnificationReceipt Index A CKMCarrier) :=
  rgMonotonicityGrandUnificationReceipt_nonempty_of_runningSigmaYukawaRGPathTable ∘
    existsZeroFreeRunningSigmaYukawaRGPathTableProducer_of_weakEndpointPathTable

end StandardModelConstraint
end SaturationMonoid
