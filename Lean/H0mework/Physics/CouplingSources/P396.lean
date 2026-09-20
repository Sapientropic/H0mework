import H0mework.Physics.SourceContracts.P395

/-!
# Proposition 396: physical four-pi normalization

P395 removes the hand-supplied nonzero-coupling witness from the running-sigma
route.  The other elementary nondegeneracy field is `fourPi != 1`, used by P393
to ensure that `sigma = g^2 / fourPi` is not just the identity coordinate
`g^2`.

For a physically normalized certificate, this field should not be hand-entered
either: `fourPi` is the real normalizer `4 * Real.pi`.  Since `pi > 0` and
`4*pi > 1`, Lean derives both positivity and nonidentity.  Thus the live
running-sigma producer surface is reduced again: supply the zero-free
certificate, the physical four-pi normalization, and the finite sigma-monotone
RG/threshold table.

Boundary: this still does not solve the RG/threshold equations.  It only
removes the remaining elementary `fourPi` bookkeeping from that producer
surface.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Real four-pi facts -/

/-- The physically normalized real `4*pi` carrier. -/
noncomputable def realFourPi : ℝ :=
  4 * Real.pi

/-- THEOREM 1: real `4*pi` is positive. -/
theorem realFourPi_pos : 0 < realFourPi := by
  dsimp [realFourPi]
  positivity

/-- THEOREM 2: real `4*pi` is not `1`. -/
theorem realFourPi_ne_one : realFourPi ≠ 1 := by
  have hgt : 1 < realFourPi := by
    dsimp [realFourPi]
    nlinarith [Real.pi_gt_three]
  exact ne_of_gt hgt

/-! ## Physical four-pi normalized running-sigma witness -/

/-- P395's weak-endpoint running-sigma witness with `fourPi` physically
normalized to `4*pi`, so positivity and nonidentity are derived internally. -/
structure PhysicalFourPiRunningSigmaIndependentCoordinateWitness
    {Index A CKMCarrier : Type*} [AddCommGroup A]
    (Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier) where
  fourPi_eq_realFourPi : Z.running.fourPi = realFourPi
  selected_yukawa_sigma_le_weak : SelectedYukawaSigmaBoundedByWeak Z

namespace PhysicalFourPiRunningSigmaIndependentCoordinateWitness

variable {Index A CKMCarrier : Type*} [AddCommGroup A]
variable {Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier}

/-- Convert the physical-normalization witness to P395's reduced weak-endpoint
witness. -/
theorem toWeakEndpointRunningSigmaIndependentCoordinateWitness
    (W : PhysicalFourPiRunningSigmaIndependentCoordinateWitness Z) :
    WeakEndpointRunningSigmaIndependentCoordinateWitness Z := by
  exact
    { fourPi_pos := by
        rw [W.fourPi_eq_realFourPi]
        exact realFourPi_pos
      fourPi_ne_one := by
        rw [W.fourPi_eq_realFourPi]
        exact realFourPi_ne_one
      selected_yukawa_sigma_le_weak := W.selected_yukawa_sigma_le_weak }

/-- Convert the physical-normalization witness to P393's full running-sigma
coordinate witness. -/
def toRunningSigmaIndependentCoordinateWitness
    (W : PhysicalFourPiRunningSigmaIndependentCoordinateWitness Z) :
    RunningSigmaIndependentCoordinateWitness Z :=
  W.toWeakEndpointRunningSigmaIndependentCoordinateWitness
    |>.toRunningSigmaIndependentCoordinateWitness

/-- Convert the physical-normalization witness to P392's independent
coordinate producer. -/
def toIndependentRGCoordinateProducer
    (W : PhysicalFourPiRunningSigmaIndependentCoordinateWitness Z) :
    IndependentRGCoordinateProducer Z :=
  W.toWeakEndpointRunningSigmaIndependentCoordinateWitness
    |>.toIndependentRGCoordinateProducer

end PhysicalFourPiRunningSigmaIndependentCoordinateWitness

/-- A zero-free certificate equipped with the physical four-pi normalized
running-sigma witness. -/
def ExistsZeroFreePhysicalFourPiRunningSigmaIndependentCoordinateWitness
    (Index A CKMCarrier : Type*) [AddCommGroup A] : Prop :=
  ∃ Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier,
    Nonempty (PhysicalFourPiRunningSigmaIndependentCoordinateWitness Z)

/-- THEOREM 6: the physical four-pi witness supplies P395's weak-endpoint
witness. -/
theorem existsZeroFreeWeakEndpointRunningSigmaIndependentCoordinateWitness_of_physicalFourPiWitness
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePhysicalFourPiRunningSigmaIndependentCoordinateWitness
      Index A CKMCarrier ->
      ExistsZeroFreeWeakEndpointRunningSigmaIndependentCoordinateWitness
        Index A CKMCarrier := by
  rintro ⟨Z, ⟨W⟩⟩
  exact ⟨Z, ⟨W.toWeakEndpointRunningSigmaIndependentCoordinateWitness⟩⟩

/-- THEOREM 7: the physical four-pi witness constructs the P384
grand-unification receipt. -/
theorem rgMonotonicityGrandUnificationReceipt_nonempty_of_physicalFourPiWitness
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePhysicalFourPiRunningSigmaIndependentCoordinateWitness
      Index A CKMCarrier ->
      Nonempty (RGMonotonicityGrandUnificationReceipt Index A CKMCarrier) :=
  rgMonotonicityGrandUnificationReceipt_nonempty_of_weakEndpointWitness ∘
    existsZeroFreeWeakEndpointRunningSigmaIndependentCoordinateWitness_of_physicalFourPiWitness

/-! ## Physical four-pi normalized finite path table -/

/-- P395's reduced finite running-sigma path table with `fourPi = 4*pi` as the
normalization field, so the elementary positivity/nonidentity obligations are
derived internally. -/
structure PhysicalFourPiRunningSigmaYukawaRGPathTableProducer
    {Index A CKMCarrier : Type*} [AddCommGroup A]
    (Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier) where
  step : StandardModelScaleCode -> StandardModelScaleCode -> Prop
  fourPi_eq_realFourPi : Z.running.fourPi = realFourPi
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

namespace PhysicalFourPiRunningSigmaYukawaRGPathTableProducer

variable {Index A CKMCarrier : Type*} [AddCommGroup A]
variable {Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier}

/-- Convert the physical-normalization path table to P395's weak-endpoint path
table. -/
def toWeakEndpointRunningSigmaYukawaRGPathTableProducer
    (C : PhysicalFourPiRunningSigmaYukawaRGPathTableProducer Z) :
    WeakEndpointRunningSigmaYukawaRGPathTableProducer Z :=
  { step := C.step
    fourPi_pos := by
      rw [C.fourPi_eq_realFourPi]
      exact realFourPi_pos
    fourPi_ne_one := by
      rw [C.fourPi_eq_realFourPi]
      exact realFourPi_ne_one
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

/-- Convert the physical-normalization path table to P394's full finite
running-sigma table. -/
def toRunningSigmaYukawaRGPathTableProducer
    (C : PhysicalFourPiRunningSigmaYukawaRGPathTableProducer Z) :
    RunningSigmaYukawaRGPathTableProducer Z :=
  C.toWeakEndpointRunningSigmaYukawaRGPathTableProducer
    |>.toRunningSigmaYukawaRGPathTableProducer

/-- The physical-normalization path table supplies the physical-normalization
coordinate witness. -/
theorem toPhysicalFourPiRunningSigmaIndependentCoordinateWitness
    (C : PhysicalFourPiRunningSigmaYukawaRGPathTableProducer Z) :
    PhysicalFourPiRunningSigmaIndependentCoordinateWitness Z := by
  exact
    { fourPi_eq_realFourPi := C.fourPi_eq_realFourPi
      selected_yukawa_sigma_le_weak :=
        C.toRunningSigmaYukawaRGPathTableProducer.selected_yukawa_sigma_le_weak }

end PhysicalFourPiRunningSigmaYukawaRGPathTableProducer

/-- A zero-free certificate equipped with the physical four-pi finite
running-sigma path table. -/
def ExistsZeroFreePhysicalFourPiRunningSigmaYukawaRGPathTableProducer
    (Index A CKMCarrier : Type*) [AddCommGroup A] : Prop :=
  ∃ Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier,
    Nonempty (PhysicalFourPiRunningSigmaYukawaRGPathTableProducer Z)

/-- THEOREM 11: the physical-normalization path table supplies P395's reduced
finite running-sigma table. -/
theorem existsZeroFreeWeakEndpointRunningSigmaYukawaRGPathTableProducer_of_physicalFourPiPathTable
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePhysicalFourPiRunningSigmaYukawaRGPathTableProducer
      Index A CKMCarrier ->
      ExistsZeroFreeWeakEndpointRunningSigmaYukawaRGPathTableProducer
        Index A CKMCarrier := by
  rintro ⟨Z, ⟨C⟩⟩
  exact ⟨Z, ⟨C.toWeakEndpointRunningSigmaYukawaRGPathTableProducer⟩⟩

/-- THEOREM 12: the physical-normalization path table supplies the physical
four-pi coordinate witness. -/
theorem existsZeroFreePhysicalFourPiRunningSigmaIndependentCoordinateWitness_of_pathTable
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePhysicalFourPiRunningSigmaYukawaRGPathTableProducer
      Index A CKMCarrier ->
      ExistsZeroFreePhysicalFourPiRunningSigmaIndependentCoordinateWitness
        Index A CKMCarrier := by
  rintro ⟨Z, ⟨C⟩⟩
  exact ⟨Z, ⟨C.toPhysicalFourPiRunningSigmaIndependentCoordinateWitness⟩⟩

/-- THEOREM 13: therefore the physical-normalization path table constructs
the P384 grand-unification receipt. -/
theorem rgMonotonicityGrandUnificationReceipt_nonempty_of_physicalFourPiPathTable
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePhysicalFourPiRunningSigmaYukawaRGPathTableProducer
      Index A CKMCarrier ->
      Nonempty (RGMonotonicityGrandUnificationReceipt Index A CKMCarrier) :=
  rgMonotonicityGrandUnificationReceipt_nonempty_of_weakEndpointPathTable ∘
    existsZeroFreeWeakEndpointRunningSigmaYukawaRGPathTableProducer_of_physicalFourPiPathTable

end StandardModelConstraint
end SaturationMonoid
