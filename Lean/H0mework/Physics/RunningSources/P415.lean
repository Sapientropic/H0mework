import H0mework.Physics.SourceForms.P414

/-!
# Proposition 415: atom-native nine-slot sigma RG table

P414 lowers the single-source holy-grail receipt to an atom-native finite
sigma-step certificate.  Its selected-Yukawa path field is still written as a
function `∀ y : YukawaParameter`.

This file opens that final finite surface into the concrete nine rows a
physics/RG producer must actually emit:

`up, charm, top, down, strange, bottom, electron, muon, tau`.

The theorem is an exact normal form, not a new assumption: a nine-row table is
equivalent to P414's all-Yukawa finite sigma-step producer, and therefore to
the current single-source holy-grail receipt.

Boundary: the table entries, local sigma monotonicity, and anti-tautology are
still producer data.  This file only proves that the producer surface is truly
finite and named in primitive atom-native coordinates.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Atom-native nine-row sigma table -/

/-- Explicit nine-slot atom-native sigma RG path table.

This is P414's finite native sigma-step producer with the `∀ y` path field
expanded into named Standard-Model Yukawa rows. -/
structure PrimitiveAtomNativeSigmaYukawaRGPathTableProducer
    {Index A CKMCarrier : Type*} [AddCommGroup A]
    (atoms : GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier) where
  step : StandardModelScaleCode -> StandardModelScaleCode -> Prop
  reach_not_sigma_order :
    RGStepReach step ≠
      fun a b : StandardModelScaleCode => atoms.sigma a ≤ atoms.sigma b
  fourPi_eq_realFourPi : atoms.fourPi = realFourPi
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
      atoms.sigma a ≤ atoms.sigma b

namespace PrimitiveAtomNativeSigmaYukawaRGPathTableProducer

variable {Index A CKMCarrier : Type*} [AddCommGroup A]
variable {atoms : GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier}

/-- THEOREM 1: the explicit nine-row table fills P414's all-Yukawa path field. -/
theorem selected_yukawa_reaches_weak
    (C : PrimitiveAtomNativeSigmaYukawaRGPathTableProducer atoms) :
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

/-- THEOREM 2: the explicit nine-row table is P414's finite atom-native
sigma-step producer. -/
def toPrimitiveAtomNativeSigmaRGStepPathProducer
    (C : PrimitiveAtomNativeSigmaYukawaRGPathTableProducer atoms) :
    PrimitiveAtomNativeSigmaRGStepPathProducer atoms where
  step := C.step
  reach_not_sigma_order := C.reach_not_sigma_order
  fourPi_eq_realFourPi := C.fourPi_eq_realFourPi
  selected_yukawa_reaches_weak := C.selected_yukawa_reaches_weak
  step_sigma_monotone := C.step_sigma_monotone

end PrimitiveAtomNativeSigmaYukawaRGPathTableProducer

namespace PrimitiveAtomNativeSigmaRGStepPathProducer

variable {Index A CKMCarrier : Type*} [AddCommGroup A]
variable {atoms : GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier}

/-- THEOREM 3: P414's all-Yukawa finite sigma-step producer opens to the
explicit nine-row table. -/
def toPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
    (C : PrimitiveAtomNativeSigmaRGStepPathProducer atoms) :
    PrimitiveAtomNativeSigmaYukawaRGPathTableProducer atoms where
  step := C.step
  reach_not_sigma_order := C.reach_not_sigma_order
  fourPi_eq_realFourPi := C.fourPi_eq_realFourPi
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
  step_sigma_monotone := C.step_sigma_monotone

end PrimitiveAtomNativeSigmaRGStepPathProducer

/-! ## Existence-level exact normal form -/

/-- A primitive atom object equipped with an explicit nine-row native sigma
RG table. -/
def ExistsPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
    (Index A CKMCarrier : Type*) [AddCommGroup A] : Prop :=
  ∃ atoms : GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier,
    Nonempty (PrimitiveAtomNativeSigmaYukawaRGPathTableProducer atoms)

/-- THEOREM 4: a nine-row native sigma table supplies P414's finite
all-Yukawa producer. -/
theorem existsSigmaRGStepPath_of_primitiveAtomNativeSigmaYukawaRGPathTable
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
        Index A CKMCarrier ->
      ExistsPrimitiveAtomNativeSigmaRGStepPathProducer
        Index A CKMCarrier := by
  rintro ⟨atoms, ⟨C⟩⟩
  exact ⟨atoms, ⟨C.toPrimitiveAtomNativeSigmaRGStepPathProducer⟩⟩

/-- THEOREM 5: P414's finite all-Yukawa producer opens into the explicit
nine-row native sigma table. -/
theorem existsPrimitiveAtomNativeSigmaYukawaRGPathTable_of_sigmaRGStepPath
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsPrimitiveAtomNativeSigmaRGStepPathProducer
        Index A CKMCarrier ->
      ExistsPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
        Index A CKMCarrier := by
  rintro ⟨atoms, ⟨C⟩⟩
  exact ⟨atoms, ⟨C.toPrimitiveAtomNativeSigmaYukawaRGPathTableProducer⟩⟩

/-- THEOREM 6: exact normal form.  P414's atom-native finite sigma-step
producer exists iff the explicit nine-row native sigma table exists. -/
theorem sigmaRGStepPath_nonempty_iff_primitiveAtomNativeSigmaYukawaRGPathTable
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsPrimitiveAtomNativeSigmaRGStepPathProducer
        Index A CKMCarrier ↔
      ExistsPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
        Index A CKMCarrier := by
  constructor
  · exact existsPrimitiveAtomNativeSigmaYukawaRGPathTable_of_sigmaRGStepPath
  · exact existsSigmaRGStepPath_of_primitiveAtomNativeSigmaYukawaRGPathTable

/-- THEOREM 7: receipt-level exact normal form in explicit nine-row
atom-native sigma table coordinates. -/
theorem singleSourcePhysicalHolyGrailReceipt_nonempty_iff_sigmaYukawaRGPathTable
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    Nonempty
        (SingleSourcePhysicalGrandUnificationHolyGrailReceipt
          Index A CKMCarrier) ↔
      ExistsPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
        Index A CKMCarrier := by
  exact
    singleSourcePhysicalHolyGrailReceipt_nonempty_iff_sigmaRGStepPath.trans
      sigmaRGStepPath_nonempty_iff_primitiveAtomNativeSigmaYukawaRGPathTable

/-- THEOREM 8: compact holy-grail receipt from the explicit nine-row native
sigma RG table. -/
theorem sigmaYukawaRGPathTable_singleSource_holy_grail_receipt
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
        Index A CKMCarrier ->
      ∃ C : SingleSourcePhysicalGrandUnificationHolyGrailReceipt
          Index A CKMCarrier,
        C.receipt.zeroFree = C.atoms.toZeroFree ∧
        HEq C.receipt.rg
          C.physicalRG.toSelectedYukawaRGMonotonicityCertificate ∧
        C.receipt.spine = C.atoms.toUnifiedFormulaSpine ∧
        C.receipt.primitiveAtoms = C.atoms ∧
        C.receipt.spine.target.sampled.zeroFree = C.atoms.toZeroFree ∧
        alphaEMFromIntegerConstraint ℝ = (1 : ℝ) / (137 : ℝ) ∧
        gutWeakMixingFromStructuralCards ℝ = threeEighths ℝ ∧
        alphaGUTInverseFromStructuralCards ℝ = ((133 : ℝ) / (3 : ℝ)) ∧
        C.receipt.spine.target.strongResidualProducer.correctedOutput =
          alphaStrongDisplayed ℝ ∧
        (ckmCPDepthSum : ℝ) * C.receipt.spine.target.cpRunningSigma =
          cpRawPhaseClaim ℝ := by
  intro h
  exact
    sigmaRGStepPath_singleSource_holy_grail_receipt
      (existsSigmaRGStepPath_of_primitiveAtomNativeSigmaYukawaRGPathTable h)

end StandardModelConstraint
end SaturationMonoid
