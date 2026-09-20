import H0mework.Physics.SourceForms.P412

/-!
# Proposition 413: atom-native holy-grail front door

P412 proves that the single-source holy-grail receipt is equivalent to a
physical four-pi running-sigma corridor carried by one primitive atom object.
This file removes the last projection language from that front door.

Instead of stating the remaining corridor on `atoms.toZeroFree.running`, the
native surface is stated directly on the primitive fields:

* `atoms.fourPi = 4*pi`;
* `atoms.sigma (yukawa y) <= atoms.sigma weak`.

Boundary: this is still producer-relative.  It does not construct the primitive
atom object or prove the physical inequalities; it proves that the remaining
obligation can be expressed without a `toZeroFree` wrapper.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Atom-native physical sigma corridor -/

/-- The current tightest native producer surface for the physical
grand-unification target.

All fields are on the primitive atom object itself.  The `toZeroFree`
projection is no longer part of the statement. -/
structure PrimitiveAtomNativePhysicalSigmaCorridor
    (Index A CKMCarrier : Type*) [AddCommGroup A] where
  atoms : GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier
  fourPi_eq_realFourPi : atoms.fourPi = realFourPi
  selected_yukawa_sigma_le_weak :
    ∀ y : YukawaParameter,
      atoms.sigma (StandardModelScaleCode.yukawa y) ≤
        atoms.sigma StandardModelScaleCode.weak

namespace PrimitiveAtomNativePhysicalSigmaCorridor

variable {Index A CKMCarrier : Type*} [AddCommGroup A]

/-- THEOREM 1: the atom-native corridor is exactly P412's same-source
primitive corridor after opening `toZeroFree`. -/
def toPrimitivePhysicalFourPiSigmaCorridor
    (P : PrimitiveAtomNativePhysicalSigmaCorridor Index A CKMCarrier) :
    PrimitivePhysicalFourPiSigmaCorridor Index A CKMCarrier := by
  exact
    { atoms := P.atoms
      fourPi_eq_realFourPi := by
        simpa [GrandUnificationPrimitiveProducerAtoms.toZeroFree,
          GrandUnificationPrimitiveProducerAtoms.toRunning]
          using P.fourPi_eq_realFourPi
      selected_yukawa_sigma_le_weak := by
        intro y
        simpa [SelectedYukawaSigmaBoundedByWeak,
          GrandUnificationPrimitiveProducerAtoms.toZeroFree,
          GrandUnificationPrimitiveProducerAtoms.toRunning]
          using P.selected_yukawa_sigma_le_weak y }

/-- THEOREM 2: atom-native corridors directly build the single-source
holy-grail receipt. -/
theorem toSingleSourcePhysicalHolyGrailReceipt
    (P : PrimitiveAtomNativePhysicalSigmaCorridor Index A CKMCarrier) :
    Nonempty
      (SingleSourcePhysicalGrandUnificationHolyGrailReceipt
        Index A CKMCarrier) :=
  P.toPrimitivePhysicalFourPiSigmaCorridor.toSingleSourcePhysicalHolyGrailReceipt

end PrimitiveAtomNativePhysicalSigmaCorridor

namespace PrimitivePhysicalFourPiSigmaCorridor

variable {Index A CKMCarrier : Type*} [AddCommGroup A]

/-- THEOREM 3: P412's same-source primitive corridor is atom-native. -/
def toPrimitiveAtomNativePhysicalSigmaCorridor
    (P : PrimitivePhysicalFourPiSigmaCorridor Index A CKMCarrier) :
    PrimitiveAtomNativePhysicalSigmaCorridor Index A CKMCarrier := by
  exact
    { atoms := P.atoms
      fourPi_eq_realFourPi := by
        simpa [GrandUnificationPrimitiveProducerAtoms.toZeroFree,
          GrandUnificationPrimitiveProducerAtoms.toRunning]
          using P.fourPi_eq_realFourPi
      selected_yukawa_sigma_le_weak := by
        intro y
        simpa [SelectedYukawaSigmaBoundedByWeak,
          GrandUnificationPrimitiveProducerAtoms.toZeroFree,
          GrandUnificationPrimitiveProducerAtoms.toRunning]
          using P.selected_yukawa_sigma_le_weak y }

end PrimitivePhysicalFourPiSigmaCorridor

/-! ## Exact native normal forms -/

/-- THEOREM 4: P412's same-source corridor and the atom-native corridor have
the same existence content. -/
theorem primitivePhysicalSigmaCorridor_nonempty_iff_atomNativeSigmaCorridor
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    Nonempty (PrimitivePhysicalFourPiSigmaCorridor
        Index A CKMCarrier) ↔
      Nonempty (PrimitiveAtomNativePhysicalSigmaCorridor
        Index A CKMCarrier) := by
  constructor
  · rintro ⟨P⟩
    exact ⟨P.toPrimitiveAtomNativePhysicalSigmaCorridor⟩
  · rintro ⟨P⟩
    exact ⟨P.toPrimitivePhysicalFourPiSigmaCorridor⟩

/-- THEOREM 5: atom-native exact normal form.  The fully canonical
single-source holy-grail receipt exists iff the primitive atom object itself
has `fourPi = 4*pi` and the selected running-sigma weak corridor in its native
fields. -/
theorem singleSourcePhysicalHolyGrailReceipt_nonempty_iff_atomNativeSigmaCorridor
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    Nonempty
        (SingleSourcePhysicalGrandUnificationHolyGrailReceipt
          Index A CKMCarrier) ↔
      Nonempty (PrimitiveAtomNativePhysicalSigmaCorridor
        Index A CKMCarrier) := by
  exact
    singleSourcePhysicalHolyGrailReceipt_nonempty_iff_primitivePhysicalSigmaCorridor.trans
      primitivePhysicalSigmaCorridor_nonempty_iff_atomNativeSigmaCorridor

/-- THEOREM 6: compact holy-grail receipt from atom-native primitive fields. -/
theorem atomNativeSigmaCorridor_singleSource_holy_grail_receipt
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    Nonempty (PrimitiveAtomNativePhysicalSigmaCorridor Index A CKMCarrier) ->
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
    primitivePhysicalSigmaCorridor_singleSource_holy_grail_receipt
      ((primitivePhysicalSigmaCorridor_nonempty_iff_atomNativeSigmaCorridor).mpr h)

end StandardModelConstraint
end SaturationMonoid
