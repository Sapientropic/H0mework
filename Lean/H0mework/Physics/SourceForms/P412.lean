import H0mework.Physics.CouplingSources.P411

/-!
# Proposition 412: primitive-atom running-sigma holy-grail normal form

P411 identifies the current single-source holy-grail receipt with the compact
physical four-pi running-sigma corridor on an opened zero-free certificate.
This file tightens the source boundary one more step: the corridor can be
carried by the primitive atom object itself.

The remaining front door is now:

* one primitive grand-unification atom object;
* physical `fourPi = 4*pi` for its opened zero-free certificate;
* the selected-Yukawa running-sigma weak corridor on that same opened
  certificate.

Boundary: this is still a normal-form theorem.  It does not derive the
primitive atoms, the `fourPi` normalization, or the RG/threshold inequalities;
it proves that no additional wrapper or independently chosen zero-free object
is needed at the holy-grail receipt boundary.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Primitive-atom physical sigma corridor -/

/-- The compact same-source producer surface for the current physical
grand-unification target: a primitive atom object whose opened zero-free
certificate already carries the physical four-pi selected-sigma weak
corridor. -/
structure PrimitivePhysicalFourPiSigmaCorridor
    (Index A CKMCarrier : Type*) [AddCommGroup A] where
  atoms : GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier
  fourPi_eq_realFourPi :
    atoms.toZeroFree.running.fourPi = realFourPi
  selected_yukawa_sigma_le_weak :
    SelectedYukawaSigmaBoundedByWeak atoms.toZeroFree

namespace PrimitivePhysicalFourPiSigmaCorridor

variable {Index A CKMCarrier : Type*} [AddCommGroup A]

/-- THEOREM 1: the primitive-atom corridor forgets to P411's zero-free
physical sigma corridor. -/
theorem toExistsZeroFreePhysicalFourPiRunningSigmaIndependentCoordinateWitness
    (P : PrimitivePhysicalFourPiSigmaCorridor Index A CKMCarrier) :
    ExistsZeroFreePhysicalFourPiRunningSigmaIndependentCoordinateWitness
      Index A CKMCarrier := by
  exact
    ⟨P.atoms.toZeroFree,
      ⟨{ fourPi_eq_realFourPi := P.fourPi_eq_realFourPi
         selected_yukawa_sigma_le_weak :=
          P.selected_yukawa_sigma_le_weak }⟩⟩

/-- THEOREM 2: the primitive-atom corridor builds a physical alpha-RG
producer indexed by the same opened atom object. -/
def toPhysicalAlphaRGMonotonicityProducer
    (P : PrimitivePhysicalFourPiSigmaCorridor Index A CKMCarrier) :
    PhysicalAlphaRGMonotonicityProducer P.atoms.toZeroFree :=
  let W : PhysicalFourPiRunningSigmaIndependentCoordinateWitness
      P.atoms.toZeroFree :=
    { fourPi_eq_realFourPi := P.fourPi_eq_realFourPi
      selected_yukawa_sigma_le_weak := P.selected_yukawa_sigma_le_weak }
  let H : PhysicalSelectedYukawaAlphaWeakBound P.atoms.toZeroFree :=
    W.toPhysicalFourPiGaugeWeakCorridorWitness
      |>.toPhysicalSelectedYukawaAlphaWeakBound
  H.toPhysicalAlphaRGStepPathProducer
    |>.toPhysicalAlphaRGMonotonicityProducer

/-- THEOREM 3: the primitive-atom corridor supplies P407's single-source
producer without reopening an independent primitive atom object. -/
theorem toExistsSingleSourcePhysicalGrandUnificationProducer
    (P : PrimitivePhysicalFourPiSigmaCorridor Index A CKMCarrier) :
    ExistsSingleSourcePhysicalGrandUnificationProducer
      Index A CKMCarrier := by
  exact ⟨P.atoms, ⟨P.toPhysicalAlphaRGMonotonicityProducer⟩⟩

/-- THEOREM 4: the primitive-atom corridor directly constructs the
single-source holy-grail receipt. -/
theorem toSingleSourcePhysicalHolyGrailReceipt
    (P : PrimitivePhysicalFourPiSigmaCorridor Index A CKMCarrier) :
    Nonempty
      (SingleSourcePhysicalGrandUnificationHolyGrailReceipt
        Index A CKMCarrier) :=
  singleSourcePhysicalHolyGrailReceipt_nonempty_of_producer
    P.toExistsSingleSourcePhysicalGrandUnificationProducer

end PrimitivePhysicalFourPiSigmaCorridor

/-! ## Exact receipt-level normal form -/

/-- THEOREM 5: any single-source holy-grail receipt exposes a primitive-atom
physical four-pi running-sigma corridor on its own atom object. -/
def primitivePhysicalFourPiSigmaCorridor_of_singleSourceReceipt
    {Index A CKMCarrier : Type*} [AddCommGroup A]
    (C : SingleSourcePhysicalGrandUnificationHolyGrailReceipt
      Index A CKMCarrier) :
    PrimitivePhysicalFourPiSigmaCorridor Index A CKMCarrier := by
  let H : PhysicalSelectedYukawaAlphaWeakBound C.atoms.toZeroFree :=
    C.physicalRG.toPhysicalSelectedYukawaAlphaWeakBound
  let W : PhysicalFourPiRunningSigmaIndependentCoordinateWitness
      C.atoms.toZeroFree :=
    H.toPhysicalFourPiGaugeWeakCorridorWitness
      |>.toPhysicalFourPiRunningSigmaIndependentCoordinateWitness
  exact
    { atoms := C.atoms
      fourPi_eq_realFourPi := W.fourPi_eq_realFourPi
      selected_yukawa_sigma_le_weak := W.selected_yukawa_sigma_le_weak }

/-- THEOREM 6: exact same-source normal form.  The fully canonical
single-source holy-grail receipt exists iff the primitive atom object itself
carries the compact physical four-pi running-sigma corridor. -/
theorem singleSourcePhysicalHolyGrailReceipt_nonempty_iff_primitivePhysicalSigmaCorridor
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    Nonempty
        (SingleSourcePhysicalGrandUnificationHolyGrailReceipt
          Index A CKMCarrier) ↔
      Nonempty (PrimitivePhysicalFourPiSigmaCorridor
        Index A CKMCarrier) := by
  constructor
  · rintro ⟨C⟩
    exact ⟨primitivePhysicalFourPiSigmaCorridor_of_singleSourceReceipt C⟩
  · rintro ⟨P⟩
    exact P.toSingleSourcePhysicalHolyGrailReceipt

/-- THEOREM 7: compact holy-grail receipt directly from the same-source
primitive physical sigma corridor. -/
theorem primitivePhysicalSigmaCorridor_singleSource_holy_grail_receipt
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    Nonempty (PrimitivePhysicalFourPiSigmaCorridor Index A CKMCarrier) ->
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
  rintro ⟨P⟩
  rcases P.toSingleSourcePhysicalHolyGrailReceipt with ⟨C⟩
  rcases C.holy_grail_receipt with
    ⟨_hfree, _htheta, hem, hweak, hgut, hstrong, hckm, _hdelta, _hyukawa⟩
  exact
    ⟨C, C.receipt_zeroFree_is_atoms,
      C.receipt_rg_is_physical_forgetful_image,
      C.receipt_spine_is_atoms_spine,
      C.receipt_primitiveAtoms_is_atoms,
      C.target_sampled_zeroFree_is_atoms,
      hem, hweak, hgut, hstrong, hckm⟩

end StandardModelConstraint
end SaturationMonoid
