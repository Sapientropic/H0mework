import H0mework.Physics.SourceForms.P406

/-!
# Proposition 407: single-source physical holy-grail receipt

P406 made the physical holy-grail receipt coherent at the outer `zeroFree` and
RG-certificate boundary.  This file tightens one more central seam: the receipt
is generated from one primitive producer atom object.

The single-source producer is:

* primitive grand-unification atoms;
* a physical alpha-RG monotonicity producer for `atoms.toZeroFree`.

From that one source, Lean constructs the P384 receipt whose `zeroFree`, RG
certificate, unified formula spine, and primitive atom payload are all the
canonical projections of the same object.

Boundary: this is still producer-relative.  It does not construct the primitive
atoms or the physical RG/threshold proof; it makes the exact single-source
object those producers must fill.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Single-source producer surface -/

/-- The remaining physical producer surface in its single-source form:
primitive Standard-Model grand-unification atoms plus a physical alpha-RG
monotonicity proof for the zero-free certificate opened from those atoms. -/
def ExistsSingleSourcePhysicalGrandUnificationProducer
    (Index A CKMCarrier : Type*) [AddCommGroup A] : Prop :=
  ∃ atoms : GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier,
    Nonempty (PhysicalAlphaRGMonotonicityProducer atoms.toZeroFree)

/-- THEOREM 1: the single-source producer forgets to P404's physical
alpha-RG producer surface. -/
theorem existsPhysicalAlphaRGMonotonicity_of_singleSource
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsSingleSourcePhysicalGrandUnificationProducer Index A CKMCarrier ->
      ExistsZeroFreePhysicalAlphaRGMonotonicityProducer
        Index A CKMCarrier := by
  rintro ⟨atoms, ⟨physicalRG⟩⟩
  exact ⟨atoms.toZeroFree, ⟨physicalRG⟩⟩

/-! ## Fully canonical receipt -/

/-- A fully canonical physical holy-grail receipt.

Compared with P406, this receipt also remembers the primitive atom object and
requires the embedded spine and primitive-atom fields to be the canonical
projections of that same object. -/
structure SingleSourcePhysicalGrandUnificationHolyGrailReceipt
    (Index A CKMCarrier : Type*) [AddCommGroup A] where
  atoms : GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier
  physicalRG : PhysicalAlphaRGMonotonicityProducer atoms.toZeroFree
  receipt : RGMonotonicityGrandUnificationReceipt Index A CKMCarrier
  receipt_zeroFree_eq : receipt.zeroFree = atoms.toZeroFree
  receipt_rg_heq_physicalRG :
    HEq receipt.rg physicalRG.toSelectedYukawaRGMonotonicityCertificate
  receipt_spine_eq_atoms :
    receipt.spine = atoms.toUnifiedFormulaSpine
  receipt_primitiveAtoms_eq : receipt.primitiveAtoms = atoms

namespace SingleSourcePhysicalGrandUnificationHolyGrailReceipt

variable {Index A CKMCarrier : Type*} [AddCommGroup A]

/-- THEOREM 2: single-source receipts forget to P406 canonical receipts. -/
def toCanonicalPhysicalGrandUnificationHolyGrailReceipt
    (C : SingleSourcePhysicalGrandUnificationHolyGrailReceipt
      Index A CKMCarrier) :
    CanonicalPhysicalGrandUnificationHolyGrailReceipt Index A CKMCarrier where
  zeroFree := C.atoms.toZeroFree
  physicalRG := C.physicalRG
  receipt := C.receipt
  receipt_zeroFree_eq := C.receipt_zeroFree_eq
  receipt_rg_heq_physicalRG := C.receipt_rg_heq_physicalRG

/-- THEOREM 3: the embedded P384 receipt's zero-free object is the primitive
atoms' opened zero-free object. -/
theorem receipt_zeroFree_is_atoms
    (C : SingleSourcePhysicalGrandUnificationHolyGrailReceipt
      Index A CKMCarrier) :
    C.receipt.zeroFree = C.atoms.toZeroFree :=
  C.receipt_zeroFree_eq

/-- THEOREM 4: the embedded P384 receipt's RG certificate is the forgetful
image of the same physical alpha-RG producer. -/
theorem receipt_rg_is_physical_forgetful_image
    (C : SingleSourcePhysicalGrandUnificationHolyGrailReceipt
      Index A CKMCarrier) :
    HEq C.receipt.rg C.physicalRG.toSelectedYukawaRGMonotonicityCertificate :=
  C.receipt_rg_heq_physicalRG

/-- THEOREM 5: the embedded formula spine is exactly the canonical spine
generated from the primitive atoms. -/
theorem receipt_spine_is_atoms_spine
    (C : SingleSourcePhysicalGrandUnificationHolyGrailReceipt
      Index A CKMCarrier) :
    C.receipt.spine = C.atoms.toUnifiedFormulaSpine :=
  C.receipt_spine_eq_atoms

/-- THEOREM 6: the embedded primitive atom payload is exactly the source atom
object. -/
theorem receipt_primitiveAtoms_is_atoms
    (C : SingleSourcePhysicalGrandUnificationHolyGrailReceipt
      Index A CKMCarrier) :
    C.receipt.primitiveAtoms = C.atoms :=
  C.receipt_primitiveAtoms_eq

/-- THEOREM 7: after rewriting by the single-source spine equality, the
target's sampled zero-free certificate is the same opened primitive atom
certificate. -/
theorem target_sampled_zeroFree_is_atoms
    (C : SingleSourcePhysicalGrandUnificationHolyGrailReceipt
      Index A CKMCarrier) :
    C.receipt.spine.target.sampled.zeroFree = C.atoms.toZeroFree := by
  rw [C.receipt_spine_is_atoms_spine]
  rfl

/-- THEOREM 8: single-source receipts still carry the full P406 holy-grail
receipt, now with the spine/atom source coherence exposed. -/
theorem holy_grail_receipt
    (C : SingleSourcePhysicalGrandUnificationHolyGrailReceipt
      Index A CKMCarrier) :
    NoContinuousFreeParameters
        C.receipt.spine.target.sampled.zeroFree.running.pinned.base.constraints ∧
      (∀ p : ParameterVector ℝ,
        C.receipt.spine.target.sampled.zeroFree.running.pinned.base.constraints p ->
          p StandardModelParameter.qcd_theta = 0) ∧
      alphaEMFromIntegerConstraint ℝ = (1 : ℝ) / (137 : ℝ) ∧
      gutWeakMixingFromStructuralCards ℝ = threeEighths ℝ ∧
      alphaGUTInverseFromStructuralCards ℝ = ((133 : ℝ) / (3 : ℝ)) ∧
      C.receipt.spine.target.strongResidualProducer.correctedOutput =
        alphaStrongDisplayed ℝ ∧
      (ckmCPDepthSum : ℝ) * C.receipt.spine.target.cpRunningSigma =
        cpRawPhaseClaim ℝ ∧
      cpDeltaCPClaim ℝ =
        cpTauProxy ℝ -
          (ckmCPDepthSum : ℝ) * C.receipt.spine.target.cpRunningSigma ∧
      (∀ p : ParameterVector ℝ,
        C.receipt.spine.target.sampled.zeroFree.running.pinned.base.constraints p ->
          ∀ y : YukawaParameter,
            p (yukawaSlot y) =
              (C.receipt.spine.target.sampled.zeroFree.running.pinned.yukawaAmplitude y) *
                AffineRelaxation.realDecayResidual
                  (C.receipt.spine.target.sampled.yukawaLambda y)
                  ((C.receipt.spine.target.sampled.zeroFree.running.pinned.yukawaExponent
                        C.receipt.spine.target.sampled.zeroFree.selectedSeed y :
                        ℝ) *
                    C.receipt.spine.target.sampled.yukawaStep y)) :=
  C.toCanonicalPhysicalGrandUnificationHolyGrailReceipt.holy_grail_receipt

end SingleSourcePhysicalGrandUnificationHolyGrailReceipt

/-! ## Single-source construction and normal form -/

/-- THEOREM 9: a single-source physical producer constructs the fully
canonical holy-grail receipt without choosing independent spine or atom
witnesses. -/
theorem singleSourcePhysicalHolyGrailReceipt_nonempty_of_producer
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsSingleSourcePhysicalGrandUnificationProducer Index A CKMCarrier ->
      Nonempty
        (SingleSourcePhysicalGrandUnificationHolyGrailReceipt
          Index A CKMCarrier) := by
  intro h
  rcases h with ⟨atoms, ⟨physicalRG⟩⟩
  let RGC : SelectedYukawaRGMonotonicityCertificate atoms.toZeroFree :=
    physicalRG.toSelectedYukawaRGMonotonicityCertificate
  let receipt : RGMonotonicityGrandUnificationReceipt Index A CKMCarrier :=
    { zeroFree := atoms.toZeroFree
      rg := RGC
      gaugeWeakCorridor :=
        selectedYukawaGaugeCouplingsBoundedByWeak_of_rgMonotonicity
          atoms.toZeroFree RGC
      spine := atoms.toUnifiedFormulaSpine
      primitiveAtoms := atoms }
  exact
    ⟨{ atoms := atoms
       physicalRG := physicalRG
       receipt := receipt
       receipt_zeroFree_eq := rfl
       receipt_rg_heq_physicalRG := HEq.rfl
       receipt_spine_eq_atoms := rfl
       receipt_primitiveAtoms_eq := rfl }⟩

/-- THEOREM 10: exact single-source normal form.  The fully canonical receipt
exists iff the single-source primitive+physical-RG producer exists. -/
theorem singleSourcePhysicalHolyGrailReceipt_nonempty_iff_producer
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    Nonempty
        (SingleSourcePhysicalGrandUnificationHolyGrailReceipt
          Index A CKMCarrier) ↔
      ExistsSingleSourcePhysicalGrandUnificationProducer
        Index A CKMCarrier := by
  constructor
  · rintro ⟨C⟩
    exact ⟨C.atoms, ⟨C.physicalRG⟩⟩
  · exact singleSourcePhysicalHolyGrailReceipt_nonempty_of_producer

/-- THEOREM 11: compact downstream citation for the single-source physical
holy-grail target. -/
theorem singleSourcePhysicalGrandUnification_holy_grail_receipt
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsSingleSourcePhysicalGrandUnificationProducer Index A CKMCarrier ->
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
  rcases singleSourcePhysicalHolyGrailReceipt_nonempty_of_producer h with ⟨C⟩
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
