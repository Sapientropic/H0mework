import H0mework.Physics.Generation.P418

/-!
# Proposition 419: concrete Standard-Model holy-grail output

P405-P418 progressively lower the Standard-Model grand-unification target from
an abstract receipt to primitive atom-native sigma tables and the concrete
three-generation Poincare slot carrier.

This file states the central normal form without another detour: the concrete
Standard-Model holy-grail output exists exactly when the two remaining physical
producers exist:

* physical alpha-RG monotonicity for the selected Yukawa scales;
* a 4D Poincare geometry certificate.

The output carries the current core receipt (`theta_QCD=0`, `alpha_em=1/137`,
`sin^2(theta_W)=3/8`, `alpha_GUT^{-1}=133/3`, strong-coupling displayed
closure, CKM running-sigma phase closure, sampled Yukawa residuals, and zero
continuous free parameters) plus the Poincare-generation consequence: no fourth
independent Standard-Model generation.

Boundary: the beta functions, threshold matching, CKM-depth producer, and the
manifold Poincare geometry certificate are still producer obligations.  What is
closed here is the exact Lean normal form of the "grand-unification holy grail"
surface once those two producers are supplied.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

open AffineRelaxation.GeometryConnection

/-! ## The two remaining central producers -/

/-- The concrete remaining physical front door for the current Standard-Model
holy-grail surface: P404's physical alpha-RG monotonicity producer plus a 4D
Poincare generation-slot geometry certificate. -/
def ExistsPhysicalAlphaRGPoincareGeometryProducer
    (Index A CKMCarrier : Type*) [AddCommGroup A] : Prop :=
  ExistsZeroFreePhysicalAlphaRGMonotonicityProducer Index A CKMCarrier ∧
    Nonempty FourDimensionalPoincareGenerationSlotCertificate

/-- THEOREM 1: the concrete Standard-Model Poincare-resolved surface is
equivalent to the two remaining central producers. -/
theorem standardModelPoincareResolved_nonempty_iff_physicalAlphaRG_and_geometry
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsStandardModelPoincareResolvedSigmaYukawaRGPathTableProducer
        Index A CKMCarrier ↔
      ExistsPhysicalAlphaRGPoincareGeometryProducer
        Index A CKMCarrier := by
  calc
    ExistsStandardModelPoincareResolvedSigmaYukawaRGPathTableProducer
        Index A CKMCarrier ↔
      Nonempty
          (SingleSourcePhysicalGrandUnificationHolyGrailReceipt
            Index A CKMCarrier) ∧
        Nonempty FourDimensionalPoincareGenerationSlotCertificate :=
        standardModelPoincareResolved_nonempty_iff_receipt_and_geometry
    _ ↔ ExistsPhysicalAlphaRGPoincareGeometryProducer
        Index A CKMCarrier := by
        constructor
        · rintro ⟨hreceipt, hgeometry⟩
          exact
            ⟨(singleSourcePhysicalHolyGrailReceipt_nonempty_iff_physicalAlphaRGMonotonicity).mp
                hreceipt,
              hgeometry⟩
        · rintro ⟨hphysical, hgeometry⟩
          exact
            ⟨(singleSourcePhysicalHolyGrailReceipt_nonempty_iff_physicalAlphaRGMonotonicity).mpr
                hphysical,
              hgeometry⟩

/-! ## Concrete holy-grail output -/

/-- The full single-source holy-grail receipt statement, factored out as a
`Prop` so downstream output objects can carry it without confusing the existing
theorem `C.holy_grail_receipt` (a proof term) for a proposition-valued field. -/
def SingleSourceHolyGrailReceiptStatement
    {Index A CKMCarrier : Type*} [AddCommGroup A]
    (C : SingleSourcePhysicalGrandUnificationHolyGrailReceipt
      Index A CKMCarrier) : Prop :=
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
                    (ckmCPDepthSum : ℝ) *
                      C.receipt.spine.target.cpRunningSigma ∧
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
                                C.receipt.spine.target.sampled.yukawaStep y))

/-- THEOREM 2: the existing single-source receipt theorem proves the factored
holy-grail receipt statement. -/
theorem singleSourceHolyGrailReceiptStatement_of_receipt
    {Index A CKMCarrier : Type*} [AddCommGroup A]
    (C : SingleSourcePhysicalGrandUnificationHolyGrailReceipt
      Index A CKMCarrier) :
    SingleSourceHolyGrailReceiptStatement C :=
  C.holy_grail_receipt

/-- The concrete Standard-Model holy-grail output surface.

This is not a new producer assumption.  It is the compact output object that
the two central producers above construct: a single-source receipt, a Poincare
geometry certificate, source-coherence equalities, the full existing holy-grail
receipt, and the finite-generation consequence.
-/
structure StandardModelPoincareHolyGrailOutput
    (Index A CKMCarrier : Type*) [AddCommGroup A] where
  receipt : SingleSourcePhysicalGrandUnificationHolyGrailReceipt
    Index A CKMCarrier
  geometry : FourDimensionalPoincareGenerationSlotCertificate
  receipt_zeroFree_eq : receipt.receipt.zeroFree = receipt.atoms.toZeroFree
  receipt_rg_heq_physicalRG :
    HEq receipt.receipt.rg
      receipt.physicalRG.toSelectedYukawaRGMonotonicityCertificate
  receipt_spine_eq_atoms :
    receipt.receipt.spine = receipt.atoms.toUnifiedFormulaSpine
  receipt_primitiveAtoms_eq : receipt.receipt.primitiveAtoms = receipt.atoms
  target_sampled_zeroFree_eq :
    receipt.receipt.spine.target.sampled.zeroFree = receipt.atoms.toZeroFree
  holy_grail : SingleSourceHolyGrailReceiptStatement receipt
  generation_equiv :
    StandardModelFermionGeneration ≃ FourDimensionalPoincareSlot
  yukawa_slots_cover : Function.Surjective yukawaPoincareSlot
  no_fourth_generation : IsEmpty (Fin 4 ↪ StandardModelFermionGeneration)

namespace StandardModelPoincareHolyGrailOutput

variable {Index A CKMCarrier : Type*} [AddCommGroup A]

/-- THEOREM 2: output objects forget to the two remaining central producers. -/
theorem toPhysicalAlphaRGPoincareGeometryProducer
    (O : StandardModelPoincareHolyGrailOutput Index A CKMCarrier) :
    ExistsPhysicalAlphaRGPoincareGeometryProducer Index A CKMCarrier := by
  exact
    ⟨(singleSourcePhysicalHolyGrailReceipt_nonempty_iff_physicalAlphaRGMonotonicity).mp
        ⟨O.receipt⟩,
      ⟨O.geometry⟩⟩

end StandardModelPoincareHolyGrailOutput

/-! ## Construction and exact normal forms -/

/-- THEOREM 3: the two remaining central producers construct the concrete
Standard-Model holy-grail output. -/
theorem standardModelPoincareHolyGrailOutput_nonempty_of_physicalAlphaRG_and_geometry
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsPhysicalAlphaRGPoincareGeometryProducer Index A CKMCarrier ->
      Nonempty (StandardModelPoincareHolyGrailOutput Index A CKMCarrier) := by
  rintro ⟨hphysical, ⟨geometry⟩⟩
  rcases
    (singleSourcePhysicalHolyGrailReceipt_nonempty_iff_physicalAlphaRGMonotonicity).mpr
      hphysical with
    ⟨C⟩
  exact
    ⟨{ receipt := C
       geometry := geometry
       receipt_zeroFree_eq := C.receipt_zeroFree_is_atoms
       receipt_rg_heq_physicalRG := C.receipt_rg_is_physical_forgetful_image
       receipt_spine_eq_atoms := C.receipt_spine_is_atoms_spine
       receipt_primitiveAtoms_eq := C.receipt_primitiveAtoms_is_atoms
       target_sampled_zeroFree_eq := C.target_sampled_zeroFree_is_atoms
       holy_grail := singleSourceHolyGrailReceiptStatement_of_receipt C
       generation_equiv := standardModelGenerationPoincareEquiv
       yukawa_slots_cover := yukawaPoincareSlot_surjective
       no_fourth_generation :=
        (standardModelPoincareFermionGenerationProducer geometry).no_fourth_generation }⟩

/-- THEOREM 4: exact output normal form.  The concrete holy-grail output exists
iff the physical alpha-RG producer and 4D Poincare geometry producer exist. -/
theorem standardModelPoincareHolyGrailOutput_nonempty_iff_physicalAlphaRG_and_geometry
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    Nonempty (StandardModelPoincareHolyGrailOutput Index A CKMCarrier) ↔
      ExistsPhysicalAlphaRGPoincareGeometryProducer Index A CKMCarrier := by
  constructor
  · rintro ⟨O⟩
    exact O.toPhysicalAlphaRGPoincareGeometryProducer
  · exact standardModelPoincareHolyGrailOutput_nonempty_of_physicalAlphaRG_and_geometry

/-- THEOREM 5: the concrete Standard-Model Poincare-resolved surface and the
concrete holy-grail output have exactly the same existence content. -/
theorem standardModelPoincareResolved_nonempty_iff_holyGrailOutput
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsStandardModelPoincareResolvedSigmaYukawaRGPathTableProducer
        Index A CKMCarrier ↔
      Nonempty (StandardModelPoincareHolyGrailOutput Index A CKMCarrier) := by
  exact
    standardModelPoincareResolved_nonempty_iff_physicalAlphaRG_and_geometry.trans
      standardModelPoincareHolyGrailOutput_nonempty_iff_physicalAlphaRG_and_geometry.symm

/-- THEOREM 6: the concrete Standard-Model Poincare-resolved surface rules out
a fourth independent Standard-Model generation. -/
theorem standardModelPoincareResolved_no_fourth_generation
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsStandardModelPoincareResolvedSigmaYukawaRGPathTableProducer
        Index A CKMCarrier ->
      IsEmpty (Fin 4 ↪ StandardModelFermionGeneration) := by
  rintro ⟨atoms, ⟨P⟩⟩
  exact P.no_fourth_generation

/-- THEOREM 7: compact central citation form.  The two remaining central
producers yield the full holy-grail output, including the full receipt,
generation-slot equivalence, Yukawa slot coverage, and no-fourth-generation
consequence. -/
theorem physicalAlphaRG_and_geometry_concrete_holy_grail_output
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsPhysicalAlphaRGPoincareGeometryProducer Index A CKMCarrier ->
      ∃ O : StandardModelPoincareHolyGrailOutput Index A CKMCarrier,
        SingleSourceHolyGrailReceiptStatement O.receipt ∧
          Nonempty
            (StandardModelFermionGeneration ≃ FourDimensionalPoincareSlot) ∧
          Function.Surjective yukawaPoincareSlot ∧
          IsEmpty (Fin 4 ↪ StandardModelFermionGeneration) := by
  intro h
  rcases
    standardModelPoincareHolyGrailOutput_nonempty_of_physicalAlphaRG_and_geometry h with
    ⟨O⟩
  exact
    ⟨O, O.holy_grail, ⟨O.generation_equiv⟩, O.yukawa_slots_cover,
      O.no_fourth_generation⟩

end StandardModelConstraint
end SaturationMonoid
