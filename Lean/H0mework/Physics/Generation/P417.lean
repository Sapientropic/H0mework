import H0mework.Physics.Generation.P416

/-!
# Proposition 417: the Standard-Model generation carrier is the Poincare slot carrier

P416 proves a producer-relative statement: any fermion-generation carrier that
injects into the 4D Poincare pairing slots admits no fourth independent
generation.

This file closes the finite carrier part for the actual Standard-Model
three-family surface.  The concrete `StandardModelFermionGeneration` type is
equivalent to the three 4D Poincare slots, the nine Yukawa rows hit all three
slots, and a Standard-Model Poincare-resolved sigma table is exactly a P415
nine-row table together with a 4D Poincare geometry certificate.

Boundary: the genuine geometry certificate remains producer data.  What is no
longer producer data is the finite injection from the Standard-Model generation
carrier into the Poincare slot carrier.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

open AffineRelaxation.GeometryConnection

/-! ## Concrete Standard-Model generation slot equivalence -/

/-- The concrete Standard-Model generation carrier maps to the three 4D
Poincare slots. -/
def standardModelGenerationPoincareSlot :
    StandardModelFermionGeneration -> FourDimensionalPoincareSlot
  | .first => .scalarVolume
  | .second => .connectionCurrent
  | .third => .curvature

/-- The inverse finite map from 4D Poincare slots to Standard-Model
generations. -/
def poincareSlotStandardModelGeneration :
    FourDimensionalPoincareSlot -> StandardModelFermionGeneration
  | .scalarVolume => .first
  | .connectionCurrent => .second
  | .curvature => .third

/-- THEOREM 1: the Standard-Model generation carrier is equivalent to the 4D
Poincare slot carrier. -/
def standardModelGenerationPoincareEquiv :
    StandardModelFermionGeneration ≃ FourDimensionalPoincareSlot where
  toFun := standardModelGenerationPoincareSlot
  invFun := poincareSlotStandardModelGeneration
  left_inv := by
    intro g
    cases g <;> rfl
  right_inv := by
    intro s
    cases s <;> rfl

/-- THEOREM 2: the concrete Standard-Model generation slot map is injective. -/
theorem standardModelGenerationPoincareSlot_injective :
    Function.Injective standardModelGenerationPoincareSlot := by
  intro a b h
  cases a <;> cases b <;> simp [standardModelGenerationPoincareSlot] at h ⊢

/-- THEOREM 3: the concrete Standard-Model generation slot map is surjective. -/
theorem standardModelGenerationPoincareSlot_surjective :
    Function.Surjective standardModelGenerationPoincareSlot := by
  intro s
  cases s
  · exact ⟨StandardModelFermionGeneration.first, rfl⟩
  · exact ⟨StandardModelFermionGeneration.second, rfl⟩
  · exact ⟨StandardModelFermionGeneration.third, rfl⟩

/-- THEOREM 4: a 4D Poincare geometry certificate canonically resolves the
concrete Standard-Model generation carrier. -/
def standardModelPoincareFermionGenerationProducer
    (geometry : FourDimensionalPoincareGenerationSlotCertificate) :
    PoincareFermionGenerationProducer StandardModelFermionGeneration where
  geometry := geometry
  slotOfGeneration := standardModelGenerationPoincareSlot
  slotOfGeneration_injective := standardModelGenerationPoincareSlot_injective

/-! ## Yukawa rows cover all Poincare generation slots -/

/-- The Poincare slot selected by a Yukawa row through the concrete
Standard-Model generation projection. -/
def yukawaPoincareSlot :
    YukawaParameter -> FourDimensionalPoincareSlot :=
  fun y => standardModelGenerationPoincareSlot (yukawaFermionGeneration y)

/-- THEOREM 5: first-generation Yukawa rows land in the scalar/volume
Poincare slot. -/
theorem yukawaPoincareSlot_first_rows :
    yukawaPoincareSlot YukawaParameter.up =
        FourDimensionalPoincareSlot.scalarVolume ∧
      yukawaPoincareSlot YukawaParameter.down =
        FourDimensionalPoincareSlot.scalarVolume ∧
      yukawaPoincareSlot YukawaParameter.electron =
        FourDimensionalPoincareSlot.scalarVolume := by
  simp [yukawaPoincareSlot, yukawaFermionGeneration,
    standardModelGenerationPoincareSlot]

/-- THEOREM 6: second-generation Yukawa rows land in the connection/current
Poincare slot. -/
theorem yukawaPoincareSlot_second_rows :
    yukawaPoincareSlot YukawaParameter.charm =
        FourDimensionalPoincareSlot.connectionCurrent ∧
      yukawaPoincareSlot YukawaParameter.strange =
        FourDimensionalPoincareSlot.connectionCurrent ∧
      yukawaPoincareSlot YukawaParameter.muon =
        FourDimensionalPoincareSlot.connectionCurrent := by
  simp [yukawaPoincareSlot, yukawaFermionGeneration,
    standardModelGenerationPoincareSlot]

/-- THEOREM 7: third-generation Yukawa rows land in the curvature Poincare
slot. -/
theorem yukawaPoincareSlot_third_rows :
    yukawaPoincareSlot YukawaParameter.top =
        FourDimensionalPoincareSlot.curvature ∧
      yukawaPoincareSlot YukawaParameter.bottom =
        FourDimensionalPoincareSlot.curvature ∧
      yukawaPoincareSlot YukawaParameter.tau =
        FourDimensionalPoincareSlot.curvature := by
  simp [yukawaPoincareSlot, yukawaFermionGeneration,
    standardModelGenerationPoincareSlot]

/-- THEOREM 8: the nine Standard-Model Yukawa rows hit every 4D Poincare
generation slot. -/
theorem yukawaPoincareSlot_surjective :
    Function.Surjective yukawaPoincareSlot := by
  intro s
  cases s
  · exact ⟨YukawaParameter.up, rfl⟩
  · exact ⟨YukawaParameter.charm, rfl⟩
  · exact ⟨YukawaParameter.top, rfl⟩

/-! ## Standard-Model Poincare-resolved holy-grail table -/

/-- A P415 nine-row sigma table together with a 4D Poincare geometry
certificate.  The finite Standard-Model generation-to-slot map is constructed
above and is not an extra field. -/
structure StandardModelPoincareResolvedSigmaYukawaRGPathTableProducer
    {Index A CKMCarrier : Type*} [AddCommGroup A]
    (atoms : GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier) where
  table : PrimitiveAtomNativeSigmaYukawaRGPathTableProducer atoms
  geometry : FourDimensionalPoincareGenerationSlotCertificate

namespace StandardModelPoincareResolvedSigmaYukawaRGPathTableProducer

variable {Index A CKMCarrier : Type*} [AddCommGroup A]
variable {atoms : GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier}

/-- THEOREM 9: the Standard-Model resolved table forgets to P415's table. -/
def toPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
    (P : StandardModelPoincareResolvedSigmaYukawaRGPathTableProducer atoms) :
    PrimitiveAtomNativeSigmaYukawaRGPathTableProducer atoms :=
  P.table

/-- THEOREM 10: the Standard-Model resolved table is an instance of P416's
general Poincare-resolved producer. -/
def toPoincareResolvedSigmaYukawaRGPathTableProducer
    (P : StandardModelPoincareResolvedSigmaYukawaRGPathTableProducer atoms) :
    PoincareResolvedSigmaYukawaRGPathTableProducer
      (Index := Index) (A := A) (CKMCarrier := CKMCarrier)
      (Gen := StandardModelFermionGeneration) atoms where
  table := P.table
  generation := standardModelPoincareFermionGenerationProducer P.geometry
  yukawaGeneration := yukawaFermionGeneration

/-- THEOREM 11: therefore the concrete Standard-Model resolved table rules out
a fourth independent generation. -/
theorem no_fourth_generation
    (P : StandardModelPoincareResolvedSigmaYukawaRGPathTableProducer atoms) :
    IsEmpty (Fin 4 ↪ StandardModelFermionGeneration) :=
  P.toPoincareResolvedSigmaYukawaRGPathTableProducer.no_fourth_generation

end StandardModelPoincareResolvedSigmaYukawaRGPathTableProducer

/-- Existence of a primitive atom object carrying P415's nine-row table plus a
4D Poincare geometry certificate, with the Standard-Model finite carrier map
constructed rather than supplied. -/
def ExistsStandardModelPoincareResolvedSigmaYukawaRGPathTableProducer
    (Index A CKMCarrier : Type*) [AddCommGroup A] : Prop :=
  ∃ atoms : GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier,
    Nonempty
      (StandardModelPoincareResolvedSigmaYukawaRGPathTableProducer atoms)

/-- THEOREM 12: the Standard-Model resolved surface is exactly P415's table
surface plus a 4D Poincare geometry certificate. -/
theorem standardModelPoincareResolved_nonempty_iff_table_and_geometry
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsStandardModelPoincareResolvedSigmaYukawaRGPathTableProducer
        Index A CKMCarrier ↔
      ExistsPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
        Index A CKMCarrier ∧
        Nonempty FourDimensionalPoincareGenerationSlotCertificate := by
  constructor
  · rintro ⟨atoms, ⟨P⟩⟩
    exact ⟨⟨atoms, ⟨P.table⟩⟩, ⟨P.geometry⟩⟩
  · rintro ⟨⟨atoms, ⟨T⟩⟩, ⟨G⟩⟩
    exact ⟨atoms, ⟨{ table := T, geometry := G }⟩⟩

/-- THEOREM 13: exact receipt-level normal form.  A concrete Standard-Model
Poincare-resolved surface exists iff the current single-source holy-grail
receipt exists and a 4D Poincare geometry certificate exists. -/
theorem standardModelPoincareResolved_nonempty_iff_receipt_and_geometry
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsStandardModelPoincareResolvedSigmaYukawaRGPathTableProducer
        Index A CKMCarrier ↔
      Nonempty
        (SingleSourcePhysicalGrandUnificationHolyGrailReceipt
          Index A CKMCarrier) ∧
        Nonempty FourDimensionalPoincareGenerationSlotCertificate := by
  constructor
  · intro h
    have htg :=
      (standardModelPoincareResolved_nonempty_iff_table_and_geometry).mp h
    exact
      ⟨(singleSourcePhysicalHolyGrailReceipt_nonempty_iff_sigmaYukawaRGPathTable).mpr
          htg.1,
        htg.2⟩
  · rintro ⟨hreceipt, hgeom⟩
    exact
      (standardModelPoincareResolved_nonempty_iff_table_and_geometry).mpr
        ⟨(singleSourcePhysicalHolyGrailReceipt_nonempty_iff_sigmaYukawaRGPathTable).mp
            hreceipt,
          hgeom⟩

/-- THEOREM 14: Standard-Model resolved tables supply the P416 general
Poincare-resolved surface with `Gen = StandardModelFermionGeneration`. -/
theorem existsPoincareResolved_of_standardModelPoincareResolved
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsStandardModelPoincareResolvedSigmaYukawaRGPathTableProducer
        Index A CKMCarrier ->
      ExistsPoincareResolvedSigmaYukawaRGPathTableProducer
        Index A CKMCarrier StandardModelFermionGeneration := by
  rintro ⟨atoms, ⟨P⟩⟩
  exact
    ⟨atoms,
      ⟨P.toPoincareResolvedSigmaYukawaRGPathTableProducer⟩⟩

/-- THEOREM 15: a Standard-Model Poincare-resolved table supplies the current
single-source holy-grail receipt. -/
theorem standardModelPoincareResolved_singleSource_holy_grail_receipt
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsStandardModelPoincareResolvedSigmaYukawaRGPathTableProducer
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
    poincareResolvedSigmaYukawaRGPathTable_singleSource_holy_grail_receipt
      (existsPoincareResolved_of_standardModelPoincareResolved h)

end StandardModelConstraint
end SaturationMonoid
