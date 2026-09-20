import H0mework.Physics.Generation.P417

/-!
# Proposition 418: collapse of the general Poincare-generation producer on the
Standard-Model carrier

P416 names a general Poincare-resolved generation producer with an arbitrary
generation carrier `Gen`.  P417 constructs the finite Standard-Model carrier
map explicitly.

This file proves the exact collapse between the two surfaces when
`Gen = StandardModelFermionGeneration`: the arbitrary injection field carries
no additional existence content beyond P417's concrete Standard-Model
resolution.  Equivalently, at the receipt level, the P416/P417 generation
surface exists iff the current single-source holy-grail receipt exists together
with a 4D Poincare geometry certificate.

Boundary: this is still finite/certificate-relative.  It does not construct
the manifold Poincare-duality certificate or the physical RG/threshold table.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

open AffineRelaxation.GeometryConnection

/-! ## The Standard-Model instance of P416's producer has no extra content -/

/-- THEOREM 1: for the concrete Standard-Model generation carrier, P416's
abstract Poincare generation producer exists iff a 4D Poincare geometry
certificate exists. -/
theorem standardModelPoincareFermionGenerationProducer_nonempty_iff_geometry :
    Nonempty
        (PoincareFermionGenerationProducer
          StandardModelFermionGeneration) ↔
      Nonempty FourDimensionalPoincareGenerationSlotCertificate := by
  constructor
  · rintro ⟨P⟩
    exact ⟨P.geometry⟩
  · rintro ⟨G⟩
    exact ⟨standardModelPoincareFermionGenerationProducer G⟩

/-- THEOREM 2: P416's general resolved surface, specialized to the concrete
Standard-Model generation carrier, forgets to P417's concrete resolved
surface. -/
theorem existsStandardModelPoincareResolved_of_poincareResolvedStandardModel
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsPoincareResolvedSigmaYukawaRGPathTableProducer
        Index A CKMCarrier StandardModelFermionGeneration ->
      ExistsStandardModelPoincareResolvedSigmaYukawaRGPathTableProducer
        Index A CKMCarrier := by
  rintro ⟨atoms, ⟨P⟩⟩
  exact ⟨atoms, ⟨{ table := P.table, geometry := P.generation.geometry }⟩⟩

/-- THEOREM 3: exact collapse.  For
`Gen = StandardModelFermionGeneration`, P416's general surface and P417's
concrete Standard-Model surface have exactly the same existence content. -/
theorem poincareResolvedStandardModel_nonempty_iff_standardModelPoincareResolved
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsPoincareResolvedSigmaYukawaRGPathTableProducer
        Index A CKMCarrier StandardModelFermionGeneration ↔
      ExistsStandardModelPoincareResolvedSigmaYukawaRGPathTableProducer
        Index A CKMCarrier := by
  constructor
  · exact existsStandardModelPoincareResolved_of_poincareResolvedStandardModel
  · exact existsPoincareResolved_of_standardModelPoincareResolved

/-- THEOREM 4: receipt-level collapse.  The P416 general surface specialized
to the concrete Standard-Model generation carrier exists iff the current
single-source holy-grail receipt exists and a 4D Poincare geometry certificate
exists. -/
theorem poincareResolvedStandardModel_nonempty_iff_receipt_and_geometry
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsPoincareResolvedSigmaYukawaRGPathTableProducer
        Index A CKMCarrier StandardModelFermionGeneration ↔
      Nonempty
        (SingleSourcePhysicalGrandUnificationHolyGrailReceipt
          Index A CKMCarrier) ∧
        Nonempty FourDimensionalPoincareGenerationSlotCertificate := by
  exact
    poincareResolvedStandardModel_nonempty_iff_standardModelPoincareResolved.trans
      standardModelPoincareResolved_nonempty_iff_receipt_and_geometry

/-- THEOREM 5: downstream citation for the collapsed Standard-Model Poincare
surface. -/
theorem poincareResolvedStandardModel_singleSource_holy_grail_receipt
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsPoincareResolvedSigmaYukawaRGPathTableProducer
        Index A CKMCarrier StandardModelFermionGeneration ->
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
    standardModelPoincareResolved_singleSource_holy_grail_receipt
      ((poincareResolvedStandardModel_nonempty_iff_standardModelPoincareResolved).mp h)

end StandardModelConstraint
end SaturationMonoid
