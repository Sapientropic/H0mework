import H0mework.Realization.Relations.FintypeDerivation
import H0mework.Physics.RunningSources.P415
import H0mework.Realization.RelaxationAlgebra.P282

/-!
# Proposition 416: Poincare slots as a fermion-generation producer

P280-P282 prove the finite Poincare-pairing arithmetic: in dimension four the
degree-pairing quotient has exactly three slots, and no four independent slots
can inject into it.

P415 proves the current Standard-Model holy-grail front door as an explicit
nine-row atom-native Yukawa RG table.

This file connects those two tracks.  It does **not** claim that geometry has
already produced physical fermion generations.  Instead it names the producer
surface and proves the finite consequence:

* any generation carrier that injects into the 4D Poincare slots admits no four
  independent generations;
* the Standard-Model Yukawa rows have a concrete three-family projection;
* a Poincare-resolved nine-row sigma table still supplies the P415 holy-grail
  receipt.

Boundary: the injection from physical generations to Poincare slots remains
producer data.  What is closed here is the algebra once that producer is
supplied.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

open AffineRelaxation.GeometryConnection

/-! ## Abstract Poincare generation producer -/

/-- A fermion-generation carrier resolved by the three 4D Poincare pairing
slots.

`Gen` is deliberately arbitrary: the no-four theorem below is not obtained by
defining generations to be a three-element type.  It follows from injectivity
into the Poincare slot carrier. -/
structure PoincareFermionGenerationProducer (Gen : Type*) where
  geometry : FourDimensionalPoincareGenerationSlotCertificate
  slotOfGeneration : Gen -> FourDimensionalPoincareSlot
  slotOfGeneration_injective : Function.Injective slotOfGeneration

namespace PoincareFermionGenerationProducer

variable {Gen : Type*}

/-- THEOREM 1: any generation carrier faithfully resolved by the 4D Poincare
slots has no fourth independent generation. -/
theorem no_fourth_generation
    (P : PoincareFermionGenerationProducer Gen) :
    IsEmpty (Fin 4 ↪ Gen) := by
  refine ⟨?_⟩
  intro e
  let h : Fin 4 ↪ FourDimensionalPoincareSlot :=
    { toFun := fun i => P.slotOfGeneration (e i)
      inj' := by
        intro i j hij
        apply e.injective
        exact P.slotOfGeneration_injective hij }
  exact no_four_independent_generation_slots_from_4D_poincare.false h

end PoincareFermionGenerationProducer

/-! ## Standard-Model three-family projection of Yukawa rows -/

/-- The three Standard-Model fermion generations as a concrete finite carrier
for the nine Yukawa rows. -/
inductive StandardModelFermionGeneration where
  | first
  | second
  | third
  deriving DecidableEq, Repr, FintypeViaProxy

namespace StandardModelFermionGeneration

/-- THEOREM 2: the concrete Standard-Model generation carrier has three
elements. -/
theorem card :
    Fintype.card StandardModelFermionGeneration = 3 := by
  decide

end StandardModelFermionGeneration

/-- The conventional three-family projection of the nine Yukawa slots. -/
def yukawaFermionGeneration :
    YukawaParameter -> StandardModelFermionGeneration
  | .up => .first
  | .down => .first
  | .electron => .first
  | .charm => .second
  | .strange => .second
  | .muon => .second
  | .top => .third
  | .bottom => .third
  | .tau => .third

/-- THEOREM 3: first-generation Yukawa rows. -/
theorem yukawaFermionGeneration_first_rows :
    yukawaFermionGeneration YukawaParameter.up =
        StandardModelFermionGeneration.first ∧
      yukawaFermionGeneration YukawaParameter.down =
        StandardModelFermionGeneration.first ∧
      yukawaFermionGeneration YukawaParameter.electron =
        StandardModelFermionGeneration.first := by
  simp [yukawaFermionGeneration]

/-- THEOREM 4: second-generation Yukawa rows. -/
theorem yukawaFermionGeneration_second_rows :
    yukawaFermionGeneration YukawaParameter.charm =
        StandardModelFermionGeneration.second ∧
      yukawaFermionGeneration YukawaParameter.strange =
        StandardModelFermionGeneration.second ∧
      yukawaFermionGeneration YukawaParameter.muon =
        StandardModelFermionGeneration.second := by
  simp [yukawaFermionGeneration]

/-- THEOREM 5: third-generation Yukawa rows. -/
theorem yukawaFermionGeneration_third_rows :
    yukawaFermionGeneration YukawaParameter.top =
        StandardModelFermionGeneration.third ∧
      yukawaFermionGeneration YukawaParameter.bottom =
        StandardModelFermionGeneration.third ∧
      yukawaFermionGeneration YukawaParameter.tau =
        StandardModelFermionGeneration.third := by
  simp [yukawaFermionGeneration]

/-! ## Generation-resolved holy-grail table -/

/-- P415's atom-native nine-row sigma table together with a Poincare
generation-resolution producer. -/
structure PoincareResolvedSigmaYukawaRGPathTableProducer
    {Index A CKMCarrier Gen : Type*} [AddCommGroup A]
    (atoms : GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier) where
  table : PrimitiveAtomNativeSigmaYukawaRGPathTableProducer atoms
  generation : PoincareFermionGenerationProducer Gen
  yukawaGeneration : YukawaParameter -> Gen

namespace PoincareResolvedSigmaYukawaRGPathTableProducer

variable {Index A CKMCarrier Gen : Type*} [AddCommGroup A]
variable {atoms : GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier}

/-- THEOREM 6: a generation-resolved table forgets to P415's nine-row sigma
table. -/
def toPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
    (P : PoincareResolvedSigmaYukawaRGPathTableProducer
      (Index := Index) (A := A) (CKMCarrier := CKMCarrier)
      (Gen := Gen) atoms) :
    PrimitiveAtomNativeSigmaYukawaRGPathTableProducer atoms :=
  P.table

/-- THEOREM 7: the Poincare part rules out a fourth independent generation. -/
theorem no_fourth_generation
    (P : PoincareResolvedSigmaYukawaRGPathTableProducer
      (Index := Index) (A := A) (CKMCarrier := CKMCarrier) (Gen := Gen) atoms) :
    IsEmpty (Fin 4 ↪ Gen) :=
  P.generation.no_fourth_generation

end PoincareResolvedSigmaYukawaRGPathTableProducer

/-- Existence of a primitive atom object carrying both the P415 nine-row table
and a Poincare generation-resolution producer. -/
def ExistsPoincareResolvedSigmaYukawaRGPathTableProducer
    (Index A CKMCarrier Gen : Type*) [AddCommGroup A] : Prop :=
  ∃ atoms : GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier,
    Nonempty
      (PoincareResolvedSigmaYukawaRGPathTableProducer
        (Index := Index) (A := A) (CKMCarrier := CKMCarrier)
        (Gen := Gen) atoms)

/-- THEOREM 8: a Poincare-resolved nine-row table supplies P415's native
sigma table surface. -/
theorem existsPrimitiveAtomNativeSigmaYukawaRGPathTable_of_poincareResolved
    {Index A CKMCarrier Gen : Type*} [AddCommGroup A] :
    ExistsPoincareResolvedSigmaYukawaRGPathTableProducer
        Index A CKMCarrier Gen ->
      ExistsPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
        Index A CKMCarrier := by
  rintro ⟨atoms, ⟨P⟩⟩
  exact ⟨atoms, ⟨P.toPrimitiveAtomNativeSigmaYukawaRGPathTableProducer⟩⟩

/-- THEOREM 9: a Poincare-resolved nine-row table supplies the current
single-source holy-grail receipt. -/
theorem poincareResolvedSigmaYukawaRGPathTable_singleSource_holy_grail_receipt
    {Index A CKMCarrier Gen : Type*} [AddCommGroup A] :
    ExistsPoincareResolvedSigmaYukawaRGPathTableProducer
        Index A CKMCarrier Gen ->
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
    sigmaYukawaRGPathTable_singleSource_holy_grail_receipt
      (existsPrimitiveAtomNativeSigmaYukawaRGPathTable_of_poincareResolved h)

end StandardModelConstraint
end SaturationMonoid
