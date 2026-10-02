import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.U8Revision.Header
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.CurrentFamilies.Coverage

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherU8Revision
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open ObstructionGeneratedMinimalCoface TypedSemanticWorldNetworkU8
noncomputable section
variable {N : WorldRelationNetwork.{0}} (source : SourceNativeLivingRootCurrentAt N)
    {U7 : U7ProducerCalculus N} {oldTheory : TheoryState N}
    {support : N.Support} {obstruction : N.ObstructionAt support}
    {failure : ActualExpressibilityFailure oldTheory obstruction}
    {rooted : RootedActualExpressibilityFailureAt source.root.toAuthoritativeRoot source.visit U7 failure}
    (original : FieldGroundedTypedSemanticWorldNetworkRevisionAt rooted)

def revisionCurrent : SourceNativeLivingRootCurrentAt original.generate.NewN :=
  ⟨original.generate.NewV, original.generate.newLivingRoot,
    .finite original.generate.newLivingRoot.toAuthoritativeRoot.toRoot.initialVisit⟩

def pairNetwork : Bool → WorldRelationNetwork.{0}
  | false => N
  | true => original.generate.NewN

def pairCurrent : (index : Bool) → SourceNativeLivingRootCurrentAt (pairNetwork source original index)
  | false => source
  | true => revisionCurrent source original

variable {rank : Ordinal.{0}}
local notation "M" => MotherArenaHigher.Material rank

/-- Both complete roots and all body values are bound to one packed source
material. Original fields occur as inverse type schemas and coverage targets. -/
structure SourceOrigin where
  familyMaterial : M
  bodyMaterial : M
  indices : Bool ≃ MotherCurrentFamilies.Member familyMaterial
  oldCurrent : MotherNativeCurrent.Restriction rank source
    (MotherCurrentFamilies.atMember familyMaterial (indices false))
  newCurrent : MotherNativeCurrent.Restriction rank (revisionCurrent source original)
    (MotherCurrentFamilies.atMember familyMaterial (indices true))
  formed : formOnHeader (readHeader newCurrent) (readHeader_eq newCurrent)
    (currentCoordinates oldCurrent) (currentOccurrence oldCurrent rooted.oldSuccessor.next)
    ⟨currentCoordinates newCurrent, currentOccurrence newCurrent
      original.generate.newLivingRoot.toAuthoritativeRoot.toRoot.source.initial⟩ bodyMaterial = some original

variable {source original}

def SourceOrigin.material (origin : SourceOrigin source original (rank := rank)) : M :=
  MotherArenaHigher.pack rank (origin.familyMaterial, origin.bodyMaterial)

theorem SourceOrigin.material_components (origin : SourceOrigin source original (rank := rank)) :
    MotherArenaHigher.split rank origin.material = (origin.familyMaterial, origin.bodyMaterial) :=
  MotherArenaHigher.split_pack rank _

def SourceOrigin.read (origin : SourceOrigin source original (rank := rank)) :
    FieldGroundedTypedSemanticWorldNetworkRevisionAt rooted :=
  (formOnHeader (readHeader origin.newCurrent) (readHeader_eq origin.newCurrent)
    (currentCoordinates origin.oldCurrent) (currentOccurrence origin.oldCurrent rooted.oldSuccessor.next)
    ⟨currentCoordinates origin.newCurrent, currentOccurrence origin.newCurrent
      original.generate.newLivingRoot.toAuthoritativeRoot.toRoot.source.initial⟩ origin.bodyMaterial).get
      (by rw [origin.formed]; rfl)

theorem SourceOrigin.read_eq (origin : SourceOrigin source original (rank := rank)) : origin.read = original :=
  Option.some.inj ((Option.some_get _).trans origin.formed)

variable (source original)
/-- Public full U8 material coverage: one sufficient rank, complete old and
revised living sources, every revised value and all original generated rows.
No address or restored-header condition is requested from the caller. -/
theorem every_revision_source :
    ∃ rank : Ordinal.{0}, ∃ material : MotherArenaHigher.Material rank,
      ∃ origin : SourceOrigin source original (rank := rank),
        origin.material = material ∧ origin.read = original ∧
        ∃ originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank,
          Function.LeftInverse (MotherArenaHigher.restrictOriginal rank originalAddress)
            (MotherArenaHigher.includeOriginal rank originalAddress) := by
  obtain ⟨rank, familyMaterial, indices, currents, originalAddress, originalRecovered⟩ :=
    MotherCurrentFamilies.every_current_family Bool (pairNetwork source original) (pairCurrent source original)
  obtain ⟨oldCurrent⟩ := (currents false).restriction
  obtain ⟨newCurrent⟩ := (currents true).restriction
  obtain ⟨bodyMaterial, formed⟩ := every_revision original
    (currentCoordinates oldCurrent) (currentCoordinates newCurrent)
    (currentOccurrence oldCurrent rooted.oldSuccessor.next)
    (currentOccurrence newCurrent original.generate.newLivingRoot.toAuthoritativeRoot.toRoot.source.initial)
  have onHeader : formOnHeader (readHeader newCurrent) (readHeader_eq newCurrent)
      (currentCoordinates oldCurrent) (currentOccurrence oldCurrent rooted.oldSuccessor.next)
      ⟨currentCoordinates newCurrent, currentOccurrence newCurrent
        original.generate.newLivingRoot.toAuthoritativeRoot.toRoot.source.initial⟩ bodyMaterial = some original := by
    erw [formOnHeader_eq]
    exact formed
  let origin : SourceOrigin source original (rank := rank) :=
    ⟨familyMaterial, bodyMaterial, indices, oldCurrent, newCurrent, onHeader⟩
  exact ⟨rank, origin.material, origin, rfl, origin.read_eq, originalAddress, originalRecovered⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherU8Revision
