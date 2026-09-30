import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.AdmittedWorld.Source
import H0mework.Foundation.Semantics.RootReality

/-! Original admission consumers execute on the actual recovered root and
complete visit. Their authority, history, whole ledger and original next
remain the existing root compiler's values. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAdmittedWorld
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot ZeroLawRootAdmission
noncomputable section
variable {N : WorldRelationNetwork.{0}}

private theorem consumers_of_eq {first last : StateAt N} (same : first = last) :
    HEq first.2.2.registeredOccurrence last.2.2.registeredOccurrence ∧
    HEq first.2.2.authoritativeEvolution last.2.2.authoritativeEvolution ∧
    HEq first.2.2.positiveDisposition last.2.2.positiveDisposition ∧
    HEq first.2.2.registeredOccurrence.2.priorPatches last.2.2.registeredOccurrence.2.priorPatches ∧
    HEq first.2.2.registeredOccurrence.2.currentPatch last.2.2.registeredOccurrence.2.currentPatch ∧
    HEq first.2.2.registeredOccurrence.2.wholeLedgerWriteBack last.2.2.registeredOccurrence.2.wholeLedgerWriteBack ∧
    HEq (first.2.1.toRoot.evolutionAt first.2.2.current).nextCurrent?
      (last.2.1.toRoot.evolutionAt last.2.2.current).nextCurrent? ∧
    HEq (advance first.2.1.toLedgerRoot first.2.2) (advance last.2.1.toLedgerRoot last.2.2) := by
  cases same
  exact ⟨HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

variable {original : StateAt N} (origin : Origin original)

theorem Origin.consumers_recovers :
    HEq origin.read.2.2.registeredOccurrence original.2.2.registeredOccurrence ∧
    HEq origin.read.2.2.authoritativeEvolution original.2.2.authoritativeEvolution ∧
    HEq origin.read.2.2.positiveDisposition original.2.2.positiveDisposition ∧
    HEq origin.read.2.2.registeredOccurrence.2.priorPatches original.2.2.registeredOccurrence.2.priorPatches ∧
    HEq origin.read.2.2.registeredOccurrence.2.currentPatch original.2.2.registeredOccurrence.2.currentPatch ∧
    HEq origin.read.2.2.registeredOccurrence.2.wholeLedgerWriteBack original.2.2.registeredOccurrence.2.wholeLedgerWriteBack ∧
    HEq (origin.read.2.1.toRoot.evolutionAt origin.read.2.2.current).nextCurrent?
      (original.2.1.toRoot.evolutionAt original.2.2.current).nextCurrent? ∧
    HEq (advance origin.read.2.1.toLedgerRoot origin.read.2.2)
      (advance original.2.1.toLedgerRoot original.2.2) :=
  consumers_of_eq origin.read_eq

/-- Positive total reality is consumed from the generated complete root;
it is not an additional admission premise or a replacement root law. -/
theorem Origin.totalReality : TotalReality.TotalRealityAt (RootTotalReality.semantics origin.read.2.1) :=
  RootTotalReality.isTotal origin.read.2.1

private theorem totality_of_eq {first last : StateAt N} (same : first = last) :
    HEq (RootTotalReality.isTotal first.2.1) (RootTotalReality.isTotal last.2.1) := by
  cases same
  rfl

theorem Origin.totalReality_recovers :
    HEq (RootTotalReality.isTotal origin.read.2.1) (RootTotalReality.isTotal original.2.1) :=
  totality_of_eq origin.read_eq

/-- The total public mouth ranges over the original authoritative root and
its original lawful state. LivingRoot/Handoff never enters this domain. -/
theorem every_admitted_world (N : WorldRelationNetwork.{0}) (V : ConstructiveRoot.Vocabulary.{0})
    (root : SourceNativeAuthoritativeRootClosure N V) (state : LawfulWorldStateAt root) :
    ∃ origin : Origin (⟨V, root, state⟩ : StateAt N),
      origin.world = ⟨N, V, root, state⟩ ∧
      HEq origin.read.2.2.registeredOccurrence state.registeredOccurrence ∧
      HEq origin.read.2.2.authoritativeEvolution state.authoritativeEvolution ∧
      HEq origin.read.2.2.positiveDisposition state.positiveDisposition ∧
      HEq origin.read.2.2.registeredOccurrence.2.wholeLedgerWriteBack state.registeredOccurrence.2.wholeLedgerWriteBack ∧
      HEq (origin.read.2.1.toRoot.evolutionAt origin.read.2.2.current).nextCurrent?
        (root.toRoot.evolutionAt state.current).nextCurrent? ∧
      TotalReality.TotalRealityAt (RootTotalReality.semantics origin.read.2.1) := by
  obtain ⟨origin⟩ := every_state N ⟨V, root, state⟩
  have readouts := origin.consumers_recovers
  exact ⟨origin, origin.world_eq, readouts.1, readouts.2.1, readouts.2.2.1,
    readouts.2.2.2.2.2.1, readouts.2.2.2.2.2.2.1, origin.totalReality⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAdmittedWorld
