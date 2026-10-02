import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.AuthorityFamilies.Coverage
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaReceipts.Sections
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeRegistry.Factory
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeRegistryRecovery.Process

/-! Operations on a previously formed whole node family. State identity is
its complete material index, including answered and repeated node values.
No erasure or generated-next value is inverted to choose a successor index. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherMacroOperations
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open scoped Classical
noncomputable section
variable {rank : Ordinal.{0}}

abbrev State (domain : MotherArenaHigher.Material rank) := MotherAuthorityFamilies.Member domain
abbrev Nodes (domain : MotherArenaHigher.Material rank) := State domain → RootInquiryProcessNode.{0}
abbrev Event {domain : MotherArenaHigher.Material rank} (nodes : Nodes domain) := Σ state, (nodes state).Query

structure Fields {domain : MotherArenaHigher.Material rank} (nodes : Nodes domain) where
  initial : State domain
  next : (state : State domain) → (nodes state).Query → State domain

private def unitAddress (rank : Ordinal.{0}) : Unit ↪ MotherArenaHigher.Base rank :=
  ⟨fun _ => MotherArenaHigher.point rank (.inl ()), fun _ _ _ => Subsingleton.elim _ _⟩

def stateAddress (domain : MotherArenaHigher.Material rank) : State domain ↪ MotherArenaHigher.Base rank :=
  ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩

/-- This optional adapter preserves both the full state index and its exact
query fibre when node production already supplies per-fibre addresses. -/
def eventAddress {domain : MotherArenaHigher.Material rank} (nodes : Nodes domain)
    (query : (state : State domain) → (nodes state).Query ↪ MotherArenaHigher.Base rank) :
    Event nodes ↪ MotherArenaHigher.Base rank :=
  MotherArenaObligation.sigmaEmbedding (stateAddress domain) query

variable (domain : MotherArenaHigher.Material rank) (nodes : Nodes domain)
    (event : Event nodes ↪ MotherArenaHigher.Base rank)

def formFields (material : MotherArenaHigher.Material rank) : Option (Fields nodes) :=
  let parts := MotherArenaHigher.split rank material
  (MotherArenaReceipts.NativeSection.form (unitAddress rank) (fun _ => stateAddress domain) parts.1).bind (fun initial =>
  (MotherArenaReceipts.NativeSection.form event (fun _ => stateAddress domain) parts.2).map (fun next =>
    ⟨initial (), fun state query => next ⟨state, query⟩⟩))

theorem every_fields (original : Fields nodes) :
    ∃ material : MotherArenaHigher.Material rank, formFields domain nodes event material = some original := by
  obtain ⟨initialM, initialFormed⟩ := MotherArenaReceipts.NativeSection.every_section
    (unitAddress rank) (fun _ => stateAddress domain) (fun _ => original.initial)
  obtain ⟨nextM, nextFormed⟩ := MotherArenaReceipts.NativeSection.every_section event
    (fun _ => stateAddress domain) (fun point => original.next point.1 point.2)
  refine ⟨MotherArenaHigher.pack rank (initialM, nextM), ?_⟩
  simp only [formFields, MotherArenaHigher.split_pack, initialFormed, Option.bind_some, nextFormed, Option.map_some]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherMacroOperations
