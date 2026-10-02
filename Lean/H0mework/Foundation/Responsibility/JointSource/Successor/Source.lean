import H0mework.Foundation.Responsibility.JointSource.Source

/-! Continuing updates are read from the original whole source compiler.
Their complete branch payload and finite/remainder patch remain source-owned. -/

set_option autoImplicit false
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Successor

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}

structure Packet (lower : SourceNativeLedgerRootClosure N V) (current : V.Current) : Type u where
  private mk ::
  successor : SourceNativeLedgerGeneratedSuccessorAt (lower.emitted current)
    (lower.generatedLedgerAt current)

variable {lower : SourceNativeLedgerRootClosure N V} {current : V.Current}

def read? (lower : SourceNativeLedgerRootClosure N V) (current : V.Current) : Option (Packet lower current) :=
  match SourceNativeLedgerGeneratedSuccessorAt.ofGenerated? (lower.generatedLedgerAt current) with
  | none => none
  | some successor => some ⟨successor⟩

namespace Packet
variable (packet : Packet lower current)

abbrev occurrence (_packet : Packet lower current) := lower.emitted current
abbrev generated (_packet : Packet lower current) := lower.generatedLedgerAt current

def targetCurrent : V.Current := packet.successor.targetCurrent
def targetOccurrence := packet.successor.targetOccurrence
def ledgerEvolution := packet.successor.ledgerEvolution
def originalPatch (_packet : Packet lower current) := lower.generatedPatchAt current

private theorem target_of_commutes
    {source : SourceNativeSource N V}
    (emitted : (current : V.Current) → source.toRootSource.actual.OccurrenceAt current)
    {current : V.Current} {occurrence : source.toRootSource.actual.OccurrenceAt current}
    {generated : SourceNativeLedgerEvolutionAt source occurrence}
    (successor : SourceNativeLedgerGeneratedSuccessorAt occurrence generated)
    (commutes : generated.CommutesWith emitted) :
    successor.targetOccurrence = emitted successor.targetCurrent := by
  cases generated with
  | nativeWrite => exact commutes
  | relationWrite => exact commutes
  | continuedTransport => exact commutes
  | borromeanRedirect => exact commutes
  | faithfulTerminal => exact nomatch successor

theorem target_emitted : packet.targetOccurrence = lower.emitted packet.targetCurrent :=
  target_of_commutes lower.emitted packet.successor (lower.compiler_commutes current)

theorem actual_next : (lower.source.source.toRootSource.actual.compile (lower.emitted current)).nextCurrent? =
    some packet.targetCurrent := packet.successor.next_eq

end Packet
end RootGeneratedDebtActivationJointSource.Successor
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
