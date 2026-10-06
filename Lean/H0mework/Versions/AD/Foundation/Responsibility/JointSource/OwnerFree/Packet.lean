import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.Runtime
import H0mework.Foundation.Responsibility.JointSource.Successor.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.OwnerFree
open SourceOperationEffects
namespace J
export RootGeneratedDebtActivationJointSource.Successor (read? Packet)
end J
private theorem successor_option_exists {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V} {current : V.Current}
    {occurrence : source.source.toRootSource.actual.OccurrenceAt current}
    (generated : SourceNativeLedgerEvolutionAt source.source occurrence)
    (successor : SourceNativeLedgerGeneratedSuccessorAt occurrence generated) :
    (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated? generated).isSome = true := by
  cases generated with
  | faithfulTerminal _ _ _ => exact nomatch successor
  | nativeWrite => rfl
  | relationWrite => rfl
  | continuedTransport => rfl
  | borromeanRedirect => rfl

private theorem packet_exists {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (lower : SourceNativeLedgerRootClosure N V) (current : V.Current)
    (successor : SourceNativeLedgerGeneratedSuccessorAt (lower.emitted current) (lower.generatedLedgerAt current)) :
    (J.read? lower current).isSome = true := by
  have found := successor_option_exists (lower.generatedLedgerAt current) successor
  unfold RootGeneratedDebtActivationJointSource.Successor.read?
  cases selected : SourceNativeLedgerGeneratedSuccessorAt.ofGenerated? (lower.generatedLedgerAt current) with
  | none => simp only [selected,Option.isSome_none] at found; exact Bool.noConfusion found
  | some successor => rfl

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : SourceNativeAuthoritativeRootClosure N V) (origin : V.Current)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (reader : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin →
  Raw (Value:=Value) (Var:=Var) (sort:=sort))
def packetAt (current : Current old origin reader) :
    J.Packet (authoritativeRoot old origin reader).toLedgerRoot current :=
  (J.read? (authoritativeRoot old origin reader).toLedgerRoot current).get
    (packet_exists (authoritativeRoot old origin reader).toLedgerRoot current
      (sourceSuccessor old origin reader current))
end RootGeneratedDebtActivationJointSource.OwnerFree
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
