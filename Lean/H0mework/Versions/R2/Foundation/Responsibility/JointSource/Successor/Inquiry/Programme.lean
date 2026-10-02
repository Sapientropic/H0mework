import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Successor.Restructuring.Authority

/-! The installed source compiles its own complete continuing receipt at every
current. Its next programme is derived from that compiler, including remainders. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Successor.Inquiry
open SourceOperationEffects CompilerFromPacketSourceLaw

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : SourceNativeAuthoritativeRootClosure N V)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable {origin : V.Current}
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort) old.toLedgerRoot origin)
variable (packetAt : (current : V.Current) → Packet old.toLedgerRoot current)

def nextProgramme (current : Current registered) :
    Packet (Restructuring.authoritativeRoot old registered packetAt).toLedgerRoot current :=
  (read? (Restructuring.authoritativeRoot old registered packetAt).toLedgerRoot current).get (by rfl)

theorem programme_generated (current : Current registered) :
    (nextProgramme old registered packetAt current).generated =
      (compiler registered packetAt).compile (emitted registered packetAt current) := rfl

theorem programme_target (current : Current registered) :
    (nextProgramme old registered packetAt current).targetCurrent = targetCurrent registered packetAt current := rfl

theorem programme_occurrence (current : Current registered) :
    (nextProgramme old registered packetAt current).targetOccurrence = targetOccurrence registered packetAt current := rfl

theorem programme_whole (current : Current registered) :
    (nextProgramme old registered packetAt current).ledgerEvolution = whole registered packetAt current :=
  patch_fold registered packetAt current

theorem programme_patch (current : Current registered) :
    (nextProgramme old registered packetAt current).originalPatch =
      (compiler registered packetAt).compilePatch (emitted registered packetAt current) := rfl

end RootGeneratedDebtActivationJointSource.Successor.Inquiry
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
