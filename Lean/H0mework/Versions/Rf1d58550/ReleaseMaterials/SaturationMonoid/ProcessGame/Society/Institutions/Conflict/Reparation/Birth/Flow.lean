import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Birth.Law
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Compiler.Living
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission.Injective
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Finiteness
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Structure

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Birth

open Capitalism.Universal.Source.Program
open Capitalism.Universal
open Capitalism.Universal.Root
open Financial.Installation.Admission (InjectiveLedger jointStep_injective wholeTransport_injective)
open Capitalism.Universal.Abolition
open Capitalism.Universal.Abolition.Root.Registered.Macro
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld DebtActivationLedger

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]

variable {source : Root.Cut Party Good Port Technology Instrument}
  {attack : RawEvent Party Good Port Technology Instrument}
  {community : Party → Community} {key : Key Party Good}
  (claim : ClaimAt source attack community key)

abbrev attacked (_claim : ClaimAt source attack community key) := Root.terminal source attack
abbrev originalFrame := (attacked claim).native.frame
abbrev Original := (originalFrame claim).V.Current
abbrev N := ExtendedNetwork (originalFrame claim).N (law claim)

theorem original_target_support (current : Original claim) :
    (originalFrame claim).root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
      ((originalFrame claim).successor current).targetOccurrence =
    (originalFrame claim).sourceSupport ((originalFrame claim).successor current).targetCurrent := by
  let frame := originalFrame claim
  exact congrArg (fun event => frame.root.toAuthoritativeRoot.toLedgerRoot.source.source
    |>.toRootSource.account.supportOf event) (frame.target_occurrence current)

/-- Keep the original next visit, original open support and original whole
write while making the born debt an active coordinate. -/
def oldWrite (current : Original claim) :
    {evolution : LedgerWriteEvolutionAt (originalFrame claim).N
      ⟨(originalFrame claim).sourceSupport current⟩
      ⟨(originalFrame claim).sourceSupport ((originalFrame claim).successor current).targetCurrent⟩ //
        Financial.Installation.KeepsKeys evolution} := by
  let frame := originalFrame claim
  have kept : Financial.Installation.KeepsKeys (frame.successor current).ledgerEvolution :=
    frame.successor_keys current
  exact original_target_support claim current ▸ ⟨(frame.successor current).ledgerEvolution, kept⟩

inductive Cursor (_claim : ClaimAt source attack community key)
  | pending
  | live (old : Original _claim)

def originalAt : Cursor claim → Original claim
  | .pending => (attacked claim).native.visit.current
  | .live old => old

def debtAt : Cursor claim → Stage source attack
  | .pending => .unfiled
  | .live _ => opening claim

def support (current : Cursor claim) : (N claim).Support :=
  ((originalFrame claim).sourceSupport (originalAt claim current), some (debtAt claim current))

def next (current : Cursor claim) : Cursor claim :=
  .live ((originalFrame claim).successor (originalAt claim current)).targetCurrent

private theorem old_injective (current : Original claim) : InjectiveLedger (oldWrite claim current).val :=
  ⟨Financial.Installation.keys_imply_origin_injective _ (oldWrite claim current).property
      (originalFrame claim).family.open_fibres,
    Financial.Installation.keys_imply_destination_injective _ (oldWrite claim current).property
      (originalFrame claim).family.open_fibres⟩

def write (current : Cursor claim) :
    {evolution : LedgerWriteEvolutionAt (N claim) ⟨support claim current⟩ ⟨support claim (next claim current)⟩ //
      InjectiveLedger evolution} := by
  cases current with
  | pending =>
      let old := oldWrite claim (originalAt claim .pending)
      let owner := (originalFrame claim).entry (originalAt claim .pending)
      exact ⟨jointStepLedgerEvolution old.val owner (filing claim).step,
        jointStep_injective old.val owner (filing claim).step (old_injective claim _)⟩
  | live current =>
      let old := oldWrite claim current
      let owner := (originalFrame claim).entry current
      let waiting : (law claim).TransportAt (opening claim) (opening claim) := .waiting _
      exact ⟨Financial.Installation.wholeTransport old.val owner waiting,
        wholeTransport_injective old.val owner waiting (old_injective claim _)⟩

theorem open_fibres (current : (N claim).Support) (row : (N claim).Responsibility) :
    Subsingleton ((N claim).OpenAt current row) :=
  Abolition.Root.Epoch.Finance.Future.Structure.extended_subsingleton (law claim)
    (originalFrame claim).family.open_fibres current row

private def writes : Cursor claim → Bool
  | .pending => true
  | .live current =>
    match (originalFrame claim).root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current with
    | .nativeWrite .. | .relationWrite .. => true
    | _ => false

def flow : Accounting.Root.Compiler.Flow (N claim) where
  Current := Cursor claim
  initial := .pending
  support := support claim
  next := next claim
  writes := writes claim
  evolution := fun current => (write claim current).val
  finite := fun current => Abolition.Root.Epoch.Finance.Future.Finiteness.active_finite _
    ((originalFrame claim).entries_finite (originalAt claim current))
  injective := fun current => (write claim current).property
  open_fibres := open_fibres claim

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Birth
