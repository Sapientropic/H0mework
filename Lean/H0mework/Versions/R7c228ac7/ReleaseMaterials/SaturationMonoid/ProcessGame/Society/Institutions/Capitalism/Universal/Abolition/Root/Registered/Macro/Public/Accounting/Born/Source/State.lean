import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Ledger
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Source.Law
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.NativeEvolution

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Source

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld DebtActivationLedger
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit : Nat}
  {oldPast : List (Compile.RawInput Party Good Port Technology Instrument)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  {world : WorldRelationNetwork} {anchor : (Epoch.Finance.process input depth count).GeneratedState}
  (prior : Epoch.Finance.Future.Continuation.AccountFamily input depth count world anchor)
  (origin : Accounting.Current input depth count anchor)
  (registered : Registration input depth count prefixLimit renewalLimit oldPast start origin)

abbrev State := Option (Accounting.Current input depth count registered.admitted)

def supportAt : State origin registered → (Born.N prior origin registered).Support
  | none => initialSupport prior origin registered
  | some current => Accounting.support input depth count (family prior origin registered) current

def next : State origin registered → State origin registered
  | none => some (nextCurrent origin registered)
  | some current => some (Accounting.nativeNext input depth count prefixLimit renewalLimit oldPast start current)

def writes : State origin registered → Bool
  | none => true
  | some current => Public.Source.writes input depth count prefixLimit renewalLimit oldPast start current

def wholeEvolution (current : State origin registered) :
    LedgerWriteEvolutionAt (Born.N prior origin registered) ⟨supportAt prior origin registered current⟩
      ⟨supportAt prior origin registered (next origin registered current)⟩ :=
  match current with
  | none => firstWrite prior origin registered
  | some current => Accounting.nativeEvolution input depth count prefixLimit renewalLimit oldPast start
      (family prior origin registered) current

theorem whole_keys (current : State origin registered) :
    Financial.Installation.KeepsKeys (wholeEvolution prior origin registered current) := by
  cases current with
  | none => exact firstWrite_keys prior origin registered
  | some current =>
    exact (Accounting.nativeEvolutionWithKeys
      input depth count prefixLimit renewalLimit oldPast start (family prior origin registered) current).property

theorem entry_finite (current : State origin registered) :
    Finite (OpenResponsibilityAt (Born.N prior origin registered) (supportAt prior origin registered current)) := by
  cases current with
  | none =>
    exact Epoch.Finance.Future.Finiteness.active_finite _
      (prior.entries_finite origin.account origin.native)
  | some current => exact (family prior origin registered).entries_finite current.account current.native

def owner : (current : State origin registered) →
    OpenResponsibilityAt (Born.N prior origin registered) (supportAt prior origin registered current)
  | none => oldEntry (law := Born.law origin registered) (state? := some .pending) (Accounting.owner input depth count prior origin)
  | some current => Accounting.owner input depth count (family prior origin registered) current

def account : State origin registered → (Epoch.Finance.process input depth count).GeneratedState
  | none => origin.account
  | some current => current.account

def position : State origin registered → Nat
  | none => origin.position
  | some current => current.position

def physical : State origin registered → Actual.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)
  | none => Accounting.physical input depth count prefixLimit renewalLimit oldPast start origin
  | some current => Accounting.physical input depth count prefixLimit renewalLimit oldPast start current

theorem first_current_is_the_literal_consumed_head :
    next origin registered none = some registered.next := rfl

theorem every_later_current_uses_the_original_public_next (current : Accounting.Current input depth count registered.admitted) :
    next origin registered (some current) =
      some (Accounting.nativeNext input depth count prefixLimit renewalLimit oldPast start current) := rfl

#print axioms wholeEvolution
#print axioms whole_keys
#print axioms entry_finite

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Source
