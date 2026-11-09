import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport.Visit

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld DebtActivationLedger

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]
  {source : Root.Cut Party Good Port Technology Instrument}
  {attack : RawEvent Party Good Port Technology Instrument}
  {community : Party → Community} {key : Key Party Good}
  (claim : ClaimAt source attack community key)

abbrev initialShape := Shape.install (Birth.originalFrame claim).N (Birth.law claim)

private theorem opening_support :
    ((History.filed claim).targetRoot.emitted (History.filedVisit claim).current).1 =
      (initialShape claim).support (sourceSupport (Birth.attacked claim).native) (Birth.opening claim) := by
  change Birth.support claim (History.filedVisit claim).current = _
  rw [show (History.filedVisit claim).current = Birth.next claim .pending from
    Compiler.successor_current (Birth.flow claim) .pending]
  exact congrArg (fun prior => (prior, some (Birth.opening claim)))
    (History.filing_preserves_the_original_ready_support claim)

private theorem openedEntry_on_same_support {N : WorldRelationNetwork} {law : DebtActivationLaw}
    {left right : N.Support} (stage : law.DebtState) (same : left = right) :
    HEq (debtEntry (N := N) left stage) (debtEntry (N := N) right stage) := by
  cases same
  rfl

private theorem opening_entry :
    HEq (History.filedOwner claim)
      ((initialShape claim).repair (sourceSupport (Birth.attacked claim).native) (Birth.opening claim)) := by
  let filed := History.filed claim
  let flow := Birth.flow claim
  have canonical := Compiler.canonical_destination_heq filed.targetRoot.toAuthoritativeRoot.toLedgerRoot
    _ _ filed.firstSuccessor.next_eq filed.firstSuccessor filed.bornEntry
  have actual := destination_congr rfl (Compiler.successor_support flow .pending)
    filed.firstSuccessor.ledgerEvolution (Birth.write claim .pending).val
    (Compiler.successor_destination flow .pending) filed.bornEntry filed.bornEntry HEq.rfl
  exact canonical.trans (actual.trans (openedEntry_on_same_support (law := Birth.law claim) (Birth.opening claim)
    (History.filing_preserves_the_original_ready_support claim)))

/-- The seed is the already filed visit and its born authority. -/
def openResident :
    Resident (native := (Birth.attacked claim).native) (initialShape claim) (Birth.opening claim)
      (Birth.Carry.waiting _) where
  V := (History.filed claim).TargetV
  root := (History.filed claim).targetRoot
  visit := History.filedVisit claim
  unique := Compiler.occurrence_eq_emitted (Birth.flow claim)
  support_eq := opening_support claim
  entry := History.filedOwner claim
  repair_eq := opening_entry claim
  authority := History.filedAuthority claim
  structural := fun work => (History.original_attack_is_ready claim work).elim

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport
