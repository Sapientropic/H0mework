import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Payment.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Payment

open Capitalism.Universal Capitalism.Universal.Root Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition
open Financial.Installation.Admission (InjectiveLedger jointStep_injective wholeTransport_injective)
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld DebtActivationLedger

noncomputable section

private def jointWrite {Base : WorldRelationNetwork} {Law : DebtActivationLaw}
    {before after : Base.Support} {first last : Law.DebtState}
    (old : { evolution : LedgerWriteEvolutionAt Base ⟨before⟩ ⟨after⟩ // InjectiveLedger evolution })
    (owner : OpenResponsibilityAt Base before)
    (disposition : Law.StepAt first last ⊕ Law.TransportAt first last) :
    { evolution : LedgerWriteEvolutionAt (ExtendedNetwork Base Law) ⟨(before, some first)⟩
      ⟨(after, some last)⟩ // InjectiveLedger evolution } :=
  match disposition with
  | .inl paid => ⟨jointStepLedgerEvolution old.val owner paid,
      jointStep_injective old.val owner paid old.property⟩
  | .inr carried => ⟨Financial.Installation.wholeTransport old.val owner carried,
      wholeTransport_injective old.val owner carried old.property⟩

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]
  {source : Conflict.Root.Cut Party Good Port Technology Instrument}
  {attack : RawEvent Party Good Port Technology Instrument}
  {community : Party → Community} {key : Key Party Good}
  (claim : ClaimAt source attack community key)
  (repair : Request Party Good Port Technology Instrument)
  (paid : Conflict.Root.Paid source (attack ++ [repair]))

abbrev Local := (frame claim repair).V.Current
abbrev Cursor := Option (Local claim repair)

def oldAt : Cursor claim repair → Local claim repair
  | none => start claim repair
  | some current => current

def debtAt : Cursor claim repair → Birth.Stage source attack
  | none => Birth.opening claim
  | some _ => stage repair paid

def support (current : Cursor claim repair) : (Birth.N claim).Support :=
  ((frame claim repair).sourceSupport (oldAt claim repair current), some (debtAt claim repair paid current))

def next (current : Cursor claim repair) : Cursor claim repair :=
  some ((frame claim repair).successor (oldAt claim repair current)).targetCurrent

private def oldWrite (current : Local claim repair) :
    {evolution : LedgerWriteEvolutionAt (frame claim repair).N
      ⟨(frame claim repair).sourceSupport current⟩
      ⟨(frame claim repair).sourceSupport ((frame claim repair).successor current).targetCurrent⟩ //
        InjectiveLedger evolution} := by
  let base := frame claim repair
  let step := base.successor current
  have kept := base.successor_keys current
  have injective : InjectiveLedger step.ledgerEvolution :=
    ⟨Financial.Installation.keys_imply_origin_injective _ kept base.family.open_fibres,
      Financial.Installation.keys_imply_destination_injective _ kept base.family.open_fibres⟩
  have same := congrArg (fun event => base.root.toAuthoritativeRoot.toLedgerRoot.source.source
    |>.toRootSource.account.supportOf event) (base.target_occurrence current)
  change base.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
    step.targetOccurrence = base.sourceSupport step.targetCurrent at same
  exact same ▸ ⟨step.ledgerEvolution, injective⟩

/-- Closing and partial payment are both compiled from the same actual
accepted original receipt. A nonzero residual remains in the same row. -/
def disposition :
    (Birth.law claim).StepAt (Birth.opening claim) (stage repair paid) ⊕
      (Birth.law claim).TransportAt (Birth.opening claim) (stage repair paid) :=
  if zero : remaining source attack [repair] community key = 0 then
    .inl (Birth.Step.pay (claim := claim) (front := [])
      (by simpa only [List.append_nil] using claim.paid) [repair] paid
      (by rw [initial_remaining_is_the_original_amount claim]; exact claim.positive) zero)
  else .inr (Birth.Carry.continued (front := [])
    (by simpa only [List.append_nil] using claim.paid) [repair] paid)

set_option maxHeartbeats 800000 in
def write (current : Cursor claim repair) :
    {evolution : LedgerWriteEvolutionAt (Birth.N claim) ⟨support claim repair paid current⟩
      ⟨support claim repair paid (next claim repair current)⟩ // InjectiveLedger evolution} := by
  cases current with
  | none =>
    exact jointWrite (oldWrite claim repair (start claim repair))
      ((frame claim repair).entry (start claim repair)) (disposition claim repair paid)
  | some state =>
    let waiting : (Birth.law claim).TransportAt (stage repair paid) (stage repair paid) := .waiting _
    exact jointWrite (oldWrite claim repair state) ((frame claim repair).entry state) (.inr waiting)

def flow : Accounting.Root.Compiler.Flow (Birth.N claim) where
  Current := Cursor claim repair
  initial := none
  support := support claim repair paid
  next := next claim repair
  writes := fun current => match (frame claim repair).root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
      (oldAt claim repair current) with
    | .nativeWrite .. | .relationWrite .. => true
    | _ => false
  evolution := fun current => (write claim repair paid current).val
  finite := fun current => Abolition.Root.Epoch.Finance.Future.Finiteness.active_finite _
    ((frame claim repair).entries_finite (oldAt claim repair current))
  injective := fun current => (write claim repair paid current).property
  open_fibres := Birth.open_fibres claim

def root := Accounting.Root.Compiler.livingRoot (flow claim repair paid)

theorem payment_starts_at_the_already_filed_support :
    support claim repair paid none = Birth.support claim (Birth.next claim .pending) := by
  change ((frame claim repair).sourceSupport (start claim repair), some (Birth.opening claim)) =
    ((Birth.originalFrame claim).sourceSupport
      ((Birth.originalFrame claim).successor (Birth.originalVisit claim).current).targetCurrent,
        some (Birth.opening claim))
  rw [recorded_body_starts_from_the_original_support, original_support_survives_filing claim repair paid]
  rfl

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Payment
