import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.BoundedDisclosure.Evidence
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped
open Institutions.Capitalism.Universal.Source.Program

abbrev Slot := Fin 6
abbrev Verdict := BoundedDisclosure.Verdict
abbrev Field := BoundedDisclosure.Field

def bearer (slot : Slot) : Party := slot.val / 2
def good (slot : Slot) : Good := if slot.val % 2 = 0 then .life else .spare
def useKind (slot : Slot) : Use := if slot.val % 2 = 0 then .necessity else .maintenance
def claim (slot : Slot) : ServiceSlot Party Good := ⟨bearer slot,[(good slot,1)],useKind slot⟩
def serviceRequest (slot : Slot) : RequestAt :=
  ⟨bearer slot,[],.common,[],.use (bearer slot) [(good slot,1)] (useKind slot)⟩

structure Admission where
  slot : Nat
  ordinal : Nat
  deriving DecidableEq

structure Payment where
  slot : Nat
  visit : Nat
  row : Nat
  available : ℚ
  start : ℚ
  finish : ℚ
  deriving DecidableEq

structure Evidence where
  admission : Option Admission
  payment : Option Payment
  deriving DecidableEq

/-- Two bounded masks are the primitive public query, never a result or a grant. -/
structure Query where
  slots : Fin 64
  fields : Fin 4
  deriving DecidableEq

def selected (query : Query) : List Slot :=
  (List.finRange 6).filter fun slot => query.slots.val / 2 ^ slot.val % 2 = 1

def fields (query : Query) : List Field :=
  (if query.fields.val % 2 = 1 then [.admission] else []) ++
    (if query.fields.val / 2 = 1 then [.payment] else [])

def restrict (allowed : List Field) (evidence : Evidence) : Evidence :=
  ⟨if .admission ∈ allowed then evidence.admission else none,
   if .payment ∈ allowed then evidence.payment else none⟩

def traceCheck (slot : Slot) (evidence : Evidence) : Verdict :=
  match evidence.payment with
  | none => .insufficient
  | some payment =>
    if payment.slot = slot.val ∧ payment.visit = 1 ∧ payment.row = slot.val + 2 ∧
        1 ≤ payment.available ∧ 1 ≤ payment.start ∧ payment.finish ≤ 12 then .verified else .insufficient

inductive ReplayState where
  | absent | pending | fulfilled
  deriving DecidableEq

def admit (slot : Slot) (admission : Option Admission) : ReplayState :=
  match admission with
  | none => .absent
  | some record => if record.ordinal = 0 ∧ record.slot = slot.val then .pending else .absent

def review (slot : Slot) (state : ReplayState) (payment : Option Payment) : ReplayState :=
  match state, payment with
  | .pending, some record =>
    if record.finish ≤ 12 ∧ 1 ≤ record.start ∧ 1 ≤ record.available ∧
        record.row = slot.val + 2 ∧ record.visit = 1 ∧ record.slot = slot.val then .fulfilled else .pending
  | _, _ => state

def lifecycleCheck (slot : Slot) (evidence : Evidence) : Verdict :=
  if review slot (admit slot evidence.admission) evidence.payment = .fulfilled then .verified else .insufficient

def PaymentChecked (slot : Slot) (evidence : Evidence) : Prop :=
  ∃ payment, evidence.payment = some payment ∧ payment.slot = slot.val ∧ payment.visit = 1 ∧
    payment.row = slot.val + 2 ∧ 1 ≤ payment.available ∧ 1 ≤ payment.start ∧ payment.finish ≤ 12

theorem trace_sound (slot : Slot) (evidence : Evidence) (accepted : traceCheck slot evidence = .verified) :
    PaymentChecked slot evidence := by
  rcases evidence with ⟨admission,payment⟩
  cases payment <;> simp_all [traceCheck,PaymentChecked]

theorem lifecycle_sound (slot : Slot) (evidence : Evidence) (accepted : lifecycleCheck slot evidence = .verified) :
    (∃ admission, evidence.admission = some admission ∧ admission.ordinal = 0 ∧ admission.slot = slot.val) ∧
    PaymentChecked slot evidence := by
  rcases evidence with ⟨admission,payment⟩
  cases admission <;> cases payment <;>
    simp_all [lifecycleCheck,admit,review,PaymentChecked,and_comm,and_left_comm,and_assoc]
  all_goals split_ifs at * <;> simp_all

theorem missing_payment_stops_both (slot : Slot) (evidence : Evidence) (missing : evidence.payment = none) :
    traceCheck slot evidence = .insufficient ∧ lifecycleCheck slot evidence = .insufficient := by
  rcases evidence with ⟨admission,payment⟩
  simp only at missing
  subst payment
  cases admission <;> simp [traceCheck,lifecycleCheck,admit,review]
  split <;> simp

theorem service_valid_iff (slot : Slot) (current : Current) :
    law.Valid current (serviceRequest slot) ↔ 1 ≤ current.stock (bearer slot) (good slot) := by
  rcases slot with ⟨slot,bound⟩
  interval_cases slot <;>
    simp [serviceRequest,bearer,good,useKind,RawLaw.Valid,RawLaw.SignerMatches,RawLaw.operationAllowed,
      RawPolicy.eval,RawLaw.requiredPorts,RawLaw.debit,RawLaw.credit,RawLaw.ClaimGuard,
      law,NonnegativeBundle,locate,flowAt,amount]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped
