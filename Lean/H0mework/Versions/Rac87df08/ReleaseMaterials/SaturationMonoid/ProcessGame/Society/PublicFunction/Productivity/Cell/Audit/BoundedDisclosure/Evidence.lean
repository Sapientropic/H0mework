import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Domain

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.BoundedDisclosure
open Institutions.Capitalism.Universal.Source.Program

/-- This client checks the first original whole necessity slot, not other tasks. -/
def publicClaim : ServiceSlot Party Good := ⟨0,[(.life,1)],.necessity⟩

structure AdmissionSlice where
  slot : Nat
  ordinal : Nat
  deriving DecidableEq

/-- The request is the public claim's fixed `necessity 0`. Excess stock is not released. -/
structure PaymentSlice where
  visit : Nat
  row : Nat
  available : ℚ
  start : ℚ
  finish : ℚ
  deriving DecidableEq

inductive Field where
  | admission | payment
  deriving DecidableEq

structure Evidence where
  admission : Option AdmissionSlice
  payment : Option PaymentSlice
  deriving DecidableEq

def restrict (fields : List Field) (evidence : Evidence) : Evidence :=
  ⟨if .admission ∈ fields then evidence.admission else none,
   if .payment ∈ fields then evidence.payment else none⟩

inductive Verdict where
  | verified | insufficient
  deriving DecidableEq

def traceCheck (evidence : Evidence) : Verdict :=
  match evidence.admission, evidence.payment with
  | some admission, some payment =>
    if admission.slot = 0 ∧ admission.ordinal = 0 ∧ payment.visit = 1 ∧ payment.row = 2 ∧
        1 ≤ payment.available ∧ 1 ≤ payment.start ∧ payment.finish ≤ 12 then .verified else .insufficient
  | _, _ => .insufficient

inductive ReplayState where
  | absent | pending | fulfilled
  deriving DecidableEq

def admit (admission : Option AdmissionSlice) : ReplayState :=
  match admission with
  | some record => if record.ordinal = 0 ∧ record.slot = 0 then .pending else .absent
  | none => .absent

def review (state : ReplayState) (payment : Option PaymentSlice) : ReplayState :=
  match state, payment with
  | .pending, some record =>
    if record.finish ≤ 12 ∧ 1 ≤ record.start ∧ record.row = 2 ∧ record.visit = 1 ∧
        1 ≤ record.available then .fulfilled else .pending
  | _, _ => state

/-- The second client replays admission then review; it never calls the trace client. -/
def lifecycleCheck (evidence : Evidence) : Verdict :=
  if review (admit evidence.admission) evidence.payment = .fulfilled then .verified else .insufficient

def Sufficient (evidence : Evidence) : Prop :=
  ∃ admission payment, evidence.admission = some admission ∧ evidence.payment = some payment ∧
    admission.slot = 0 ∧ admission.ordinal = 0 ∧ payment.visit = 1 ∧ payment.row = 2 ∧
    1 ≤ payment.available ∧ 1 ≤ payment.start ∧ payment.finish ≤ 12

theorem trace_sound (evidence : Evidence) (accepted : traceCheck evidence = .verified) :
    Sufficient evidence := by
  rcases evidence with ⟨admission,payment⟩
  cases admission <;> cases payment <;> simp_all [traceCheck, Sufficient]

theorem lifecycle_sound (evidence : Evidence) (accepted : lifecycleCheck evidence = .verified) :
    Sufficient evidence := by
  rcases evidence with ⟨admission,payment⟩
  cases admission <;> cases payment <;>
    simp_all [lifecycleCheck, admit, review, Sufficient, and_comm, and_left_comm, and_assoc]
  all_goals split_ifs at * <;> simp_all

theorem missing_is_insufficient (evidence : Evidence) (missing : evidence.payment = none) :
    traceCheck evidence = .insufficient ∧ lifecycleCheck evidence = .insufficient := by
  rcases evidence with ⟨admission,payment⟩
  simp only at missing
  subst payment
  cases admission <;> simp [traceCheck, lifecycleCheck, admit, review]
  split <;> simp

theorem original_use_valid_iff (current : Current) :
    law.Valid current (necessity 0) ↔ 1 ≤ current.stock 0 .life := by
  simp [necessity, RawLaw.Valid, RawLaw.SignerMatches, RawLaw.operationAllowed,
    RawPolicy.eval, RawLaw.requiredPorts, RawLaw.debit, RawLaw.credit, RawLaw.ClaimGuard,
    law, NonnegativeBundle, locate, flowAt, amount]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.BoundedDisclosure
