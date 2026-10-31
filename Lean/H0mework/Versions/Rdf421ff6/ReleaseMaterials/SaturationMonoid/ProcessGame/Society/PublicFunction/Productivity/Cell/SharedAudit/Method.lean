import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Source

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit

open Institutions.Capitalism.Universal.Source.Program

/-- A reusable recipe still checks the receiving state's actual resources. -/
def seedWord (child : Party) : List RequestAt :=
  [transfer 0 0 child [(.seed, 1)],
    transfer 3 3 child [(.feed, if child = 1 then 17 else 16), (.energy, 4), (.labor, 4)]]

def AuditPayment (request : RequestAt) : Prop := match request.operation with
  | .use actor goods purpose => actor = 0 ∧ goods = [(.labor, 1)] ∧ purpose = .contribution
  | _ => False

instance (request : RequestAt) : Decidable (AuditPayment request) := by
  unfold AuditPayment
  cases request.operation <;> infer_instance

structure PaidMethod where
  private mk ::
  before : Current
  word : List RequestAt
  item : ExecutionItem Party Good Port Technology Unit
  schema : word = seedChild 1
  original : item ∈ law.rawItems before word
  accepted : law.Valid item.before item.request
  payment : AuditPayment item.request

def compile (current : Current) : Option PaidMethod :=
  if checked : current.round = 4 ∧ Cell.Ready current then
    let item : ExecutionItem Party Good Port Technology Unit := ⟨0, current, audit 0⟩
    some ⟨current, seedChild 1, item, rfl,
      by exact List.mem_cons_self,
      by
        have ready := checked.2
        unfold Cell.Ready at ready
        have word : Cell.candidate current = seedChild 1 := by simp [Cell.candidate, checked.1]
        rw [word] at ready
        exact ready item List.mem_cons_self,
      by exact ⟨rfl, rfl, rfl⟩⟩
  else none

theorem compile_origin (current : Current) (method : PaidMethod) (generated : compile current = some method) :
    method.before = current ∧ method.item = ⟨0, current, audit 0⟩ := by
  unfold compile at generated
  split at generated
  · cases generated
    exact ⟨rfl, rfl⟩
  · cases generated


theorem PaidMethod.actual_labor_payment (method : PaidMethod) :
    flowAt (law.actualDebit method.item.before method.item.request) 0 .labor = 1 := by
  have paid := method.payment
  rw [RawLaw.actualDebit, if_pos method.accepted]
  cases operation : method.item.request.operation with
  | use actor goods purpose =>
    simp only [AuditPayment, operation] at paid
    rcases paid with ⟨rfl, rfl, rfl⟩
    norm_num [RawLaw.debit, operation, locate, flowAt, amount]
  | _ => simp only [AuditPayment, operation] at paid

private def retarget (child : Party) (request : RequestAt) : RequestAt :=
  match request.operation with
  | .transfer sender recipient goods =>
    if recipient = 1 then
      { request with operation := (.transfer sender child
          (if sender = 3 then goods.map (fun item =>
            (item.1, if item.1 = .feed ∧ child ≠ 1 then item.2 - 1 else item.2)) else goods)) }
    else request
  | _ => request

/-- The new recipe is computed from the paid, actually audited programme. -/
def PaidMethod.plan (method : PaidMethod) (child : Party) : List RequestAt :=
  method.word.tail.map (retarget child)

theorem PaidMethod.plan_is_parameterized_original (method : PaidMethod) (child : Party) :
    method.plan child = seedWord child := by
  rw [PaidMethod.plan, method.schema]
  by_cases first : child = 1
  · subst child; rfl
  · simp [seedChild, seedWord, retarget, transfer, first]
    norm_num


def Ready (current : Current) (method : PaidMethod) : Prop :=
  ∀ item ∈ law.rawItems current (method.plan 2), law.Valid item.before item.request

instance (current : Current) (method : PaidMethod) : Decidable (Ready current method) := by unfold Ready; infer_instance

inductive Response (current : Current) where
  | reused (method : PaidMethod) (accepted : Ready current method)
  | blocked (method : PaidMethod) (refused : ¬ Ready current method)
  | fresh (original : Feedback.Outcome current)

def respond (current : Current) (method : Option PaidMethod) : Response current :=
  if current.round = 7 then match method with
    | some paid => if accepted : Ready current paid then .reused paid accepted else .blocked paid accepted
    | none => .fresh (Feedback.respond current)
  else .fresh (Feedback.respond current)

def Response.word {current : Current} : Response current → List RequestAt
  | .reused method _ => method.plan 2
  | .blocked _ _ => []
  | .fresh original => original.word

structure Frame where
  raw : Current
  method : Option PaidMethod

def wordAt (ordinal : Nat) (frame : Frame) : List RequestAt :=
  if ordinal = 0 then [] else if ordinal = 1 then original
  else (respond frame.raw frame.method).word

def advance (ordinal : Nat) (frame : Frame) : Frame where
  raw := law.next frame.raw (wordAt ordinal frame)
  method := frame.method.orElse (fun _ => compile frame.raw)

def frameAt : Nat → Frame
  | 0 => ⟨initial, none⟩
  | ordinal + 1 => advance ordinal (frameAt ordinal)

theorem machine_round (ordinal : Nat) : (frameAt ordinal).raw.round = ordinal := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih =>
    change (frameAt ordinal).raw.round + 1 = ordinal + 1
    rw [ih]

theorem method_is_kept (ordinal : Nat) (method : PaidMethod) (paid : (frameAt ordinal).method = some method) :
    (frameAt (ordinal + 1)).method = some method := by
  change ((frameAt ordinal).method.orElse _ = _)
  rw [paid]
  rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit
