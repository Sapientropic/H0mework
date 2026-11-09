import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Renewal.Material

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Renewal

open Capitalism.Universal.Source.Program
open PublicFunction.Mandate

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

local notation "Item" => ExecutionItem Party Good Port (State Party Technology) Instrument

variable (base : RawLaw Party Good Port Technology Instrument)
  (scope : Scope (Party := Party) (Good := Good) (Port := Port))

/-- The command is recognized at the original material item, with the original
signer, current, and cost guard. -/
structure PaidCommand (item : Item) (command : Command Party) : Prop where
  request_eq : item.request = request scope item.before item.request.signer command
  valid : (law base scope).Valid item.before item.request

variable {base scope}

omit [DecidableEq Instrument] in
theorem PaidCommand.canRun {item : Item} {command : Command Party}
    (paid : PaidCommand base scope item command) : CanRun scope item.before item.request.signer command := by
  have admitted := paid.valid.1.2
  rw [paid.request_eq] at admitted
  exact (command_policy base scope item.before item.request.signer command).mp admitted

theorem PaidCommand.after {item : Item} {command : Command Party}
    (paid : PaidCommand base scope item command) :
    ((law base scope).step item.before item.request).technology = advance scope item.before command := by
  have accepted := paid.valid
  rw [paid.request_eq] at accepted ⊢
  exact (paid_command_effect base scope item.before item.request.signer command accepted).1

omit [DecidableEq Instrument] in
theorem PaidCommand.fee {item : Item} {command : Command Party}
    (paid : PaidCommand base scope item command) :
    (PublicFunction.physicalLaw (law base scope)).actualDebit item.before item.request =
      locate item.request.signer scope.revisionCost := by
  simp only [RawLaw.actualDebit, if_pos (PublicFunction.valid_physical _ _ _ paid.valid)]
  rw [paid.request_eq]
  rfl

theorem PaidCommand.stock {item : Item} {command : Command Party}
    (paid : PaidCommand base scope item command) (party : Party) (good : Good) :
    ((PublicFunction.physicalLaw (law base scope)).step item.before item.request).stock party good =
      item.before.stock party good - flowAt (locate item.request.signer scope.revisionCost) party good := by
  simp only [RawLaw.step, if_pos (PublicFunction.valid_physical _ _ _ paid.valid), RawLaw.paidStep]
  rw [paid.request_eq]
  change item.before.stock party good - flowAt (locate item.request.signer scope.revisionCost) party good +
    flowAt [] party good = _
  simp [flowAt, amount, request]

variable (base scope)

/-- Every authorized material item either leaves the full mandate state
unchanged or is the original source command signed against that item. -/
theorem classify_material_item (item : Item) (licensed : (law base scope).Valid item.before item.request) :
    ((law base scope).step item.before item.request).technology = item.before.technology ∨
      ∃ command, PaidCommand base scope item command := by
  cases operation : item.request.operation with
  | revise operator target =>
    right
    have policy := licensed.1.2
    cases marked : target.last with
    | none => simp [law, RawLaw.operationAllowed, RawPolicy.eval, operation, marked] at policy
    | some command =>
      simp only [law, RawLaw.operationAllowed, RawPolicy.eval, operation, marked, decide_eq_true_eq] at policy
      obtain ⟨sameSigner, consents, purpose, gates, result, _⟩ := policy
      refine ⟨command, ⟨?_, licensed⟩⟩
      calc
        item.request = ⟨item.request.signer, item.request.consents, item.request.purpose,
            item.request.gates, item.request.operation⟩ := by cases item.request; rfl
        _ = request scope item.before item.request.signer command := by
          rw [consents, purpose, gates, operation, sameSigner, result]
          rfl
  | _ => left; simp only [RawLaw.step, if_pos licensed, RawLaw.paidStep, operation]

theorem MaterialTrace.same_technology {start final : State Party Technology} {items : List Item}
    (trace : MaterialTrace base scope start items final) : final.technology = start.technology := by
  induction trace with
  | nil => rfl
  | @cons current final item tail same licensed rest kept =>
    rw [kept, ← same]
    rcases classify_material_item base scope item licensed with unchanged | ⟨command, paid⟩
    · rw [unchanged]
    · rw [paid.after]
      cases command <;> simp [advance]
      split <;> rfl

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Renewal
