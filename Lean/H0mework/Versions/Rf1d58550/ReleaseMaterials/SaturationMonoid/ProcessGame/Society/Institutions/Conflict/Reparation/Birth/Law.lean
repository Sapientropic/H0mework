import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.RecordedBalance
import H0mework.Realization.Audit.DebtFirstWrite

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Birth

open Capitalism.Universal.Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld DebtAdmissionFirstWrite

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument
local notation "Script" => List (Option (Capitalism.Universal.Abolition.Root.Registered.Compile.RawInput
  Party Good Port Technology Instrument))

/-- The activated obligation has only a phase and a restriction of the
original paid continuation. Every material quantity is a source readout. -/
inductive Stage (source : C) (attack : Word)
  | unfiled
  | filed (tail : Word) (actual : Root.Paid source (attack ++ tail))
  | recorded (tail : Script)

variable {source : Root.Cut Party Good Port Technology Instrument}
  {attack : RawEvent Party Good Port Technology Instrument}
  {community : Party → Community} {key : Key Party Good}
  (claim : ClaimAt source attack community key)

def opening : Stage source attack :=
  .filed [] (by simpa only [List.append_nil] using claim.paid)

def budget : Stage source attack → Nat
  | .unfiled => 2
  | .filed tail _ => if remaining source attack tail community key = 0 then 0 else 1
  | .recorded tail => if recordedDue source attack tail community key = 0 then 0 else 1

theorem opening_budget : budget (community := community) (key := key) (opening claim) = 1 := by
  simp [budget, opening, initial_remaining_is_the_original_amount claim, ne_of_gt claim.positive]

inductive Step : Stage source attack → Stage source attack → Type
  | declare : Step .unfiled (opening claim)
  | pay {front : Word} (earlier : Root.Paid source (attack ++ front))
      (rest : Word) (actual : Root.Paid source (attack ++ (front ++ rest)))
      (outstanding : 0 < remaining source attack front community key)
      (closed : remaining source attack (front ++ rest) community key = 0) :
      Step (.filed front earlier) (.filed (front ++ rest) actual)
  | payRecordedStart (first : Script) (closed : recordedDue source attack first community key = 0) :
      Step (opening claim) (.recorded first)
  | payRecordedNext (front rest : Script)
      (outstanding : 0 < recordedDue source attack front community key)
      (closed : recordedDue source attack (front ++ rest) community key = 0) :
      Step (.recorded front) (.recorded (front ++ rest))

inductive Carry : Stage source attack → Stage source attack → Type
  | waiting (state : Stage source attack) : Carry state state
  | continued {front : Word} (earlier : Root.Paid source (attack ++ front))
      (rest : Word) (actual : Root.Paid source (attack ++ (front ++ rest))) :
      Carry (.filed front earlier) (.filed (front ++ rest) actual)
  | recordedStart (earlier : Root.Paid source (attack ++ [])) (first : Script) :
      Carry (.filed [] earlier) (.recorded first)
  | recordedNext (front rest : Script) : Carry (.recorded front) (.recorded (front ++ rest))

inductive Settlement : Stage source attack → Type
  | actual {tail : Word} (paid : Root.Paid source (attack ++ tail))
      (zero : remaining source attack tail community key = 0) : Settlement (.filed tail paid)
  | actualRecorded {tail : Script}
      (record : Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recorded
        (Root.terminal source attack) tail)
      (zero : recordedDue source attack tail community key = 0) : Settlement (.recorded tail)

inductive Obstruction : Stage source attack → Type
  | notFiled : Obstruction .unfiled
  | unpaid {tail : Word} (paid : Root.Paid source (attack ++ tail))
      (positive : 0 < remaining source attack tail community key) : Obstruction (.filed tail paid)
  | recordedUnpaid {tail : Script} (positive : 0 < recordedDue source attack tail community key) :
      Obstruction (.recorded tail)

private theorem balance_budget_decreases {before after : ℚ} (descends : after ≤ before) (nonnegative : 0 ≤ after) :
    (if after = 0 then (0 : Nat) else 1) ≤ if before = 0 then 0 else 1 := by
  by_cases closed : after = 0
  · rw [if_pos closed]
    exact Nat.zero_le _
  · have original : before ≠ 0 := by
      intro zero
      exact closed (le_antisymm (descends.trans_eq zero) nonnegative)
    simp only [if_neg closed, if_neg original, Nat.le_refl]

include claim in
private theorem carry_budget {earlier later : Stage source attack} (step : Carry earlier later) :
    budget (community := community) (key := key) later ≤ budget (community := community) (key := key) earlier := by
  cases step with
  | waiting => exact le_rfl
  | @continued front _ rest _ =>
    exact balance_budget_decreases (remaining_append_le source attack front rest community key) (le_max_left _ _)
  | recordedStart _ first =>
    change (if recordedDue source attack first community key = 0 then 0 else 1) ≤
      budget (community := community) (key := key) (opening claim)
    rw [opening_budget claim]
    split <;> decide
  | recordedNext front rest =>
    exact balance_budget_decreases (recordedDue_append_le source attack front rest community key) (le_max_left _ _)

/-- An original damage event generates an additional responsibility
coordinate. Filing uses the paid damage rather than a debtor-signed loan. -/
def law : DebtActivationLaw where
  DebtState := Stage source attack
  DebtId := Key Party Good
  DebtClaim := {address : Key Party Good // ClaimAt source attack community address}
  debtId := key
  debtClaim := ⟨key, claim⟩
  budget := budget (community := community) (key := key)
  StepAt := Step claim
  step_budget_lt := by
    intro _ _ step
    cases step with
    | declare =>
      rw [opening_budget claim]
      change 1 < 2
      decide
    | pay _ _ _ positive closed => simp [budget, ne_of_gt positive, closed]
    | payRecordedStart _ closed => rw [opening_budget claim]; simp [budget, closed]
    | payRecordedNext _ _ positive closed => simp [budget, ne_of_gt positive, closed]
  transportLaw? := some
    { EventAt := Carry
      budget_le := carry_budget claim }
  SettlementAt := Settlement (community := community) (key := key)
  settlement_budget_zero := by
    intro _ evidence
    cases evidence with
    | actual _ closed => simp [budget, closed]
    | actualRecorded _ closed => simp [budget, closed]
  supportTerminalLaw? := none
  ObstructionAt := Obstruction (community := community) (key := key)

def filing : SourceFixedDebtAdmissionEventAt (law claim) (.unfiled) :=
  SourceFixedDebtAdmissionEventAt.ofStep (Step.declare (claim := claim))

theorem original_debt_is_live_on_filing :
    (law claim).budget (filing claim).target = 1 :=
  opening_budget claim

theorem unilateral_continuation_cannot_certify_settlement
    (tail : Word) (actual : Root.Paid source (attack ++ tail))
    (unilateral : ∀ request ∈ tail, community request.signer = community key.2.1) :
    ¬ Nonempty ((law claim).SettlementAt (.filed tail actual)) := by
  rintro ⟨closure⟩
  cases closure with
  | actual _ zero => exact (ne_of_gt (unilateral_carry_cannot_archive claim tail unilateral)) zero

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Birth
