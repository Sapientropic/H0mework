import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.History.Cursor

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.History

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]
  {source : Root.Cut Party Good Port Technology Instrument}
  {attack : RawEvent Party Good Port Technology Instrument}
  {community : Party → Community} {key : Key Party Good}
  (claim : ClaimAt source attack community key)
  (script : List (Option (Compile.RawInput Party Good Port Technology Instrument)))

/-- The initial entry is the actual already-filed row. Later amounts come
from the original material inventory of the prefix at this native visit. -/
def debtAt : Cursor claim script → Birth.Stage source attack
  | .inl position =>
    if position.val = 0 then Birth.opening claim else .recorded (script.take position.val)
  | .inr _ => .recorded script

theorem debt_after_original_step (position : Fin script.length) :
    debtAt claim script (nextCursor claim script (.inl position)) =
      .recorded (script.take (position.val + 1)) := by
  by_cases later : position.val + 1 < script.length
  · have selected : nextCursor claim script (.inl position) = .inl ⟨position.val + 1, later⟩ := dif_pos later
    exact (congrArg (debtAt claim script) selected).trans
      (if_neg (t := Birth.opening claim) (Nat.succ_ne_zero position.val))
  · have selected : nextCursor claim script (.inl position) = .inr (finalCut claim script).native.visit.current :=
      dif_neg later
    have last : position.val + 1 = script.length := by omega
    exact (congrArg (debtAt claim script) selected).trans
      (congrArg Birth.Stage.recorded (by rw [last, List.take_length]))

private def move {first last start finish : Birth.Stage source attack}
    (initial : first = start) (final : last = finish)
    (event : (Birth.law claim).StepAt start finish ⊕ (Birth.law claim).TransportAt start finish) :
    (Birth.law claim).StepAt first last ⊕ (Birth.law claim).TransportAt first last := by
  cases initial
  cases final
  exact event

set_option maxHeartbeats 600000 in
def disposition (current : Cursor claim script) :
    (Birth.law claim).StepAt (debtAt claim script current) (debtAt claim script (nextCursor claim script current)) ⊕
      (Birth.law claim).TransportAt (debtAt claim script current) (debtAt claim script (nextCursor claim script current)) := by
  cases current with
  | inr original => exact .inr (.waiting (.recorded script))
  | inl position =>
    have nextStage := debt_after_original_step claim script position
    let nextPrefix := script.take (position.val + 1)
    by_cases first : position.val = 0
    · let event : (Birth.law claim).StepAt (Birth.opening claim) (.recorded nextPrefix) ⊕
          (Birth.law claim).TransportAt (Birth.opening claim) (.recorded nextPrefix) :=
        if zero : recordedDue source attack nextPrefix community key = 0 then
          .inl (Birth.Step.payRecordedStart (claim := claim) nextPrefix zero)
        else .inr (Birth.Carry.recordedStart (by simpa only [List.append_nil] using claim.paid) nextPrefix)
      exact move claim (if_pos first) nextStage event
    · let front := script.take position.val
      let rest := [script[position.val]]
      have joined : nextPrefix = front ++ rest := List.take_succ_eq_append_getElem position.isLt
      let event : (Birth.law claim).StepAt (.recorded front) (.recorded (front ++ rest)) ⊕
          (Birth.law claim).TransportAt (.recorded front) (.recorded (front ++ rest)) :=
        if positive : 0 < recordedDue source attack front community key then
          if zero : recordedDue source attack (front ++ rest) community key = 0 then
            .inl (Birth.Step.payRecordedNext (claim := claim) front rest positive zero)
          else .inr (Birth.Carry.recordedNext front rest)
        else .inr (Birth.Carry.recordedNext front rest)
      exact move claim (if_neg first) (nextStage.trans (congrArg Birth.Stage.recorded joined)) event

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.History
