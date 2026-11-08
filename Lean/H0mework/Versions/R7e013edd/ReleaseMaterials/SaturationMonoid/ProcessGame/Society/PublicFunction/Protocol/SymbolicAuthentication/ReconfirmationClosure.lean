import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeOpportunityConsumer
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WithdrawalInquiry

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReconfirmationClosure
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Mandate.Challenge

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Mandate.Scope (Party := Party) (Good := Good) (Port := Port)}
  {Index : Type} (bound : ProgrammeFamily base scope Index) (inputs : Index)
  (original : Claim bound inputs) (first second : Position bound inputs)

def advances (receipt : Reconfirmation bound inputs original) : Bool :=
  match through bound inputs original first.ordinal with
  | .closed .. => false
  | .pending target .. => decide (Later bound inputs (target.claim bound inputs).position receipt.target.position)

theorem the_two_actual_positions_close_the_same_original
    (positions : positionsAt bound inputs first.ordinal = [first, second])
    (receipt : Reconfirmation bound inputs original)
    (renewed : readReconfirmation bound inputs original first = some receipt)
    (forward : advances bound inputs original first receipt = true)
    (noRenewal : readReconfirmation bound inputs original second = none)
    (attempt : Attempt bound inputs receipt.target)
    (withdrawn : readAttempt bound inputs receipt.target second = some attempt)
    (paid : (Mandate.law base scope).Valid (attempt.position.item bound inputs).before
      (attempt.position.item bound inputs).request) :
    (through bound inputs original (first.ordinal + 1)).isPending bound inputs = false := by
  rw [through, positions]
  simp only [List.foldl_cons, List.foldl_nil]
  cases before : through bound inputs original first.ordinal with
  | closed state archive slots => rfl
  | pending target state slots =>
    have later : Later bound inputs (target.claim bound inputs).position receipt.target.position := by
      unfold advances at forward
      rw [before] at forward
      exact of_decide_eq_true forward
    generalize acted : (History.pending target state slots).receive bound inputs first = next
    cases next with
    | closed nextState archive nextSlots => rfl
    | pending nextTarget nextState nextSlots =>
      let targetOf : History bound inputs original → Option (Target bound inputs original)
        | .pending value .. => some value
        | .closed .. => none
      have projected := congrArg targetOf acted
      simp only [History.receive, renewed, dif_pos later, targetOf] at projected
      cases Option.some.inj projected
      simp only [History.receive, noRenewal, Target.claim, withdrawn, dif_pos paid, History.isPending]

private def tag (position : Position bound inputs) := (position.ordinal, position.index.val)

private theorem tag_injective : Function.Injective (tag bound inputs) := by
  intro left right same
  cases left with
  | mk ordinal index =>
    cases right with
    | mk other candidate =>
      obtain ⟨rfl, equal⟩ := Prod.mk.inj same
      have sameIndex := Fin.ext equal
      cases sameIndex
      rfl

theorem two_positions_are_the_complete_actual_visit
    (same : second.ordinal = first.ordinal) (one : first.index.val = 0) (two : second.index.val = 1)
    (count : (Institutions.Capitalism.Universal.Source.ProgrammeFace.Registered.traceItems (I bound inputs)
      (ProgrammeHistory.visitAt (I bound inputs) first.ordinal).current).length = 2) :
    positionsAt bound inputs first.ordinal = [first, second] := by
  apply (List.map_injective_iff.mpr (tag_injective bound inputs))
  simp only [positionsAt, List.map_map, Function.comp_def, tag, List.map_cons, List.map_nil]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_finRange, count, List.length_cons, List.length_nil]
  · intro index leftBound rightBound
    have bounded : index < 2 := by simpa only [List.length_map, List.length_finRange, count] using leftBound
    have possibilities : index = 0 ∨ index = 1 := by omega
    rcases possibilities with rfl | rfl
    · simp only [List.getElem_map, List.getElem_finRange, List.getElem_cons_zero, one, Fin.val_cast]
    · simp only [List.getElem_map, List.getElem_finRange, List.getElem_cons_succ, List.getElem_cons_zero,
        same, two, Fin.val_cast]


end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReconfirmationClosure
