import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Contract.Step
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary.Defence

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open PublicFunction.Mandate
open Quantities.Execution (endAt endAt_append endAt_input inventory inventory_append primitiveScript)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology]
  [DecidableEq Instrument] [DecidableEq Community]

local notation "M" => State Party Technology
local notation "C" => Root.Cut Party Good Port M Instrument
local notation "Word" => Reparation.Actual.Script Party Good Port M Instrument
local notation "RawWord" => RawEvent Party Good Port M Instrument

variable {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
  {seed : Root.Cut Party Good Port (State Party Technology) Instrument}
  {community : Party → Community} {anchor : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument}
  {control : RawCurrent Party Good (State Party Technology) Instrument → List Party}
  (prior : GuardedVisit base scope seed community anchor control) (answers : OwnerAnswers seed)
  (offer : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument →
    Reparation.Actual.Script Party Good Port (State Party Technology) Instrument)

/-- All earlier native inputs determine the actual people and items at
each visit of a submitted response. -/
structure ResponseRoute (word : Word) : Prop where
  authors : ∀ front input tail, word = front ++ input :: tail →
    let past := prior.history ++ front
    let roster := bearers seed community anchor ++ bearers seed community past
    Authorized roster answers past input ∧ ∀ position, grantRule roster answers past input position
  exits : ∀ front : Word, front.IsPrefix word →
    let history := prior.history ++ front
    MandateExit.PaidAt seed anchor history ∧
      MandateExit.LiveCertificate seed anchor history community base scope control (offer history)

theorem the_same_guard_forwards_each_visit_of_the_actual_response {word : Word}
    (paid : Reparation.Actual.SourceAuthority (endAt seed prior.history) word)
    (route : ResponseRoute prior answers offer word) (front : Word)
    (input : Reparation.Actual.Input Party Good Port M Instrument) (tail : Word)
    (split : word = front ++ input :: tail) :
    let past := prior.history ++ front
    let roster := bearers seed community anchor ++ bearers seed community past
    let viable := fun history => MandateExit.ReadyAt seed anchor history community base scope control
    (select roster answers grantRule viable (exitProbe base scope seed community anchor control offer) past input).emitted =
      [input] := by
  let next := (prior.history ++ front) ++ [input]
  have exactAuth := route.authors front input tail split
  have exits := route.exits (front ++ [input])
    ⟨tail, by simpa only [List.append_assoc, List.singleton_append] using split.symm⟩
  have due : MandateExit.PaidAt seed anchor next := by simpa only [next, List.append_assoc] using exits.1
  have own : MandateExit.LiveCertificate seed anchor next community base scope control (offer next) := by
    simpa only [next, List.append_assoc] using exits.2
  obtain ⟨verified, checked⟩ := MandateExit.a_paid_nominated_word_supplies_the_checked_continuation
    seed anchor next community base scope control (offer next) due own
  have originalAuthority : Reparation.Actual.SourceAuthority (endAt seed (prior.history ++ front)) [input] := by
    intro item listed
    have original : item ∈ inventory (endAt seed prior.history) word := by
      rw [split, inventory_append, List.mem_append]
      right
      rw [show input :: tail = [input] ++ tail from rfl, inventory_append, List.mem_append]
      left
      rwa [← endAt_append]
    have valid := paid item original
    rw [endAt_input] at valid ⊢
    exact valid
  exact the_composed_gate_forwards_an_admitted_continuation
    (bearers seed community anchor ++ bearers seed community (prior.history ++ front))
    answers grantRule (fun history => MandateExit.ReadyAt seed anchor history community base scope control)
    (exitProbe base scope seed community anchor control offer) (prior.history ++ front) input
    ⟨originalAuthority, exactAuth.1⟩ exactAuth.2 (verified := verified) checked

variable {source : Root.Cut Party Good Port (State Party Technology) Instrument}
  {attackWord response floor : RawEvent Party Good Port (State Party Technology) Instrument}
  (attack : Boundary.AggressionAt source attackWord community)

def defend (_atAttack : endAt seed prior.history = attack.after)
    (_defended : Boundary.DefenceAt attack response floor)
    (route : ResponseRoute prior answers offer (primitiveScript response)) :
    GuardedVisit base scope seed community anchor control :=
  let checked := route.exits (primitiveScript response) List.prefix_rfl
  ⟨prior.history ++ primitiveScript response, prior.original.trans (List.prefix_append _ _),
    Receipts.writeAfter answers prior.state (primitiveScript response),
    Receipts.writeAfter_origins answers prior.history _ prior.state prior.origins,
    ⟨checked.1, _, checked.2⟩⟩

/-- An actual local defence keeps its original permissive effect and
its independent floor on the very successor used by the guarded root. -/
theorem the_paid_defence_uses_the_same_admission_and_original_reparation_successor
    (atAttack : endAt seed prior.history = attack.after)
    (defended : Boundary.DefenceAt attack response floor)
    (route : ResponseRoute prior answers offer (primitiveScript response)) :
    let word := primitiveScript response
    let reached := defend prior answers offer attack atAttack defended route
    (∀ front input tail, word = front ++ input :: tail →
      let past := prior.history ++ front
      let roster := bearers seed community anchor ++ bearers seed community past
      let viable := fun history => MandateExit.ReadyAt seed anchor history community base scope control
      (select roster answers grantRule viable (exitProbe base scope seed community anchor control offer) past input).emitted =
        [input]) ∧
      Quantities.Recorded seed reached.history ∧
      ¬ Boundary.Permission attack.after.native.input.law (endAt seed reached.history).raw attack.item.request ∧
      ¬ Nonempty (Boundary.AggressionAt attack.after response community) ∧
      Boundary.ExitFloorAt source (endAt seed reached.history) attack.residents floor ∧
      MandateExit.ReadyAt seed anchor reached.history community base scope control ∧
      ∀ loss ∈ Reparation.Actual.originalLosses seed community reached.history,
        ∃ balance, ∃ row, reached.state.read row = .inr (loss, balance) := by
  let reached := defend prior answers offer attack atAttack defended route
  have paid := Emergency.originalAuthority_of_paid_word defended.responsePaid
  have authority : Reparation.Actual.SourceAuthority (endAt seed prior.history) (primitiveScript response) :=
    atAttack.symm ▸ paid
  have reachedExact : endAt seed reached.history = Root.terminal attack.after response := by
    change endAt seed (prior.history ++ primitiveScript response) = _
    rw [endAt_append, atAttack]
  refine ⟨fun front input tail split => the_same_guard_forwards_each_visit_of_the_actual_response
      prior answers offer authority route front input tail split,
    Quantities.record _ _, ?_, defended.noOverreach, ?_, reached.continues, reached.every_original_loss_has_an_exact_live_row⟩
  · rw [reachedExact]
    exact defended.closed
  · rw [reachedExact]
    exact defended.independentExit

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard
