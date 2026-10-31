import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Response.Plan
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Response.Origin

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Response

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle

variable {fuel : ℚ} {inputs : List (List Action)}

def positionsBefore (count : Nat) : List (Position fuel inputs) :=
  (List.range count).flatMap (positionsAt fuel inputs)

theorem position_before {count : Nat} (position : Position fuel inputs) (present : position ∈ positionsBefore count) :
    position.ordinal < count := by
  obtain ⟨ordinal, inside, located⟩ := List.mem_flatMap.mp present
  obtain ⟨index, _, same⟩ := List.mem_map.mp located
  cases same
  exact List.mem_range.mp inside

structure Pending (cut : Cut fuel inputs) where
  private mk ::
  claim : Claim fuel inputs
  decoded : read fuel inputs claim.position = some claim
  inside : claim.position.ordinal < cut.depth + 2
  live : (through fuel inputs claim (cut.depth + 2)).isPending fuel inputs = true

def pendingAt (cut : Cut fuel inputs) : List (Pending cut) :=
  (positionsBefore (fuel := fuel) (inputs := inputs) (cut.depth + 2)).attach.filterMap fun position =>
    match decoded : read fuel inputs position.val with
    | none => none
    | some claim =>
      if live : (through fuel inputs claim (cut.depth + 2)).isPending fuel inputs = true then
        some ⟨claim, by rw [read_position position.val claim decoded]; exact decoded,
          by rw [read_position position.val claim decoded]; exact position_before position.val position.property, live⟩
      else none

def pending (cut : Cut fuel inputs) : Option (Pending cut) :=
  ((pendingAt cut).find? (fun original => decide (original.claim.snapshot fuel inputs = cut.past.frame.raw.technology))).orElse
    (fun _ => (pendingAt cut).head?)

inductive Decision (cut : Cut fuel inputs)
  | ordinary
  | current (original : Pending cut) (same : original.claim.snapshot fuel inputs = cut.past.frame.raw.technology)
  | shifted (original : Pending cut) (changed : original.claim.snapshot fuel inputs ≠ cut.past.frame.raw.technology)

def decideAt (cut : Cut fuel inputs) : Decision cut :=
  match pending cut with
  | none => .ordinary
  | some original =>
    if same : original.claim.snapshot fuel inputs = cut.past.frame.raw.technology then .current original same
    else .shifted original same

def Decision.word {cut : Cut fuel inputs} : Decision cut → List Action
  | .ordinary => (reply fuel cut.past).word
  | .current .. => Response.word cut.past.frame.raw
  | .shifted .. => [submission]

def emit (cut : Cut fuel inputs) := (decideAt cut).word
abbrev nextInputs (cut : Cut fuel inputs) := branchInputs cut (emit cut)
def nextCut (cut : Cut fuel inputs) := afterInput cut (emit cut)

theorem native_pending_is_live (cut : Cut fuel inputs) (original : Pending cut) :
    (through fuel inputs original.claim (cut.depth + 2)).state.current.LiveAt 0 :=
  History.live_of_pending _ _ _ original.live

theorem feedback_is_actually_emitted (cut : Cut fuel inputs) :
    (actualExecution fuel (nextInputs cut) (cut.depth + 1)).submitted = emit cut :=
  new_input_is_actually_emitted cut (emit cut)

theorem feedback_uses_its_own_actual_current (cut : Cut fuel inputs) :
    (actualExecution fuel (nextInputs cut) (cut.depth + 1)).before = cut.past.frame.raw :=
  new_input_uses_the_original_cut cut (emit cut)

theorem feedback_next_is_its_actual_effect (cut : Cut fuel inputs) :
    (nextCut cut).past = cut.past.append (emit cut) := afterInput_is_the_interpreted_original_cut cut (emit cut)

theorem failure_is_in_the_emitted_interpreter (cut : Cut fuel inputs) (original : Pending cut)
    (same : original.claim.snapshot fuel inputs = cut.past.frame.raw.technology)
    (selected : decideAt cut = .current original same) (failure : Failure cut.past.frame.raw) :
    failure.item ∈ law.rawItems (actualExecution fuel (nextInputs cut) (cut.depth + 1)).before
      (actualExecution fuel (nextInputs cut) (cut.depth + 1)).submitted ∧ ¬ law.Valid failure.item.before failure.item.request := by
  rw [feedback_is_actually_emitted, feedback_uses_its_own_actual_current]
  simp only [emit, selected, Decision.word]
  exact every_failure_is_in_the_actual_word _ failure

theorem order_is_in_the_emitted_word (cut : Cut fuel inputs) (original : Pending cut)
    (same : original.claim.snapshot fuel inputs = cut.past.frame.raw.technology)
    (selected : decideAt cut = .current original same) (order : Order cut.past.frame.raw)
    (present : order ∈ orders cut.past.frame.raw) :
    order.request ∈ (actualExecution fuel (nextInputs cut) (cut.depth + 1)).submitted := by
  rw [feedback_is_actually_emitted]
  simp only [emit, selected, Decision.word]
  exact every_order_is_an_actual_request _ order present

def transportedClaim (cut : Cut fuel inputs) (original : Pending cut) :=
  replacement cut (emit cut) original.claim original.inside

def oldHistory (cut : Cut fuel inputs) (original : Pending cut) := through fuel inputs original.claim (cut.depth + 2)
def newBefore (cut : Cut fuel inputs) (original : Pending cut) :=
  through fuel (nextInputs cut) (transportedClaim cut original) (cut.depth + 2)
def newAfter (cut : Cut fuel inputs) (original : Pending cut) :=
  through fuel (nextInputs cut) (transportedClaim cut original) (cut.depth + 3)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Response
