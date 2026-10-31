import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Renewal.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Joint.Growth

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Renewal

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Followup

variable {fuel : ℚ}

def legalOpening : List Action := [submission]

theorem legal_opening_is_a_real_valid_word (current : Current) :
    ∀ item ∈ law.rawItems current legalOpening, law.Valid item.before item.request := by
  intro item inside
  change item ∈ [⟨0, current, submission⟩] at inside
  have same := List.mem_singleton.mp inside
  subst item
  exact submission_valid current

theorem legal_opening_strictly_grows_the_native_ledger (inventory : Joint.Inventory fuel)
    (active : Mandate.Response.Active inventory.cut.past.frame.raw) :
    Joint.volume inventory.frame.rows < Joint.volume (Joint.submit inventory legalOpening).frame.rows := by
  apply Joint.an_actual_signature_strictly_grows_the_whole_native_ledger inventory (signedWord []) (firstIndex inventory [])
    (Opening.signature inventory.cut [] active)
  rw [first_event_is_the_signature_position]
  exact Opening.signature_is_actually_read inventory.cut [] active

/-- A legal sink would prevent every lawful primitive continuation from
recording an additional native admission or lifecycle event. -/
def LegalNativeSink (inventory : Joint.Inventory fuel) : Prop :=
  ∀ word, (∀ item ∈ law.rawItems inventory.cut.past.frame.raw word, law.Valid item.before item.request) →
    Joint.volume (Joint.submit inventory word).frame.rows ≤ Joint.volume inventory.frame.rows

theorem no_active_actual_cut_is_a_legal_native_sink (inventory : Joint.Inventory fuel)
    (active : Mandate.Response.Active inventory.cut.past.frame.raw) : ¬ LegalNativeSink inventory := by
  intro sink
  exact Nat.not_le_of_lt (legal_opening_strictly_grows_the_native_ledger inventory active)
    (sink legalOpening (legal_opening_is_a_real_valid_word _))

theorem every_legal_reachable_active_current_has_an_actual_nonabsorbing_ledger (fuel : ℚ) (current : Current)
    (reached : OutstandingSource.History.LegalReach (source fuel) current) (active : Mandate.Response.Active current) :
    ∃ inventory : Joint.Inventory fuel, inventory.cut.past.frame.raw = current ∧ ¬ LegalNativeSink inventory := by
  obtain ⟨inputs, same⟩ := OutstandingSource.History.every_legal_reachable_state_has_its_own_actual_source
    (source fuel) current reached
  let inventory := Joint.initial (start fuel inputs)
  have actual : inventory.cut.past.frame.raw = current := (start fuel inputs).actual_current.trans same
  exact ⟨inventory, actual, no_active_actual_cut_is_a_legal_native_sink inventory (by rw [actual]; exact active)⟩

def lastIndex (inventory : Joint.Inventory fuel) (actor : Bool) :
    Fin (Joint.actualEvents inventory.cut (word inventory.cut.past.frame.raw actor)).length :=
  ⟨(attemptedWord inventory.cut.past.frame.raw actor).length, by
    have bound : (attemptedWord inventory.cut.past.frame.raw actor).length <
        (financialItems fuel (branchInputs inventory.cut (word inventory.cut.past.frame.raw actor)) (inventory.cut.depth + 2)).length :=
      (signaturePosition inventory.cut actor).index.isLt
    simpa only [Joint.actualEvents, List.length_map, List.length_finRange] using bound⟩

theorem last_event_is_the_actual_post_attempt_signature (inventory : Joint.Inventory fuel) (actor : Bool) :
    ((Joint.actualEvents inventory.cut (word inventory.cut.past.frame.raw actor)).get (lastIndex inventory actor)).val =
      signaturePosition inventory.cut actor := by
  let count := (financialItems fuel (branchInputs inventory.cut (word inventory.cut.past.frame.raw actor))
    (inventory.cut.depth + 2)).length
  let index := (attemptedWord inventory.cut.past.frame.raw actor).length
  have bound : index < count := (signaturePosition inventory.cut actor).index.isLt
  have rangeBound : index < (List.finRange count).length := by simpa only [List.length_finRange] using bound
  have mappedBound : index < ((List.finRange count).map (Joint.actualEvent inventory.cut (word inventory.cut.past.frame.raw actor))).length := by
    simpa only [List.length_map] using rangeBound
  change (((List.finRange count).map (Joint.actualEvent inventory.cut (word inventory.cut.past.frame.raw actor)))[index]'mappedBound).val = _
  rw [List.getElem_map]
  change (⟨inventory.cut.depth + 2, (List.finRange count)[index]'rangeBound⟩ : Position fuel _) = _
  apply congrArg (fun entry : Fin count => (⟨inventory.cut.depth + 2, entry⟩ : Position fuel _))
  apply Fin.ext
  simp only [List.getElem_finRange]
  rfl

theorem signed_word_strictly_grows_the_native_ledger (inventory : Joint.Inventory fuel) (suffix : List Action)
    (active : Mandate.Response.Active inventory.cut.past.frame.raw) :
    Joint.volume inventory.frame.rows < Joint.volume (Joint.submit inventory (signedWord suffix)).frame.rows := by
  apply Joint.an_actual_signature_strictly_grows_the_whole_native_ledger inventory _ (firstIndex inventory suffix)
    (Opening.signature inventory.cut suffix active)
  rw [first_event_is_the_signature_position]
  exact Opening.signature_is_actually_read inventory.cut suffix active

theorem actual_exit_strictly_grows_the_native_ledger (inventory : Joint.Inventory fuel)
    (active : Mandate.Response.Active inventory.cut.past.frame.raw) :
    Joint.volume inventory.frame.rows < Joint.volume (Joint.submit inventory (Exit.emit inventory)).frame.rows := by
  cases held : inventory.cut.past.frame.raw.technology.holder with
  | some actor =>
      rw [Exit.holder_emission inventory actor held]
      exact signed_word_strictly_grows_the_native_ledger inventory _ active
  | none =>
      rw [Exit.emit, held, Opening.active_emission inventory active]
      exact signed_word_strictly_grows_the_native_ledger inventory _ active

theorem every_active_emission_strictly_grows_the_native_ledger (inventory : Joint.Inventory fuel)
    (active : Mandate.Response.Active inventory.cut.past.frame.raw) :
    Joint.volume inventory.frame.rows < Joint.volume (advance inventory).frame.rows := by
  change Joint.volume inventory.frame.rows < Joint.volume (Joint.submit inventory (emit inventory)).frame.rows
  by_cases waiting : pending inventory = true
  · have emitted : emit inventory = Admission.emit inventory := by simp only [emit, if_pos waiting]
    rw [emitted, Admission.active_emission_is_the_existing_exit inventory active]
    exact actual_exit_strictly_grows_the_native_ledger inventory active
  · cases held : inventory.cut.past.frame.raw.technology.holder with
    | none =>
        have emitted : emit inventory = Admission.emit inventory := by simp only [emit, if_neg waiting, held]
        rw [emitted, Admission.active_emission_is_the_existing_exit inventory active]
        exact actual_exit_strictly_grows_the_native_ledger inventory active
    | some actor =>
        have emitted : emit inventory = word inventory.cut.past.frame.raw actor := by simp only [emit, if_neg waiting, held]
        rw [emitted]
        apply Joint.an_actual_signature_strictly_grows_the_whole_native_ledger inventory _ (lastIndex inventory actor)
          (signature inventory.cut actor held)
        rw [last_event_is_the_actual_post_attempt_signature]
        exact signature_is_actually_read inventory.cut actor held

theorem finite_active_source_run_has_strictly_accumulating_native_history (inventory : Joint.Inventory fuel) (count : Nat)
    (active : ∀ index < count, Mandate.Response.Active (run inventory index).cut.past.frame.raw) :
    Joint.volume inventory.frame.rows + count ≤ Joint.volume (run inventory count).frame.rows := by
  induction count with
  | zero => exact Nat.le_refl _
  | succ count ih =>
      have prior := ih (fun index inside => active index (Nat.lt_trans inside (Nat.lt_succ_self _)))
      have next := every_active_emission_strictly_grows_the_native_ledger (run inventory count)
        (active count (Nat.lt_succ_self _))
      change _ ≤ Joint.volume (advance (run inventory count)).frame.rows
      omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Renewal
