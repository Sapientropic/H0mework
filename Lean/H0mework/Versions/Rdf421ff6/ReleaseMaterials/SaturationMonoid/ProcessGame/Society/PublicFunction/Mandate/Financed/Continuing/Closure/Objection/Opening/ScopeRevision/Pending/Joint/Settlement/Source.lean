import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Effects
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Repayment.Portfolio.Local

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Settlement

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Followup

variable {fuel : ℚ} {old : Followup.Joint.Inventory fuel} (ready : Ready old)
  {originInputs : List (List Action)} (inventory : Inventory ready originInputs)

/-- The complete address space, before filtering by the saved native shares. -/
def addresses : List (Repayment.Position Bool Unit) :=
  [⟨(), false, false⟩, ⟨(), false, true⟩, ⟨(), true, false⟩, ⟨(), true, true⟩]

def balance (position : Repayment.Position Bool Unit) : ℚ :=
  Financial.Family.ledgerClaims Finance.sources inventory.finance.current position.instrument position.debtor position.creditor

def positions := addresses.filter fun position => decide (0 < balance ready inventory position)

def objectionWord := Joint.emit ready inventory
def afterPrefix := ((epochLaw ready).execute (current ready inventory.inputs) 0 (objectionWord ready inventory)).final

def suffix := Repayment.Portfolio.word (epochLaw ready) (positions ready inventory) (afterPrefix ready inventory)
def emit := objectionWord ready inventory ++ suffix ready inventory

noncomputable def advance := submit ready inventory (emit ready inventory)
noncomputable abbrev I := OutstandingSource.History.input (epochSource ready) (advance ready inventory).inputs
noncomputable abbrev execution := Joint.actual ready inventory (emit ready inventory)

theorem every_positive_native_address_is_selected (position : Repayment.Position Bool Unit)
    (positive : 0 < balance ready inventory position) : position ∈ positions ready inventory := by
  apply List.mem_filter.mpr
  refine ⟨?_, decide_eq_true positive⟩
  rcases position with ⟨instrument, debtor, creditor⟩
  cases instrument
  cases debtor <;> cases creditor <;> simp [addresses]

private theorem silent_step (before : Current) (action : Action) (silent : ClaimSilent action) :
    ((epochLaw ready).step before action).claims = before.claims := by
  unfold RawLaw.step
  split
  · change RawLaw.nextClaims before action = before.claims
    rcases action with ⟨signer, consents, purpose, gates, operation⟩
    cases operation <;> simp_all [ClaimSilent, RawLaw.nextClaims]
  · rfl

private theorem silent_execute (before : Current) (index : Nat) (word : List Action)
    (silent : ∀ action ∈ word, ClaimSilent action) :
    (((epochLaw ready).execute before index word).final).claims = before.claims := by
  induction word generalizing before index with
  | nil => rfl
  | cons action tail ih =>
    change (((epochLaw ready).execute ((epochLaw ready).step before action) (index + 1) tail).final).claims = _
    rw [ih _ _ (fun next member => silent next (List.mem_cons_of_mem _ member)),
      silent_step ready before action (silent action List.mem_cons_self)]

theorem saved_native_shares_are_the_actual_suffix_balances :
    (afterPrefix ready inventory).claims = Financial.Family.ledgerClaims Finance.sources inventory.finance.current :=
  (silent_execute ready _ 0 _ (Joint.emitted_word_is_financially_silent ready inventory)).trans
    (financial_matrix_at_every_actual_cut ready inventory).symm

theorem original_objection_response_is_the_literal_prefix :
    Joint.emit ready inventory <+: emit ready inventory := List.prefix_append _ _

theorem actual_word_and_cut :
    (execution ready inventory).submitted = emit ready inventory ∧
    (execution ready inventory).before = current ready inventory.inputs :=
  Joint.actual_word_and_cut ready inventory _

theorem actual_after :
    (current ready (advance ready inventory).inputs) =
      (epochLaw ready).next (current ready inventory.inputs) (emit ready inventory) := by
  have after := OutstandingSource.History.actual_next (epochSource ready) (advance ready inventory).inputs
    (inventory.inputs.length + 1)
  have word := actual_word_and_cut ready inventory
  have length : (advance ready inventory).inputs.length + 2 = inventory.inputs.length + 3 := by
    change (inventory.inputs ++ [emit ready inventory]).length + 2 = _
    simp only [List.length_append, List.length_singleton, Nat.add_assoc]
  change OutstandingSource.History.currentAt (epochSource ready) (advance ready inventory).inputs
    ((advance ready inventory).inputs.length + 2) = _
  rw [length, ← after]
  change (epochLaw ready).next (execution ready inventory).before (execution ready inventory).submitted = _
  rw [word.1, word.2]

/-- The two stages share one execution; the suffix reads the objection response's actual final state. -/
theorem composed_execution :
    ((epochLaw ready).execute (current ready inventory.inputs) 0 (emit ready inventory)).final =
      ((epochLaw ready).execute (afterPrefix ready inventory) 0 (suffix ready inventory)).final :=
  Repayment.Portfolio.execute_append_final _ _ _ _

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Settlement
