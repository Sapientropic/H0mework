import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Effects
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Embedding.Canonical

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Finance

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Followup

abbrev Input := ProgrammeSource.Input Bool Good Mandate.Source.Port (State Bool Unit) Unit
def sources : Input → Input := id
abbrev Account := (Financial.Family.process sources).GeneratedState

variable {fuel : ℚ} {old : Followup.Joint.Inventory fuel} (ready : Ready old)

def originalInput (_ : Ready old) : Input := Objection.I fuel (ScopeRevision.advance old).inputs
def originalAccount : Account :=
  (Financial.Family.Embedding.accountAt sources (originalInput ready) (old.cut.depth + 3)).account

theorem original_full_state :
    (originalAccount ready).current = Financial.Family.Embedding.state sources (originalInput ready)
      (Financial.accountAt (originalInput ready) (old.cut.depth + 3)).current :=
  Financial.Family.Embedding.accountAt_full_state sources _ _

theorem original_full_history :
    (originalAccount ready).current.history =
      (Financial.accountAt (originalInput ready) (old.cut.depth + 3)).current.history.map
        (Financial.Family.Embedding.record sources (originalInput ready)) :=
  Financial.Family.Embedding.accountAt_full_history sources _ _

theorem original_complete_matrix :
    Financial.Family.ledgerClaims sources (originalAccount ready).current =
      Financial.BalanceConservation.ledgerClaims (originalInput ready)
        (Financial.accountAt (originalInput ready) (old.cut.depth + 3)).current := by
  rw [original_full_state]
  exact Financial.Family.Embedding.state_matrix sources _ _

theorem every_original_native_claim_is_literal :
    (originalAccount ready).current.slots.map (Financial.Family.slotClaim sources) =
      ((Financial.accountAt (originalInput ready) (old.cut.depth + 3)).current.slots.map
        (Financial.slotClaim (originalInput ready))).map (Sigma.mk (originalInput ready)) :=
  Financial.Family.Embedding.accountAt_complete_claims sources _ _

def initial (inputs : List (List Action)) : Account :=
  Financial.Family.continueVisits sources (OutstandingSource.History.input (epochSource ready) inputs)
    0 (inputs.length + 2) (originalAccount ready)

def append (inputs : List (List Action)) (word : List Action) (state : Account) : Account :=
  Financial.Family.consumeVisit sources (OutstandingSource.History.input (epochSource ready) (inputs ++ [word]))
    (inputs.length + 2) state

inductive Generated (originInputs : List (List Action)) : List (List Action) → Account → Type
  | initial : Generated originInputs originInputs (initial ready originInputs)
  | submit {inputs state} (prior : Generated originInputs inputs state) (word : List Action) :
      Generated originInputs (inputs ++ [word]) (append ready inputs word state)

def appendTrace (inputs : List (List Action)) (word : List Action) (state : Account) :=
  Financial.Family.instructionTrace sources
    (Financial.Family.visitOrigins sources (OutstandingSource.History.input (epochSource ready) (inputs ++ [word]))
      (inputs.length + 2)) state

def appendRun (inputs : List (List Action)) (word : List Action) (state : Account) :
    (Financial.Family.process sources).Run state.current (append ready inputs word state).current :=
  Financial.Family.visitRun sources _ _ _

theorem initial_keeps_the_complete_original_issues (inputs : List (List Action)) :
    ((Financial.accountAt (originalInput ready) (old.cut.depth + 3)).current.slots.map
      (Financial.slotClaim (originalInput ready))).map (Sigma.mk (originalInput ready)) <+:
      (initial ready inputs).current.slots.map (Financial.Family.slotClaim sources) := by
  rw [← every_original_native_claim_is_literal ready]
  exact Financial.Family.continueVisits_preserves_original_claims sources _ _ _ _

theorem append_issues_only_actual_new_claims (inputs : List (List Action)) (word : List Action) (state : Account) :
    (append ready inputs word state).current.slots.map (Financial.Family.slotClaim sources) =
      state.current.slots.map (Financial.Family.slotClaim sources) ++
        (Financial.Family.visitOrigins sources
          (OutstandingSource.History.input (epochSource ready) (inputs ++ [word])) (inputs.length + 2)).filterMap
            (Financial.Family.originsClaim? sources) :=
  Financial.Family.origins_exact_claims sources _ _

theorem Generated.keeps_every_complete_original_claim {originInputs inputs : List (List Action)} {state : Account}
    (generated : Generated ready originInputs inputs state) :
    ((Financial.accountAt (originalInput ready) (old.cut.depth + 3)).current.slots.map
      (Financial.slotClaim (originalInput ready))).map (Sigma.mk (originalInput ready)) <+:
      state.current.slots.map (Financial.Family.slotClaim sources) := by
  induction generated with
  | initial => exact initial_keeps_the_complete_original_issues ready _
  | submit prior word ih => exact ih.trans (Financial.Family.consumeOrigins_preserves_original_claims sources _ _)

def oldDebtContinuation (inputs : List (List Action)) (word : List Action) (state : Account)
    (index : Nat) (slot : ObligationSlot (Financial.Family.vocabulary sources))
    (present : state.current.slots[index]? = some slot) :=
  Financial.Family.Migration.follow sources (appendRun ready inputs word state) index slot present

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Finance
