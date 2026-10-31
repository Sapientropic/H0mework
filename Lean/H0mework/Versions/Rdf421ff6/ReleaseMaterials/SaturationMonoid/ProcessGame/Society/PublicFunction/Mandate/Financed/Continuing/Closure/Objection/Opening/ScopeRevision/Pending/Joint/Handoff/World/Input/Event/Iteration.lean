import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Runtime

/-! Each observed primitive event re-enters its actual after-cut's own root.
The finite history is consumed incrementally; no future successes are supplied. -/
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Iteration
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch)

def seed := (Replacement.Runtime.fromRoot inventory).packet

def seedEvolution : Evolution ⟨epoch,inventory⟩ (seed inventory) :=
  completionEvolution (Replacement.Runtime.fromRoot inventory).original.decision

def after (history : List (List Action)) := Event.run (seed inventory) history

def native (history : List (List Action)) : Evolution ⟨epoch,inventory⟩ (after inventory history) :=
  .append (seedEvolution inventory) (runEvolution (seed inventory) history)

def finance (history : List (List Action)) :
    (Financial.Family.process sources).Run inventory.finance.current (after inventory history).2.finance.current :=
  (Replacement.Runtime.fromRoot inventory).financialRun.concatRuns _ (runFinance (seed inventory) history)

def atCut (history : List (List Action)) (word : List Action) := Runtime.fromRoot (after inventory history).2 word

theorem every_actual_event_reenters_its_own_response_root (history : List (List Action)) (word : List Action) :
    atCut inventory history word = Event.produce (after inventory history).2 word ∧
    Financial.Family.ledgerClaims sources (atCut inventory history word).packet.2.finance.current =
      (current (atCut inventory history word).packet.1 (atCut inventory history word).packet.2.inputs).claims :=
  ⟨rfl,(atCut inventory history word).packet.2.matrix⟩

def oldGrant (history : List (List Action)) (entry : GrantCohort) (member : entry ∈ inventory.pastGrants) :=
  (native inventory history).grant entry member

def oldChallenge (history : List (List Action)) (entry : ChallengeCohort epoch.scope) (member : entry ∈ inventory.pastChallenges) :=
  (native inventory history).challenge entry member

def oldService (history : List (List Action)) (entry : ServiceCohort epoch.source.seed.initial.clock) (member : entry ∈ inventory.pastServices) :=
  (native inventory history).service entry member

/-- This also tracks every newborn row present at any earlier actual cut. -/
def between (earlier later : List (List Action)) :
    Evolution (after inventory earlier) (after inventory (earlier ++ later)) := by
  change Evolution (Event.run (seed inventory) earlier) (Event.run (seed inventory) (earlier ++ later))
  rw [Event.run_append]
  exact runEvolution (after inventory earlier) later

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Iteration
