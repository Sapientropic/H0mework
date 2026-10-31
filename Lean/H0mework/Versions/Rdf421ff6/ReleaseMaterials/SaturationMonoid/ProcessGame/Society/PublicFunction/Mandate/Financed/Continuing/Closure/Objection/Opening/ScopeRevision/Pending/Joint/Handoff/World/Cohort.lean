import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Continuation.Effects

/-! Heterogeneous past cohorts keep their own origin and small native
process code. A later source supplies actual receipts, never a new identity. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
abbrev Scope := Mandate.Scope (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)

structure Epoch where
  originalScope : Scope
  original : BoundSource base originalScope
  history : List (List Action)
  fresh : Handoff.Ready original history

def Epoch.ofFresh {scope : Scope} {bound : BoundSource base scope} {inputs : List (List Action)}
    (fresh : Handoff.Ready bound inputs) : Epoch := ⟨scope,bound,inputs,fresh⟩

abbrev Epoch.scope (epoch : Epoch) := epoch.fresh.scope
abbrev Epoch.source (epoch : Epoch) := Handoff.source epoch.fresh
abbrev Epoch.bound (epoch : Epoch) := Handoff.newBound epoch.fresh

theorem Epoch.window (epoch : Epoch) : epoch.scope.task.earliest ≤ epoch.scope.task.deadline := by
  change (Handoff.after epoch.original epoch.history).clock + 2 ≤ (Handoff.after epoch.original epoch.history).clock + 3
  exact add_le_add (le_refl _) (by decide : (2 : ℚ) ≤ 3)

abbrev GrantOrigin := Sigma fun epoch : Epoch => Mandate.Challenge.Cross.GrantResident epoch.original epoch.history
abbrev ChallengeOrigin := Sigma fun epoch : Epoch => Mandate.Challenge.Cross.Resident epoch.original epoch.history

structure GrantCohort where
  origin : GrantOrigin
  saved : Continuation.Grant.Saved origin.1.fresh origin.2

def GrantCohort.advance (entry : GrantCohort) (source : Mandate.Challenge.ScopeBoundary.Source base)
    (receipts : List (Mandate.Challenge.ScopeBoundary.Receipt source)) : GrantCohort :=
  ⟨entry.origin,entry.saved.consume source receipts⟩

structure ChallengeCohort (currentScope : Scope) where
  origin : ChallengeOrigin
  saved : Continuation.Challenge.Saved origin.1.fresh origin.2
  later : origin.1.originalScope.task.deadline < currentScope.task.earliest

def ChallengeCohort.advance {currentScope : Scope} (entry : ChallengeCohort currentScope)
    (source : Mandate.Challenge.ScopeBoundary.Source base)
    (follow : currentScope.task.earliest ≤ source.scope.task.earliest)
    (receipts : List (Mandate.Challenge.ScopeBoundary.Receipt source)) : ChallengeCohort source.scope :=
  ⟨entry.origin,entry.saved.consume source (lt_of_lt_of_le entry.later follow) receipts,lt_of_lt_of_le entry.later follow⟩

structure ServiceOrigin where
  source : OutstandingSource Bool Good Mandate.Source.Port (State Bool Unit) Unit
  originInputs : List (List Action)
  inputs : List (List Action)
  index : source.Slot
  original : OutstandingSource.History.NativeService.Thread source originInputs index inputs

structure ServiceCohort (initialClock : ℚ) where
  origin : ServiceOrigin
  saved : OutstandingSource.History.NativeService.Expired.Continuation origin.source origin.original
  expired : origin.source.seed.task.deadline < initialClock

theorem clock_after_initial (source : OutstandingSource Bool Good Mandate.Source.Port (State Bool Unit) Unit)
    (inputs : List (List Action)) (ordinal : Nat) :
    source.seed.initial.clock ≤ (OutstandingSource.History.currentAt source inputs ordinal).clock := by
  induction ordinal with
  | zero => exact le_refl _
  | succ ordinal ih =>
    have step : (OutstandingSource.History.currentAt source inputs ordinal).clock ≤
        (OutstandingSource.History.currentAt source inputs (ordinal + 1)).clock := by
      change (ProgrammeSource.rawCurrent (OutstandingSource.History.input source inputs)
        (ProgrammeHistory.visitAt (OutstandingSource.History.input source inputs) ordinal).current).clock ≤
        (ProgrammeSource.rawCurrent (OutstandingSource.History.input source inputs)
          (ProgrammeSource.next (OutstandingSource.History.input source inputs)
            (ProgrammeHistory.visitAt (OutstandingSource.History.input source inputs) ordinal).current)).clock
      rw [ProgrammeSource.actual_raw_next]
      exact source.seed.law.next_clock_nondecreasing _ _
    exact ih.trans step

def ServiceCohort.observations {initialClock : ℚ} (entry : ServiceCohort initialClock)
    (source : Mandate.Challenge.ScopeBoundary.Source base) (start count : Nat) :=
  (List.range count).filterMap fun offset =>
    OutstandingSource.History.NativeService.ExpiredInput.read entry.origin.source source.bound.source source.inputs (start + offset)

def ServiceCohort.advance {initialClock : ℚ} (entry : ServiceCohort initialClock)
    (source : Mandate.Challenge.ScopeBoundary.Source base) (clock : initialClock ≤ source.bound.source.seed.initial.clock)
    (start count : Nat) : ServiceCohort source.bound.source.seed.initial.clock :=
  ⟨entry.origin,entry.saved.consume entry.origin.source (entry.observations source start count),lt_of_lt_of_le entry.expired clock⟩

theorem ServiceCohort.every_actual_visit_is_present {initialClock : ℚ} (entry : ServiceCohort initialClock)
    (source : Mandate.Challenge.ScopeBoundary.Source base) (clock : initialClock ≤ source.bound.source.seed.initial.clock)
    (start count : Nat) :
    (entry.observations source start count).map OutstandingSource.History.NativeService.ExpiredInput.depth =
      (List.range count).map (fun offset => start + offset) := by
  unfold ServiceCohort.observations
  rw [List.map_filterMap,← List.filterMap_eq_map']
  apply List.filterMap_congr
  intro offset _
  have late := lt_of_lt_of_le (lt_of_lt_of_le entry.expired clock)
    (clock_after_initial source.bound.source source.inputs (start + offset + 1))
  simp only [OutstandingSource.History.NativeService.ExpiredInput.read,dif_pos late,Option.map_some]

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World
