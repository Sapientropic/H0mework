import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Continuation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Successor.StepNative

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Normalization.RawAuthority

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (point : Cursor model.source.code) (fallback : Rule model.source.code)
  (program : Program model.source.code) (environment : Opponent model.source.code)

abbrev before := Replanning.native model point
abbrev target := Replanning.native model (after point fallback program environment 1)
abbrev raw := schedule point fallback program
abbrev control := Programme.controller point fallback program environment
abbrev arrival := arrivalDepth (before model point) point.cut

abbrev actualGrant (record : GrantAtArrival (before model point) point.cut) :=
  migratedGrant (before model point) point.entry point.cut (control model point fallback program environment)
    (raw model point fallback program) rfl record

structure GrantStep where
  original : GrantAtArrival (before model point) point.cut
  after : Native.Authority.TracedGrant (target model point fallback program environment) original.val.1.val (arrival model point+1)
  after_exact : after = Native.Authority.traceGrant (target model point fallback program environment) original.val.1.val
    (arrival model point+1) (actualGrant model point fallback program environment original)

def grantStep (record : GrantAtArrival (before model point) point.cut) : GrantStep model point fallback program environment :=
  ⟨record,Native.Authority.traceGrant (target model point fallback program environment) record.val.1.val
    (arrival model point+1) (actualGrant model point fallback program environment record),rfl⟩

def GrantStep.actualRun (record : GrantStep model point fallback program environment) :
    (Mandate.Lifecycle.Observed.process (base := model.base) (scope := model.scope)
      (currentAt := Native.Authority.currentAt (target model point fallback program environment))
      (wordAt := Native.Authority.wordAt (target model point fallback program environment))
      (birth := record.original.val.1.val) (grant := actualGrant model point fallback program environment record.original)).Run
      record.original.val.2.continuation.state record.after.continuation.state := by
  rw [record.after_exact]
  dsimp only [Native.Authority.traceGrant]
  rw [← migrated_grant_keeps_the_entire_original_cut_state (before model point) point.entry point.cut
    (control model point fallback program environment) (raw model point fallback program) rfl record.original]
  exact Mandate.Lifecycle.Observed.fromActualCut (arrival model point) 1

def grants : List (GrantStep model point fallback program environment) :=
  (Native.Authority.recordsAt (before model point) (arrival model point)).attach.map
    (grantStep model point fallback program environment)

theorem all_original_grants_are_kept :
    (grants model point fallback program environment).map (fun record => record.original.val) =
      Native.Authority.recordsAt (before model point) (arrival model point) := by
  simp [grants,grantStep,List.map_map,Function.comp_def]

abbrev inherited (record : ChallengeAtArrival (before model point) point.cut) :=
  inheritedChallenge (before model point) point.entry point.cut (control model point fallback program environment)
    (raw model point fallback program) rfl record

structure ChallengeStep where
  original : ChallengeAtArrival (before model point) point.cut
  after : Mandate.Challenge.Cross.History (Native.Authority.programme (before model point)) original.val.1
    (Native.Authority.sourceIndex (target model point fallback program environment))
  after_exact : after = Mandate.Challenge.Cross.Programme.continueFrom (Native.Authority.programme (before model point))
    (inherited model point fallback program environment original) (Cut.start point.source point.cut) 1

def challengeStep (record : ChallengeAtArrival (before model point) point.cut) : ChallengeStep model point fallback program environment :=
  ⟨record,Mandate.Challenge.Cross.Programme.continueFrom (Native.Authority.programme (before model point))
    (inherited model point fallback program environment record) (Cut.start point.source point.cut) 1,rfl⟩

def ChallengeStep.actualRun (record : ChallengeStep model point fallback program environment) :
    (Mandate.Challenge.Cross.process (Native.Authority.programme (before model point)) record.original.val.1).Run
      record.original.val.2.state.current record.after.state.current := by
  rw [record.after_exact]
  have generated := Mandate.Challenge.Cross.Programme.continueRun (Native.Authority.programme (before model point))
    (inherited model point fallback program environment record.original) (Cut.start point.source point.cut) 1
  have preserved :
      (inherited model point fallback program environment record.original).state =
        (Mandate.Challenge.Cross.History.inherit (Native.Authority.programme (before model point)) record.original.val.2).state := by
    unfold inherited inheritedChallenge
    exact Mandate.Challenge.Cross.Programme.transport_preserves_the_entire_generated_state
      (Native.Authority.programme (before model point))
      (inputs := Native.Authority.sourceIndex (before model point))
      (nextInputs := Native.Authority.sourceIndex
        (candidate (before model point) point.entry point.cut (control model point fallback program environment)
          (raw model point fallback program)))
      (Cut.start (before model point).source point.cut)
      (prefix_items (before model point) point.entry point.cut (control model point fallback program environment)
        (raw model point fallback program) rfl) _ _
  rw [preserved] at generated
  have inheritedCurrent :
      (Mandate.Challenge.Cross.History.inherit (Native.Authority.programme (before model point)) record.original.val.2).state.current =
        record.original.val.2.state.current := by
    cases record.original.val.2 with
    | closed state archive slots => rfl
    | pending target state slots => cases target <;> rfl
  rw [inheritedCurrent] at generated
  exact generated

theorem ChallengeStep.preserves_the_entire_original_history
    (record : ChallengeStep model point fallback program environment) :
    record.after.state.current.history = record.original.val.2.state.current.history ++
      (record.actualRun model point fallback program environment).events :=
  (record.actualRun model point fallback program environment).history_eq

def challenges : List (ChallengeStep model point fallback program environment) :=
  (Native.Authority.challengesAt (before model point) (Cut.start point.source point.cut)).attach.map
    (challengeStep model point fallback program environment)

theorem all_original_challenges_are_kept :
    (challenges model point fallback program environment).map (fun record => record.original.val) =
      Native.Authority.challengesAt (before model point) (Cut.start point.source point.cut) := by
  simp [challenges,challengeStep,List.map_map,Function.comp_def]

structure Payload where
  grants : List (GrantStep model point fallback program environment)
  grants_exact : grants = StepNative.grants model point fallback program environment
  challenges : List (ChallengeStep model point fallback program environment)
  challenges_exact : challenges = StepNative.challenges model point fallback program environment
  original_grants : grants.map (fun record => record.original.val) = Native.Authority.recordsAt (before model point) (arrival model point)
  original_challenges : challenges.map (fun record => record.original.val) =
    Native.Authority.challengesAt (before model point) (Cut.start point.source point.cut)
  actual_source : (target model point fallback program environment).source = (after point fallback program environment 1).source

def generate : Payload model point fallback program environment :=
  ⟨grants model point fallback program environment,rfl,challenges model point fallback program environment,rfl,
    all_original_grants_are_kept model point fallback program environment,
    all_original_challenges_are_kept model point fallback program environment,rfl⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Successor.StepNative
