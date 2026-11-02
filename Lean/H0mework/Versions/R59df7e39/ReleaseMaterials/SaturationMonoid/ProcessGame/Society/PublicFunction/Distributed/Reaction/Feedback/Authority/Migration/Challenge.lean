import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Prefix
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Cross.Programme

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (input : Input bound.source.code) (cut : Nat)
  (rival : Opponent bound.source.code) (term : Cut.Term bound.source input cut)
  (active : bound.source.feedback? = some input)

abbrev OriginalChallenge := Sigma fun claim : Native.Authority.Challenge bound => Native.Authority.ChallengeHistory bound claim
abbrev ChallengeAtArrival := {record : OriginalChallenge bound //
  record ∈ Native.Authority.challengesAt bound (Cut.start bound.source cut)}

def inheritedChallenge (record : ChallengeAtArrival bound cut) :
    Mandate.Challenge.Cross.History (Native.Authority.programme bound) record.val.1
      (Native.Authority.sourceIndex (candidate bound input cut rival term)) := by
  have original := Mandate.Challenge.Cross.Programme.record_is_its_actual_prefix
    (Native.Authority.programme bound) (Cut.start bound.source cut) record.val record.property
  apply Mandate.Challenge.Cross.Programme.transportHistory (Native.Authority.programme bound)
    (Cut.start bound.source cut) (prefix_items bound input cut rival term active)
    (Mandate.Challenge.Cross.History.inherit (Native.Authority.programme bound) record.val.2)
  apply Mandate.Challenge.Cross.Programme.inherit_within
  rw [original.2]
  exact Mandate.Challenge.Cross.Programme.local_through_within _ _ _ _ original.1 (Nat.le_refl _)

structure ChallengeContinuation where
  private mk ::
  original : ChallengeAtArrival bound cut
  after : Mandate.Challenge.Cross.History (Native.Authority.programme bound) original.val.1
    (Native.Authority.sourceIndex (candidate bound input cut rival term))
  after_exact : after = Mandate.Challenge.Cross.Programme.continueFrom (Native.Authority.programme bound)
    (inheritedChallenge bound input cut rival term active original) (Cut.start bound.source cut) (Cut.horizon bound.source input cut)

private def carryChallenge (record : ChallengeAtArrival bound cut) : ChallengeContinuation bound input cut rival term active :=
  ⟨record, Mandate.Challenge.Cross.Programme.continueFrom (Native.Authority.programme bound)
    (inheritedChallenge bound input cut rival term active record) (Cut.start bound.source cut) (Cut.horizon bound.source input cut), rfl⟩

def challengeContinuations : List (ChallengeContinuation bound input cut rival term active) :=
  (Native.Authority.challengesAt bound (Cut.start bound.source cut)).attach.map
    (carryChallenge bound input cut rival term active)

def ChallengeContinuation.actualRun (record : ChallengeContinuation bound input cut rival term active) :
    (Mandate.Challenge.Cross.process (Native.Authority.programme bound) record.original.val.1).Run
      record.original.val.2.state.current record.after.state.current := by
  rw [record.after_exact]
  have generated := Mandate.Challenge.Cross.Programme.continueRun (Native.Authority.programme bound)
    (inheritedChallenge bound input cut rival term active record.original)
    (Cut.start bound.source cut) (Cut.horizon bound.source input cut)
  have preserved := Mandate.Challenge.Cross.Programme.transport_preserves_the_entire_generated_state
    (Native.Authority.programme bound) (Cut.start bound.source cut)
    (prefix_items bound input cut rival term active)
    (Mandate.Challenge.Cross.History.inherit (Native.Authority.programme bound) record.original.val.2)
  unfold inheritedChallenge at generated
  rw [preserved] at generated
  have inheritedCurrent :
      (Mandate.Challenge.Cross.History.inherit (Native.Authority.programme bound) record.original.val.2).state.current =
        record.original.val.2.state.current := by
    cases record.original.val.2 with
    | closed state archive slots => rfl
    | pending target state slots => cases target <;> rfl
  rw [inheritedCurrent] at generated
  exact generated

theorem ChallengeContinuation.preserves_the_entire_original_history
    (record : ChallengeContinuation bound input cut rival term active) :
    record.after.state.current.history = record.original.val.2.state.current.history ++
      (record.actualRun bound input cut rival term active).events :=
  (record.actualRun bound input cut rival term active).history_eq

theorem challenge_migration_keeps_the_entire_original_census :
    (challengeContinuations bound input cut rival term active).map (fun record => record.original.val) =
      Native.Authority.challengesAt bound (Cut.start bound.source cut) := by
  simp [challengeContinuations, List.map_map, Function.comp_def, carryChallenge]

theorem carried_challenge_keeps_original_admission_actor_and_scope
    (record : ChallengeContinuation bound input cut rival term active)
    (target : Mandate.Challenge.Cross.Target (Native.Authority.programme bound) record.original.val.1
      (Native.Authority.sourceIndex (candidate bound input cut rival term))) :
    (Mandate.Challenge.Cross.tracked (Native.Authority.programme bound) target).admission =
        (Mandate.Challenge.obligation (Native.Authority.programme bound) (Native.Authority.sourceIndex bound) record.original.val.1).admission ∧
      (Mandate.Challenge.Cross.tracked (Native.Authority.programme bound) target).bearer =
        record.original.val.1.actor (Native.Authority.programme bound) (Native.Authority.sourceIndex bound) ∧
      (Mandate.Challenge.Cross.tracked (Native.Authority.programme bound) target).content = record.original.val.1 ∧
      (Mandate.Challenge.Cross.tracked (Native.Authority.programme bound) target).scope =
        record.original.val.1.origin (Native.Authority.programme bound) (Native.Authority.sourceIndex bound) ∧
      (Mandate.Challenge.Cross.tracked (Native.Authority.programme bound) target).lineage =
        record.original.val.1.origin (Native.Authority.programme bound) (Native.Authority.sourceIndex bound) := ⟨rfl, rfl, rfl, rfl, rfl⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority
