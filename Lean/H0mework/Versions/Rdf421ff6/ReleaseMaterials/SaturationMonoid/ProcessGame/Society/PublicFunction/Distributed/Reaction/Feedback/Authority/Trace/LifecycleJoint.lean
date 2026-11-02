import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.ChallengeLifecycle

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Mandate.Challenge

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (input : Input bound.source.code) (cut : Nat) (rival : Opponent bound.source.code)
  (term : Cut.Term bound.source input cut)
  (active : bound.source.feedback? = some input) (empty : bound.source.continuation = [])

def continuedChallenge (record : ChallengeAtArrival bound cut) :=
  Cross.Programme.continueFrom (Native.Authority.programme bound)
    (inheritedChallenge bound input cut rival term active record) (Cut.start bound.source cut) (Cut.horizon bound.source input cut)

def JointChallengeLifecycleAgreement (record : ChallengeAtArrival bound cut) : Prop :=
  ChallengeLifecycle.Match bound.source.code (Native.Authority.programme bound)
    (continuedChallenge bound input cut rival term active record)
    (continuedChallenge bound input cut (Future.jointOpponent bound.source input cut rival) term active record)

include active in
private theorem inherited_challenge_within (record : ChallengeAtArrival bound cut) :
    Cross.Programme.Within (Native.Authority.programme bound) (Cut.start bound.source cut)
      (inheritedChallenge bound input cut rival term active record) := by
  unfold inheritedChallenge
  exact ChallengeLifecycle.transport_within (Native.Authority.programme bound) _ _ _ _

include active in
private theorem inherited_challenges_match (record : ChallengeAtArrival bound cut) :
    ChallengeLifecycle.Match bound.source.code (Native.Authority.programme bound)
      (inheritedChallenge bound input cut rival term active record)
      (inheritedChallenge bound input cut (Future.jointOpponent bound.source input cut rival) term active record) := by
  have original := Cross.Programme.record_is_its_actual_prefix (Native.Authority.programme bound)
    (Cut.start bound.source cut) record.val record.property
  have within : Cross.Programme.Within (Native.Authority.programme bound) (Cut.start bound.source cut)
      (Cross.History.inherit (Native.Authority.programme bound) record.val.2) := by
    apply Cross.Programme.inherit_within
    rw [original.2]
    exact Cross.Programme.local_through_within _ _ _ _ original.1 (Nat.le_refl _)
  unfold inheritedChallenge
  exact ChallengeLifecycle.transport_seeds_match bound.source.code (Native.Authority.programme bound)
    (inputs := Native.Authority.sourceIndex (candidate bound input cut rival term))
    (nextInputs := Native.Authority.sourceIndex (candidate bound input cut (Future.jointOpponent bound.source input cut rival) term))
    (Cross.History.inherit (Native.Authority.programme bound) record.val.2) (Cut.start bound.source cut) within rfl rfl
    (Future.prior_raw_event bound.source input cut rival term.val active)
    (Future.prior_raw_event bound.source input cut (Future.jointOpponent bound.source input cut rival) term.val active)

include active empty in
theorem joint_original_challenge_lifecycle (record : ChallengeAtArrival bound cut) :
    JointChallengeLifecycleAgreement bound input cut rival term active record := by
  apply ChallengeLifecycle.continue_match bound.source.code (Native.Authority.programme bound)
    (inputs := Native.Authority.sourceIndex (candidate bound input cut rival term))
    (nextInputs := Native.Authority.sourceIndex (candidate bound input cut (Future.jointOpponent bound.source input cut rival) term))
    (Cut.finish bound.source input cut) rfl (joint_prior_events bound input cut rival term active empty)
    (Cut.start bound.source cut) (Cut.horizon bound.source input cut) (Nat.le_refl _)
    _ _ (inherited_challenges_match bound input cut rival term active record)
  exact ChallengeLifecycle.within_mono (Native.Authority.programme bound) (Cut.start bound.source cut) (Cut.finish bound.source input cut)
    (by simp only [Cut.finish]; omega) _ (inherited_challenge_within bound input cut rival term active record)

include active empty in
theorem joint_original_challenge_manifest :
    (generate bound input cut (Future.jointOpponent bound.source input cut rival) term active).originalChallenges =
      (generate bound input cut rival term active).originalChallenges := by
  simp only [generate, challengeContinuations, List.map_map]
  change (Native.Authority.challengesAt bound (Cut.start bound.source cut)).attach.map
      (fun record => (challengeImage bound.source.code (Native.Authority.programme bound) (Native.Authority.sourceIndex bound) record.val.1,
        challengeStateImage bound.source.code (Native.Authority.programme bound) (Native.Authority.sourceIndex bound) record.val.2.state.current,
        challengeStateImage bound.source.code (Native.Authority.programme bound) (Native.Authority.sourceIndex bound)
          (continuedChallenge bound input cut (Future.jointOpponent bound.source input cut rival) term active record).state.current)) =
    (Native.Authority.challengesAt bound (Cut.start bound.source cut)).attach.map
      (fun record => (challengeImage bound.source.code (Native.Authority.programme bound) (Native.Authority.sourceIndex bound) record.val.1,
        challengeStateImage bound.source.code (Native.Authority.programme bound) (Native.Authority.sourceIndex bound) record.val.2.state.current,
        challengeStateImage bound.source.code (Native.Authority.programme bound) (Native.Authority.sourceIndex bound)
          (continuedChallenge bound input cut rival term active record).state.current))
  apply List.map_congr_left
  intro record _
  exact congrArg (fun image => (challengeImage bound.source.code (Native.Authority.programme bound) (Native.Authority.sourceIndex bound) record.val.1,
    challengeStateImage bound.source.code (Native.Authority.programme bound) (Native.Authority.sourceIndex bound) record.val.2.state.current, image))
    (joint_original_challenge_lifecycle bound input cut rival term active empty record).state

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace
