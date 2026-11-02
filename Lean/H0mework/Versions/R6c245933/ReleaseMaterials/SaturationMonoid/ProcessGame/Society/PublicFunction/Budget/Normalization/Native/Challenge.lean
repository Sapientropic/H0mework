import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Normalization.Native.Grant
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Normalization.RawAuthority.Trace
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.LocalLifecycle
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.ChallengeLifecycle

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Normalization.NativeTransport

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Authority.Trace Mandate.Challenge

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (input : Input model.source.code) (cut : Nat) (raw : List (Option model.source.code.Policy))
  (party : Party) (good : Good)
  (floor : Gross.Floor model.source.code.law party good model.source.code.actions) (budget : ℚ)
  (rival : Opponent model.source.code)
  (paid : Source.Paid model.source input cut raw (Cut.horizon model.source input cut) party good budget rival)
  (active : model.source.feedback? = some input) (empty : model.source.continuation = [])

abbrev representative := Source.term model.source cut raw (floor.cap budget) (Cut.horizon model.source input cut)

include active in
private theorem inherited_within (record : RawAuthority.ChallengeAtArrival model cut) :
    Cross.Programme.Within (Native.Authority.programme model) (Cut.start model.source cut)
      (RawAuthority.inheritedChallenge model input cut rival raw active record) := by
  unfold RawAuthority.inheritedChallenge
  exact ChallengeLifecycle.transport_within (Native.Authority.programme model) _ _ _ _

include active in
private theorem inherited_match (record : RawAuthority.ChallengeAtArrival model cut) :
    ChallengeLifecycle.Match model.source.code (Native.Authority.programme model)
      (RawAuthority.inheritedChallenge model input cut rival raw active record)
      (RawAuthority.inheritedChallenge model input cut rival (representative model input cut raw party good floor budget) active record) := by
  have original := Cross.Programme.record_is_its_actual_prefix (Native.Authority.programme model)
    (Cut.start model.source cut) record.val record.property
  have within : Cross.Programme.Within (Native.Authority.programme model) (Cut.start model.source cut)
      (Cross.History.inherit (Native.Authority.programme model) record.val.2) := by
    apply Cross.Programme.inherit_within
    rw [original.2]
    exact Cross.Programme.local_through_within _ _ _ _ original.1 (Nat.le_refl _)
  unfold RawAuthority.inheritedChallenge
  exact ChallengeLifecycle.transport_seeds_match model.source.code (Native.Authority.programme model)
    (inputs := Native.Authority.sourceIndex (RawAuthority.candidate model input cut rival raw))
    (nextInputs := Native.Authority.sourceIndex (RawAuthority.candidate model input cut rival (representative model input cut raw party good floor budget)))
    (Cross.History.inherit (Native.Authority.programme model) record.val.2) (Cut.start model.source cut) within rfl rfl
    (Future.prior_raw_event model.source input cut rival raw active)
    (Future.prior_raw_event model.source input cut rival (representative model input cut raw party good floor budget) active)

include paid active empty in
theorem original_challenge_lifecycle (record : RawAuthority.ChallengeAtArrival model cut) :
    ChallengeLifecycle.Match model.source.code (Native.Authority.programme model)
      (Cross.Programme.continueFrom (Native.Authority.programme model)
        (RawAuthority.inheritedChallenge model input cut rival raw active record)
        (Cut.start model.source cut) (Cut.horizon model.source input cut))
      (Cross.Programme.continueFrom (Native.Authority.programme model)
        (RawAuthority.inheritedChallenge model input cut rival (representative model input cut raw party good floor budget) active record)
        (Cut.start model.source cut) (Cut.horizon model.source input cut)) := by
  apply ChallengeLifecycle.continue_match model.source.code (Native.Authority.programme model)
    (inputs := Native.Authority.sourceIndex (RawAuthority.candidate model input cut rival raw))
    (nextInputs := Native.Authority.sourceIndex (RawAuthority.candidate model input cut rival (representative model input cut raw party good floor budget)))
    (Cut.finish model.source input cut) rfl
    (events model input cut raw (Cut.horizon model.source input cut) party good floor budget rival paid active empty)
    (Cut.start model.source cut) (Cut.horizon model.source input cut) (Nat.le_refl _)
    _ _ (inherited_match model input cut raw party good floor budget rival active record)
  exact ChallengeLifecycle.within_mono (Native.Authority.programme model) (Cut.start model.source cut) (Cut.finish model.source input cut)
    (by simp only [Cut.finish];omega) _ (inherited_within model input cut raw rival active record)

include paid active empty in
theorem original_challenge_manifest :
    (RawAuthority.manifest model input cut rival (representative model input cut raw party good floor budget) active).originalChallenges =
      (RawAuthority.manifest model input cut rival raw active).originalChallenges := by
  simp only [RawAuthority.manifest,RawAuthority.challengeContinuations,List.map_map]
  change (Native.Authority.challengesAt model (Cut.start model.source cut)).attach.map
      (fun record => (challengeImage model.source.code (Native.Authority.programme model) (Native.Authority.sourceIndex model) record.val.1,
        challengeStateImage model.source.code (Native.Authority.programme model) (Native.Authority.sourceIndex model) record.val.2.state.current,
        challengeStateImage model.source.code (Native.Authority.programme model) (Native.Authority.sourceIndex model)
          (Cross.Programme.continueFrom (Native.Authority.programme model)
            (RawAuthority.inheritedChallenge model input cut rival (representative model input cut raw party good floor budget) active record)
            (Cut.start model.source cut) (Cut.horizon model.source input cut)).state.current)) = _
  apply List.map_congr_left
  intro record _
  exact congrArg (fun image => (challengeImage model.source.code (Native.Authority.programme model) (Native.Authority.sourceIndex model) record.val.1,
    challengeStateImage model.source.code (Native.Authority.programme model) (Native.Authority.sourceIndex model) record.val.2.state.current,image))
    (original_challenge_lifecycle model input cut raw party good floor budget rival paid active empty record).state

include paid active empty in
theorem complete_candidate_challenge_manifest :
    (RawAuthority.manifest model input cut rival (representative model input cut raw party good floor budget) active).candidateChallenges =
      (RawAuthority.manifest model input cut rival raw active).candidateChallenges :=
  LocalLifecycle.census_images model.source.code (Native.Authority.programme model)
    (inputs := Native.Authority.sourceIndex (RawAuthority.candidate model input cut rival raw))
    (nextInputs := Native.Authority.sourceIndex (RawAuthority.candidate model input cut rival (representative model input cut raw party good floor budget)))
    (Cut.finish model.source input cut) rfl
    (events model input cut raw (Cut.horizon model.source input cut) party good floor budget rival paid active empty)
    (Cut.finish model.source input cut) (Nat.le_refl _)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Normalization.NativeTransport
