import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.Joint
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.ChallengeTransport

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

include active empty in
theorem joint_prior_events (ordinal : Nat) (inside : ordinal < Cut.finish bound.source input cut) :
    ProgrammeSource.rawEvent (candidate bound input cut (Future.jointOpponent bound.source input cut rival) term).source.input
        (ProgrammeHistory.visitAt (candidate bound input cut rival term).source.input ordinal).current =
      ProgrammeSource.rawEvent (candidate bound input cut rival term).source.input
        (ProgrammeHistory.visitAt (candidate bound input cut rival term).source.input ordinal).current := by
  have actual := Future.joint_occurrences bound.source input cut rival term.val active empty term.property ordinal inside
  exact (congrArg (ProgrammeSource.rawEvent (candidate bound input cut (Future.jointOpponent bound.source input cut rival) term).source.input) actual.1).symm.trans actual.2

include active empty in
theorem joint_challenge_items (ordinal : Nat) (inside : ordinal < Cut.finish bound.source input cut) :
    Institutions.Capitalism.Universal.Source.ProgrammeFace.Registered.traceItems
        (candidate bound input cut (Future.jointOpponent bound.source input cut rival) term).source.input
        (ProgrammeHistory.visitAt (candidate bound input cut (Future.jointOpponent bound.source input cut rival) term).source.input ordinal).current =
      Institutions.Capitalism.Universal.Source.ProgrammeFace.Registered.traceItems (candidate bound input cut rival term).source.input
        (ProgrammeHistory.visitAt (candidate bound input cut rival term).source.input ordinal).current :=
  ChallengeTransport.items (Native.Authority.programme bound) (inputs := Native.Authority.sourceIndex (candidate bound input cut rival term))
    (nextInputs := Native.Authority.sourceIndex (candidate bound input cut (Future.jointOpponent bound.source input cut rival) term)) (Cut.finish bound.source input cut) rfl
    (joint_prior_events bound input cut rival term active empty) ordinal inside

include active empty in
theorem joint_candidate_challenge_births :
    ((generate bound input cut (Future.jointOpponent bound.source input cut rival) term active).candidateChallenges.map Prod.fst) =
      ((generate bound input cut rival term active).candidateChallenges.map Prod.fst) := by
  simp only [generate, List.map_map, Function.comp_def]
  exact ChallengeTransport.census_images bound.source.code (Native.Authority.programme bound) (inputs := Native.Authority.sourceIndex (candidate bound input cut rival term))
    (nextInputs := Native.Authority.sourceIndex (candidate bound input cut (Future.jointOpponent bound.source input cut rival) term))
    (Cut.finish bound.source input cut) rfl (joint_prior_events bound input cut rival term active empty)
    (Cut.finish bound.source input cut) (Nat.le_refl _)

def JointChallengeReadAgreement {originInputs : Native.Authority.Sources bound.base bound.scope}
    (original : Claim (Native.Authority.programme bound) originInputs)
    (target : Cross.Target (Native.Authority.programme bound) original (Native.Authority.sourceIndex (candidate bound input cut rival term)))
    (within : target.claim.position.ordinal < Cut.finish bound.source input cut)
    (position : Position (Native.Authority.programme bound) (Native.Authority.sourceIndex (candidate bound input cut rival term)))
    (inside : position.ordinal < Cut.finish bound.source input cut) : Prop :=
  let common := joint_challenge_items bound input cut rival term active empty
  let nextTarget := Cross.Programme.transportTarget (Native.Authority.programme bound) (inputs := Native.Authority.sourceIndex (candidate bound input cut rival term))
    (nextInputs := Native.Authority.sourceIndex (candidate bound input cut (Future.jointOpponent bound.source input cut rival) term)) (Cut.finish bound.source input cut) common target within
  let nextPosition := Cross.Programme.position (Native.Authority.programme bound) (inputs := Native.Authority.sourceIndex (candidate bound input cut rival term))
    (nextInputs := Native.Authority.sourceIndex (candidate bound input cut (Future.jointOpponent bound.source input cut rival) term)) (Cut.finish bound.source input cut) common position inside
  challengeImage bound.source.code (Native.Authority.programme bound)
      (Native.Authority.sourceIndex (candidate bound input cut (Future.jointOpponent bound.source input cut rival) term)) nextTarget.claim =
    challengeImage bound.source.code (Native.Authority.programme bound) (Native.Authority.sourceIndex (candidate bound input cut rival term)) target.claim ∧
    nextTarget.snapshot (Native.Authority.programme bound) = target.snapshot (Native.Authority.programme bound) ∧
    ChallengeTransport.reconfirmationSource bound.source.code (Native.Authority.programme bound) nextTarget nextPosition =
      ChallengeTransport.reconfirmationSource bound.source.code (Native.Authority.programme bound) target position ∧
    ChallengeTransport.attemptSource bound.source.code (Native.Authority.programme bound) nextTarget nextPosition =
      ChallengeTransport.attemptSource bound.source.code (Native.Authority.programme bound) target position

include active empty in
theorem joint_challenge_read_sources {originInputs : Native.Authority.Sources bound.base bound.scope}
    (original : Claim (Native.Authority.programme bound) originInputs)
    (target : Cross.Target (Native.Authority.programme bound) original (Native.Authority.sourceIndex (candidate bound input cut rival term)))
    (within : target.claim.position.ordinal < Cut.finish bound.source input cut)
    (position : Position (Native.Authority.programme bound) (Native.Authority.sourceIndex (candidate bound input cut rival term)))
    (inside : position.ordinal < Cut.finish bound.source input cut) :
    JointChallengeReadAgreement bound input cut rival term active empty original target within position inside :=
  ChallengeTransport.actual_source_transport bound.source.code (Native.Authority.programme bound) (inputs := Native.Authority.sourceIndex (candidate bound input cut rival term))
    (nextInputs := Native.Authority.sourceIndex (candidate bound input cut (Future.jointOpponent bound.source input cut rival) term))
    (Cut.finish bound.source input cut) rfl (joint_prior_events bound input cut rival term active empty) target within position inside

def JointChallengeReads : Prop :=
  ∀ {originInputs : Native.Authority.Sources bound.base bound.scope}
    (original : Claim (Native.Authority.programme bound) originInputs)
    (target : Cross.Target (Native.Authority.programme bound) original (Native.Authority.sourceIndex (candidate bound input cut rival term)))
    (within : target.claim.position.ordinal < Cut.finish bound.source input cut)
    (position : Position (Native.Authority.programme bound) (Native.Authority.sourceIndex (candidate bound input cut rival term)))
    (inside : position.ordinal < Cut.finish bound.source input cut),
    JointChallengeReadAgreement bound input cut rival term active empty original target within position inside

include active empty in
theorem joint_challenge_reads : JointChallengeReads bound input cut rival term active empty :=
  fun original target within position inside => joint_challenge_read_sources bound input cut rival term active empty original target within position inside

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace
