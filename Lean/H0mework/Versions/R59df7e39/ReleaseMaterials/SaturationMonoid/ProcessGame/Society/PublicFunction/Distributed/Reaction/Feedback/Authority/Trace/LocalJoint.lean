import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.LocalLifecycle

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

def jointCandidateClaim (claim : Native.Authority.Challenge (candidate bound input cut rival term))
    (inside : claim.position.ordinal < Cut.finish bound.source input cut) :
    Native.Authority.Challenge (candidate bound input cut (Future.jointOpponent bound.source input cut rival) term) :=
  Cross.Programme.replacement (Native.Authority.programme bound)
    (inputs := Native.Authority.sourceIndex (candidate bound input cut rival term))
    (nextInputs := Native.Authority.sourceIndex (candidate bound input cut (Future.jointOpponent bound.source input cut rival) term))
    (Cut.finish bound.source input cut) (joint_challenge_items bound input cut rival term active empty) claim inside

def JointCandidateChallengeAgreement (claim : Native.Authority.Challenge (candidate bound input cut rival term))
    (inside : claim.position.ordinal < Cut.finish bound.source input cut) : Prop :=
  LocalLifecycle.Match bound.source.code (Native.Authority.programme bound)
    (Mandate.Challenge.through (Native.Authority.programme bound)
      (Native.Authority.sourceIndex (candidate bound input cut rival term)) claim (Cut.finish bound.source input cut))
    (Mandate.Challenge.through (Native.Authority.programme bound)
      (Native.Authority.sourceIndex (candidate bound input cut (Future.jointOpponent bound.source input cut rival) term))
      (jointCandidateClaim bound input cut rival term active empty claim inside) (Cut.finish bound.source input cut))

include active empty in
theorem joint_candidate_challenge_lifecycle (claim : Native.Authority.Challenge (candidate bound input cut rival term))
    (inside : claim.position.ordinal < Cut.finish bound.source input cut) :
    JointCandidateChallengeAgreement bound input cut rival term active empty claim inside :=
  LocalLifecycle.through_match bound.source.code (Native.Authority.programme bound)
    (inputs := Native.Authority.sourceIndex (candidate bound input cut rival term))
    (nextInputs := Native.Authority.sourceIndex (candidate bound input cut (Future.jointOpponent bound.source input cut rival) term))
    (Cut.finish bound.source input cut) rfl (joint_prior_events bound input cut rival term active empty)
    (Cut.finish bound.source input cut) (Nat.le_refl _)
    (ChallengeTransport.claim_image bound.source.code (Native.Authority.programme bound)
      (inputs := Native.Authority.sourceIndex (candidate bound input cut rival term))
      (nextInputs := Native.Authority.sourceIndex (candidate bound input cut (Future.jointOpponent bound.source input cut rival) term))
      (Cut.finish bound.source input cut) rfl (joint_prior_events bound input cut rival term active empty) claim inside)

include active empty in
theorem joint_candidate_challenge_manifest :
    (generate bound input cut (Future.jointOpponent bound.source input cut rival) term active).candidateChallenges =
      (generate bound input cut rival term active).candidateChallenges := by
  simp only [generate]
  exact LocalLifecycle.census_images bound.source.code (Native.Authority.programme bound)
    (inputs := Native.Authority.sourceIndex (candidate bound input cut rival term))
    (nextInputs := Native.Authority.sourceIndex (candidate bound input cut (Future.jointOpponent bound.source input cut rival) term))
    (Cut.finish bound.source input cut) rfl (joint_prior_events bound input cut rival term active empty)
    (Cut.finish bound.source input cut) (Nat.le_refl _)

include active empty in
theorem joint_complete_manifest :
    generate bound input cut (Future.jointOpponent bound.source input cut rival) term active =
      generate bound input cut rival term active := by
  apply (Manifest.mk.injEq ..).mpr
  exact ⟨joint_world_images bound input cut rival term active empty,
    joint_original_grant_manifest bound input cut rival term active empty,
    joint_original_challenge_manifest bound input cut rival term active empty,
    joint_candidate_grant_manifest bound input cut rival term active empty,
    joint_candidate_challenge_manifest bound input cut rival term active empty⟩

include active empty in
theorem finite_manifest_relation_iff_every_future_opponent
    (relation : Manifest Party Good Port Technology Instrument → Manifest Party Good Port Technology Instrument → Prop)
    (new old : Cut.Term bound.source input cut) :
    (∀ table ∈ Cut.tables bound.source input cut,
      relation (generate bound input cut (Cut.opponent bound.source input cut table) new active)
        (generate bound input cut (Cut.opponent bound.source input cut table) old active)) ↔
      ∀ actual : Opponent bound.source.code,
        relation (generate bound input cut actual new active) (generate bound input cut actual old active) := by
  constructor
  · intro finite actual
    have checked := finite (Residual.restrict bound.source.code (Residual.seed bound.source input cut)
      (Residual.schedules bound.source input cut) actual)
      (Residual.restriction_is_generated bound.source.code (Residual.seed bound.source input cut)
        (Residual.schedules bound.source input cut) actual)
    change relation (generate bound input cut (Future.jointOpponent bound.source input cut actual) new active)
      (generate bound input cut (Future.jointOpponent bound.source input cut actual) old active) at checked
    rw [joint_complete_manifest bound input cut actual new active empty,
      joint_complete_manifest bound input cut actual old active empty] at checked
    exact checked
  · intro all table _
    exact all (Cut.opponent bound.source input cut table)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace
