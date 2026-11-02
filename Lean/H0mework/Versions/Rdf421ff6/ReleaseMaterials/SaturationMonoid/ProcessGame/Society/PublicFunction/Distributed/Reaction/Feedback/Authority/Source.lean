import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.LocalJoint
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.Compare
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.Selection.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Migration.Challenge

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (input : Input bound.source.code) (cut : Nat)

variable (active : bound.source.feedback? = some input) (empty : bound.source.continuation = [])

structure Disposition where
  feedback : Runtime.Disposition bound.source input cut
  feedback_exact : feedback = Runtime.generate bound.source input active empty cut
  current : Native.Authority.FullDisposition bound (bound.source.history.length + 1 + cut)
  current_exact : current = Native.Authority.fullGenerate bound (bound.source.history.length + 1 + cut)
  candidates : (rival : Opponent bound.source.code) → (term : Cut.Term bound.source input cut) →
    Native.Authority.FullDisposition (candidate bound input cut rival term) (terminalDepth bound input cut)
  candidates_exact : ∀ rival term, candidates rival term =
    Native.Authority.fullGenerate (candidate bound input cut rival term) (terminalDepth bound input cut)
  grants : (rival : Opponent bound.source.code) → (term : Cut.Term bound.source input cut) →
    List (GrantContinuation bound input cut rival term active)
  grants_exact : ∀ rival term, grants rival term = grantContinuations bound input cut rival term active
  challenges : (rival : Opponent bound.source.code) → (term : Cut.Term bound.source input cut) →
    List (ChallengeContinuation bound input cut rival term active)
  challenges_exact : ∀ rival term, challenges rival term = challengeContinuations bound input cut rival term active
  traces : (rival : Opponent bound.source.code) → (term : Cut.Term bound.source input cut) →
    Trace.Manifest Party Good Port Technology Instrument
  traces_exact : ∀ rival term, traces rival term = Trace.generate bound input cut rival term active
  worlds_joint : ∀ rival term, (traces (Future.jointOpponent bound.source input cut rival) term).worlds = (traces rival term).worlds
  grants_joint : ∀ rival term (record : GrantAtArrival bound cut), Trace.JointGrantAgreement bound input cut rival term active record
  challenge_births_joint : ∀ rival term,
    (traces (Future.jointOpponent bound.source input cut rival) term).candidateChallenges.map Prod.fst =
      (traces rival term).candidateChallenges.map Prod.fst
  challenge_reads_joint : ∀ rival term, Trace.JointChallengeReads bound input cut rival term active empty
  challenges_joint : ∀ rival term (record : ChallengeAtArrival bound cut),
    Trace.JointChallengeLifecycleAgreement bound input cut rival term active record
  candidate_grants_joint : ∀ rival term,
    (traces (Future.jointOpponent bound.source input cut rival) term).candidateGrants =
      (traces rival term).candidateGrants
  traces_joint : ∀ rival term, traces (Future.jointOpponent bound.source input cut rival) term = traces rival term
  candidate_challenge_lifecycles_joint : ∀ rival term
    (claim : Native.Authority.Challenge (candidate bound input cut rival term))
    (inside : claim.position.ordinal < Cut.finish bound.source input cut),
    Trace.JointCandidateChallengeAgreement bound input cut rival term active empty claim inside
  selection : (reference : Cut.Term bound.source input cut) → Trace.Selection.Disposition bound input cut active reference
  selection_exact : ∀ reference, selection reference = Trace.Selection.generateSelection bound input cut active empty reference

def generate : Disposition bound input cut active empty :=
  ⟨Runtime.generate bound.source input active empty cut, rfl,
    Native.Authority.fullGenerate bound _, rfl,
    (fun rival term => Native.Authority.fullGenerate (candidate bound input cut rival term) _), fun _ _ => rfl,
    (fun rival term => grantContinuations bound input cut rival term active), fun _ _ => rfl,
    (fun rival term => challengeContinuations bound input cut rival term active), fun _ _ => rfl,
    (fun rival term => Trace.generate bound input cut rival term active), fun _ _ => rfl,
    (fun rival term => Trace.joint_world_images bound input cut rival term active empty),
    (fun rival term record => Trace.joint_original_grant_state_and_receipts bound input cut rival term active empty record),
    (fun rival term => Trace.joint_candidate_challenge_births bound input cut rival term active empty),
    (fun rival term => Trace.joint_challenge_reads bound input cut rival term active empty),
    (fun rival term record => Trace.joint_original_challenge_lifecycle bound input cut rival term active empty record),
    (fun rival term => Trace.joint_candidate_grant_manifest bound input cut rival term active empty),
    (fun rival term => Trace.joint_complete_manifest bound input cut rival term active empty),
    (fun rival term claim inside => Trace.joint_candidate_challenge_lifecycle bound input cut rival term active empty claim inside),
    (fun reference => Trace.Selection.generateSelection bound input cut active empty reference), fun _ => rfl⟩

theorem generated_migrations_preserve_both_original_censuses
    (rival : Opponent bound.source.code) (term : Cut.Term bound.source input cut) :
    ((generate bound input cut active empty).grants rival term).map (fun record => record.original.val) =
        Native.Authority.recordsAt bound (arrivalDepth bound cut) ∧
      ((generate bound input cut active empty).challenges rival term).map (fun record => record.original.val) =
        Native.Authority.challengesAt bound (Cut.start bound.source cut) :=
  ⟨grant_migration_keeps_the_entire_original_census bound input cut rival term active,
    challenge_migration_keeps_the_entire_original_census bound input cut rival term active⟩

theorem each_candidate_reads_its_own_actual_challenge_input
    (rival : Opponent bound.source.code) (term : Cut.Term bound.source input cut) :
    Mandate.Challenge.I (Native.Authority.programme (candidate bound input cut rival term))
      (Native.Authority.sourceIndex (candidate bound input cut rival term)) =
      (Cut.machine bound.source input cut rival term).input := rfl

theorem every_candidate_challenge_is_consumed
    (rival : Opponent bound.source.code) (term : Cut.Term bound.source input cut)
    (position : Mandate.Challenge.Position (Native.Authority.programme (candidate bound input cut rival term))
      (Native.Authority.sourceIndex (candidate bound input cut rival term)))
    (claim : Native.Authority.Challenge (candidate bound input cut rival term))
    (decoded : Mandate.Challenge.read (Native.Authority.programme (candidate bound input cut rival term))
      (Native.Authority.sourceIndex (candidate bound input cut rival term)) position = some claim)
    (inside : position.ordinal < terminalDepth bound input cut + 2) :
    (⟨claim, Mandate.Challenge.through (Native.Authority.programme (candidate bound input cut rival term))
      (Native.Authority.sourceIndex (candidate bound input cut rival term)) claim
      (terminalDepth bound input cut + 2)⟩ : Sigma fun claim : Native.Authority.Challenge (candidate bound input cut rival term) =>
        Native.Authority.ChallengeHistory (candidate bound input cut rival term) claim) ∈
      ((generate bound input cut active empty).candidates rival term).challenges :=
  Native.Authority.every_actual_signed_challenge_is_natively_admitted _ position claim decoded _ inside

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority
