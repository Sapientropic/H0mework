import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.Challenge
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.GrantTransport

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

structure GrantImage (Party Good Port Technology Instrument : Type) where
  birth : Nat
  proposal : ItemImage Party Good Port (Mandate.State Party Technology) Instrument
  acceptance : ItemImage Party Good Port (Mandate.State Party Technology) Instrument
  initial : GrantObligationImage Party Port
  final : GrantObligationImage Party Port
  history : List (GrantRecordImage Party Good Port Technology Instrument)
  deriving DecidableEq

variable (bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

def grantImage (birth last : Nat) (record : Native.Authority.TracedGrant bound birth last) :
    GrantImage Party Good Port Technology Instrument :=
  ⟨birth, itemImage bound.source.code record.admission.grant.proposal.item.val,
    itemImage bound.source.code record.admission.grant.acceptance.item.val,
    grantObligationImage (Mandate.Lifecycle.original bound.base bound.scope
      (Native.Authority.currentAt bound) (Native.Authority.wordAt bound) birth record.admission.grant),
    grantObligationImage record.continuation.obligation, grantHistoryImage bound.source.code record.continuation⟩

variable (input : Input bound.source.code) (cut : Nat) (rival : Opponent bound.source.code)
  (term : Cut.Term bound.source input cut) (active : bound.source.feedback? = some input)

def continuedGrantImage (record : GrantAtArrival bound cut) : GrantImage Party Good Port Technology Instrument :=
  grantImage (candidate bound input cut rival term) record.val.1.val (terminalDepth bound input cut)
    (Native.Authority.traceGrant (candidate bound input cut rival term) record.val.1.val (terminalDepth bound input cut)
      (migratedGrant bound input cut rival term active record))

def worlds : List (Identity.OccurrenceImage Party Good Port (Mandate.State Party Technology) Instrument) :=
  (List.range (Cut.finish bound.source input cut)).map fun ordinal =>
    Identity.occurrenceImage bound.source.code (candidate bound input cut rival term).source.input
      (ProgrammeHistory.visitAt (candidate bound input cut rival term).source.input ordinal).current

structure Manifest (Party Good Port Technology Instrument : Type) where
  worlds : List (Identity.OccurrenceImage Party Good Port (Mandate.State Party Technology) Instrument)
  originalGrants : List (GrantImage Party Good Port Technology Instrument × GrantImage Party Good Port Technology Instrument)
  originalChallenges : List (ChallengeImage Party Good Port Technology Instrument ×
    ChallengeStateImage Party Good Port Technology Instrument × ChallengeStateImage Party Good Port Technology Instrument)
  candidateGrants : List (GrantImage Party Good Port Technology Instrument)
  candidateChallenges : List (ChallengeImage Party Good Port Technology Instrument × ChallengeStateImage Party Good Port Technology Instrument)
  deriving DecidableEq

def generate : Manifest Party Good Port Technology Instrument where
  worlds := worlds bound input cut rival term
  originalGrants := (grantContinuations bound input cut rival term active).map fun record =>
    (grantImage bound record.original.val.1.val _ record.original.val.2,
      grantImage (candidate bound input cut rival term) record.original.val.1.val _ record.after)
  originalChallenges := (challengeContinuations bound input cut rival term active).map fun record =>
    (challengeImage bound.source.code (Native.Authority.programme bound) (Native.Authority.sourceIndex bound) record.original.val.1,
      challengeStateImage bound.source.code (Native.Authority.programme bound) (Native.Authority.sourceIndex bound) record.original.val.2.state.current,
      challengeStateImage bound.source.code (Native.Authority.programme bound) (Native.Authority.sourceIndex bound) record.after.state.current)
  candidateGrants := (Native.Authority.recordsAt (candidate bound input cut rival term) (terminalDepth bound input cut)).map fun record =>
    grantImage (candidate bound input cut rival term) record.1.val _ record.2
  candidateChallenges := (Native.Authority.challengesAt (candidate bound input cut rival term) (Cut.finish bound.source input cut)).map fun record =>
    (challengeImage bound.source.code (Native.Authority.programme bound) (Native.Authority.sourceIndex (candidate bound input cut rival term)) record.1,
      challengeStateImage bound.source.code (Native.Authority.programme bound) (Native.Authority.sourceIndex (candidate bound input cut rival term)) record.2.state.current)

theorem worlds_keep_every_actual_instruction (ordinal : Nat) (inside : ordinal < Cut.finish bound.source input cut) :
    (worlds bound input cut rival term)[ordinal]? = some
      (Identity.occurrenceImage bound.source.code (candidate bound input cut rival term).source.input
        (ProgrammeHistory.visitAt (candidate bound input cut rival term).source.input ordinal).current) := by
  simp only [worlds, List.getElem?_map, List.getElem?_range inside, Option.map_some]

/-- Missing or reordered records are checked against a fresh read of the actual native producer. -/
def verify (supplied : Manifest Party Good Port Technology Instrument) : Bool :=
  decide (supplied = generate bound input cut rival term active)

theorem verify_iff (supplied : Manifest Party Good Port Technology Instrument) :
    verify bound input cut rival term active supplied = true ↔ supplied = generate bound input cut rival term active := by
  simp only [verify, decide_eq_true_eq]

theorem replay_accepts_generated_manifest :
    verify bound input cut rival term active (generate bound input cut rival term active) = true :=
  (verify_iff bound input cut rival term active _).mpr rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace
