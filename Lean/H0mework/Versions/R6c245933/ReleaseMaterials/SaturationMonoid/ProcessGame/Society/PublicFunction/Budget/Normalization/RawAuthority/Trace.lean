import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Normalization.RawAuthority.Migration.Grant
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Normalization.RawAuthority.Migration.Challenge
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Normalization.RawAuthority

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Authority.Trace

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (input : Input model.source.code) (cut : Nat) (rival : Opponent model.source.code)
  (raw : List (Option model.source.code.Policy)) (active : model.source.feedback? = some input)

/-- The complete native manifest reads the actual raw emitter, without an old-cap certificate. -/
def manifest : Manifest Party Good Port Technology Instrument where
  worlds := (List.range (Cut.finish model.source input cut)).map fun ordinal =>
    Identity.occurrenceImage model.source.code (candidate model input cut rival raw).source.input
      (ProgrammeHistory.visitAt (candidate model input cut rival raw).source.input ordinal).current
  originalGrants := (grantContinuations model input cut rival raw active).map fun record =>
    (grantImage model record.original.val.1.val _ record.original.val.2,
      grantImage (candidate model input cut rival raw) record.original.val.1.val _ record.after)
  originalChallenges := (challengeContinuations model input cut rival raw active).map fun record =>
    (challengeImage model.source.code (Native.Authority.programme model) (Native.Authority.sourceIndex model) record.original.val.1,
      challengeStateImage model.source.code (Native.Authority.programme model) (Native.Authority.sourceIndex model) record.original.val.2.state.current,
      challengeStateImage model.source.code (Native.Authority.programme model) (Native.Authority.sourceIndex model) record.after.state.current)
  candidateGrants := (Native.Authority.recordsAt (candidate model input cut rival raw) (terminalDepth model input cut)).map fun record =>
    grantImage (candidate model input cut rival raw) record.1.val _ record.2
  candidateChallenges := (Native.Authority.challengesAt (candidate model input cut rival raw) (Cut.finish model.source input cut)).map fun record =>
    (challengeImage model.source.code (Native.Authority.programme model) (Native.Authority.sourceIndex (candidate model input cut rival raw)) record.1,
      challengeStateImage model.source.code (Native.Authority.programme model) (Native.Authority.sourceIndex (candidate model input cut rival raw)) record.2.state.current)

def verify (supplied : Manifest Party Good Port Technology Instrument) : Bool :=
  decide (supplied = manifest model input cut rival raw active)

theorem independent_manifest_review (supplied : Manifest Party Good Port Technology Instrument) :
    verify model input cut rival raw active supplied = true ↔ supplied = manifest model input cut rival raw active := by
  simp only [verify,decide_eq_true_eq]

theorem the_raw_manifest_preserves_the_original_complete_manifest
    (term : Cut.Term model.source input cut) :
    manifest model input cut rival term.val active = Authority.Trace.generate model input cut rival term active := by
  apply (Manifest.mk.injEq ..).mpr
  refine ⟨rfl,?_,?_,rfl,rfl⟩
  · simp only [grantContinuations,Authority.grantContinuations,List.map_map,Function.comp_def]
    rfl
  · simp only [challengeContinuations,Authority.challengeContinuations,List.map_map,Function.comp_def]
    rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Normalization.RawAuthority
