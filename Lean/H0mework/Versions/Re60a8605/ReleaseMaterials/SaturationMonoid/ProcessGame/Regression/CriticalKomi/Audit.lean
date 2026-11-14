import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.CalculationRuntime
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.CorridorContinuation
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.CorridorPreparation
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.InitialColourPass
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.RegionalProgram

open SaturationMonoid.ProcessGame.Go
open SaturationMonoid.ProcessGame.Go.CriticalKomi

#print axioms CorridorContinuation.wall_reserve
#print axioms CorridorContinuation.after_seal_wall
#print axioms CorridorContinuation.reply_ready
#print axioms CorridorContinuation.rawReply_source
#print axioms CorridorContinuation.continuation
#print axioms CorridorPreparation.plan
#print axioms CorridorPreparation.saved
#print axioms CorridorPreparation.area_lower
#print axioms CorridorPreparation.accepted
#print axioms CorridorPreparation.prepare
#print axioms CorridorPreparation.base
#print axioms VitalBirth.finish_after_placement
#print axioms VitalBirth.afterOpponent_ready
#print axioms VitalBirth.afterOpponent
#print axioms VitalBirth.miaiCertificate
#print axioms VitalBirth.ownCertificate
#print axioms VitalBirth.candidate?
#print axioms VitalBirth.plan_area_le_possible
#print axioms VitalBirth.plan_accepted_possible
#print axioms VitalBirthRecognize.scanMiai?
#print axioms VitalBirthRecognize.recognize?
#print axioms VitalBirthCapturing.complete_capture
#print axioms VitalBirthCapturing.finish_after_placement
#print axioms VitalBirthCapturing.afterOpponent_ready
#print axioms VitalBirthCapturing.afterOpponent
#print axioms VitalBirthCapturing.plan?
#print axioms VitalBirthCapturing.candidate?
#print axioms ExceptionalAll.certificate?
#print axioms Corridor.certificate?
#print axioms RoomSplit.Capturing.miai
#print axioms RoomSplit.certificate?
#print axioms StraightFourVital.certificate?
#print axioms WallResponse.certificate?
#print axioms WallResponse.recognize?
#print axioms SourceLeaf.wallResponseAnswer?
#print axioms SourceLeaf.vitalBirthAnswer?
#print axioms HookSource.afterWhite
#print axioms HookSource.reply
#print axioms HookSource.afterBlack
#print axioms HookSource.plan
#print axioms HookSource.miai
#print axioms HookSource.response
#print axioms HookSource.certificate?
#print axioms SourceLeaf.hookSourceAnswer?
#print axioms ElevenLeftBridge.candidate?
#print axioms ElevenLeftBridge.miai?
#print axioms ElevenLeftBridge.respond?
#print axioms ElevenLeftBridge.certificate?
#print axioms ElevenLeftBridge.recognize?
#print axioms SourceLeaf.elevenLeftBridgeAnswer?
#print axioms InitialColourPass.nativeStep_swap
#print axioms InitialColourPass.areaMargin_swap
#print axioms InitialColourPass.forcing_dichotomy
#print axioms InitialColourPass.initial_not_white_negative
#print axioms InitialColourPass.initial_nonnegative_certificate
#print axioms InitialColourPass.initial_nonnegative_policy
#print axioms RegionalProgram.HistoryMatches.step
#print axioms RegionalProgram.HistoryMatches.after_subset
#print axioms RegionalProgram.ownStep
#print axioms RegionalProgram.whiteStep
#print axioms RegionalProgram.SourceAt.credit_step
#print axioms RegionalProgram.ownSource
#print axioms RegionalProgram.whiteSource
#print axioms RegionalProgram.compileDAG
#print axioms RegionalProgram.Compiled.at?
#print axioms RegionalProgram.interpret?
#print axioms settle?
#print axioms Certificate.guarantee
#print axioms Certificate.faceGuarantee
#print axioms CalculationRuntime.faceAt_factorizes
#print axioms CalculationRuntime.observe_is_original_cursor
#print axioms GoalBracket.InitialBound.ofCertificate
#print axioms GoalBracket.InitialBound.ofAnswer
#print axioms GoalBracket.Bracket.absorb
#print axioms GoalBracket.Bracket.absorb_of_not_improves
#print axioms GoalBracket.Bracket.absorb_bounds
#print axioms GoalCursor.State.receiveCertificate
#print axioms GoalCursor.absorb
#print axioms GoalCursor.advance_receipt
#print axioms GoalCursor.advance_generated_receipt
#print axioms GoalCursor.query_answer_improves
#print axioms InitialColourPass.exact_value_bounds
#print axioms CalculationRuntime.received_next
#print axioms CalculationRuntime.mathematicalRange
#print axioms CalculationRuntime.mathematicalAt_authority
#print axioms Corridor.Source
#print axioms Corridor.sealedGeometry?
#print axioms ExceptionalAll.certificateWithStep?
#print axioms Corridor.fromSource?

example {frame : Frame 19} (certificate : Certificate .positive (-345) frame)
    (scoring : ScoringStatus frame) (opponent : ExecutablePolicy 19) :
    (-345 : Int) ≤ areaMargin (executePolicies (versus .positive certificate.policy opponent)
      frame scoring).replay.final.visible.board := by
  simpa only [acceptsMargin, decide_eq_true_eq] using certificate.guarantee scoring opponent
