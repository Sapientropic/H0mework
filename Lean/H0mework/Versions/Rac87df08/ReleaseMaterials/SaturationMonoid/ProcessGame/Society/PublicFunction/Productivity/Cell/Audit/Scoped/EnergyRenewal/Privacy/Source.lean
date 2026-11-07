import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy.Supply
import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy.Adaptive

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy
open Lean

/-- The entire public source request may be chosen again from prior complete outputs. -/
structure SourceInput where
  queries : Nat → Query
  births : Governance.Births
  replies : List ReplyInput
  cut : Nat
  candidate : Party
  epochQueries : Nat → Query
  ordinal : Nat
  commands : Input

def SourceInput.plan (input : SourceInput) (larger : Bool) : Plan :=
  sourcePlan input.queries larger input.births input.replies input.cut input.candidate

def initialWindows (larger : Bool) (input : SourceInput) : Option (Continuation.Window (input.plan larger)) :=
  (Runtime.nextEpoch (input.plan larger)).map (fun seed => Continuation.first seed input.epochQueries input.ordinal)

theorem initial_windows_are_generated (input : SourceInput) :
    Option.Rel WindowTwin (initialWindows false input) (initialWindows true input) :=
  original_source_generates_initial_windows input.queries input.epochQueries input.births input.replies
    input.cut input.candidate input.ordinal

def sourceResponse (larger : Bool) (input : SourceInput) : Except String Json :=
  (initialWindows larger input).elim (.error "ORIGINAL_SUPPLY_NOT_READY")
    (fun window => response window (input.cut+input.ordinal+2) input.commands)

theorem source_response_equal (input : SourceInput) : sourceResponse false input = sourceResponse true input := by
  have consume : ∀ {lp rp : Plan} {l : Option (Continuation.Window lp)} {r : Option (Continuation.Window rp)},
      Option.Rel WindowTwin l r →
      (l.elim (Except.error "ORIGINAL_SUPPLY_NOT_READY" : Except String Json) (fun window => response window (input.cut+input.ordinal+2) input.commands)) =
      (r.elim (Except.error "ORIGINAL_SUPPLY_NOT_READY" : Except String Json) (fun window => response window (input.cut+input.ordinal+2) input.commands)) := by
    intro lp rp l r related
    cases related with
    | none => rfl
    | some twin => exact twin.response _ _
  unfold sourceResponse
  exact consume (lp := input.plan false) (rp := input.plan true)
    (l := initialWindows false input) (r := initialWindows true input) (initial_windows_are_generated input)

abbrev SourceStrategy := List (Except String Json) → Nat → SourceInput

def sourceAdaptive (larger : Bool) (strategy : SourceStrategy) : Nat → List (Except String Json)
  | 0 => []
  | n+1 => let past := sourceAdaptive larger strategy n
    past ++ [sourceResponse larger (strategy past n)]

/-- No WindowTwin, supplied world, successful supply, reply order or bounded actor is a premise. -/
theorem every_original_source_strategy_preserves_complete_cumulative_privacy (strategy : SourceStrategy) (count : Nat) :
    sourceAdaptive false strategy count = sourceAdaptive true strategy count := by
  induction count with
  | zero => rfl
  | succ n ih => simp only [sourceAdaptive,ih,source_response_equal]

/-- Authentication identities, nonces and other allowed metadata belong to the public input;
all source errors and successful fields remain inside the observed result. -/
def sourceEnvelope (larger : Bool) (decode : Json → Except String SourceInput)
    (metadata : Json → Json) (raw : Json) : Except String Json := do
  let input ← decode raw
  let answer ← sourceResponse larger input
  return Json.mkObj [("metadata",metadata raw),("native",answer)]

theorem source_envelope_equal (decode : Json → Except String SourceInput) (metadata : Json → Json) (raw : Json) :
    sourceEnvelope false decode metadata raw = sourceEnvelope true decode metadata raw := by
  unfold sourceEnvelope
  cases decode raw with
  | error _ => rfl
  | ok input => simp only [source_response_equal]

def sourceEnvelopeAdaptive (larger : Bool) (decode : Json → Except String SourceInput)
    (metadata : Json → Json) (strategy : List (Except String Json) → Nat → Json) : Nat → List (Except String Json)
  | 0 => []
  | n+1 => let past := sourceEnvelopeAdaptive larger decode metadata strategy n
    past ++ [sourceEnvelope larger decode metadata (strategy past n)]

theorem every_decoded_source_strategy_preserves_all_output (decode : Json → Except String SourceInput)
    (metadata : Json → Json) (strategy : List (Except String Json) → Nat → Json) (count : Nat) :
    sourceEnvelopeAdaptive false decode metadata strategy count = sourceEnvelopeAdaptive true decode metadata strategy count := by
  induction count with
  | zero => rfl
  | succ n ih => simp only [sourceEnvelopeAdaptive,ih,source_envelope_equal]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy
