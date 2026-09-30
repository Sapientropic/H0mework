import H0mework.Versions.X.Fock.RetainedCoarsening.Value

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceRetainedCoarsening

open SourceRetainedReceiver (Raw Frame At rawAt value)
open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem realize_injective (runtime : LivingRuntimeState process) : Function.Injective (realize runtime) := by
  intro left right same
  apply SourceReceivedConditionalStep.coordinates_injective runtime (maximumIndex runtime) 0
  have read := congrArg (SourceCopyCurrentCoordinates.sourceRead runtime (maximumIndex runtime) 0) same
  simpa only [realize, LinearMap.coe_mk, AddHom.coe_mk, SourceReceivedConditionalStep.completeValue,
    SourceCopyCurrentCoordinates.realize_source] using read

variable {Key : Type*} [DecidableEq Key]

theorem frame_ext (bound stride : Nat) (left right : Frame Key bound stride)
    (keys : left.keys = right.keys) (native : left.native = right.native)
    (rows : ∀ key, rawAt bound stride left key = rawAt bound stride right key) : left = right := by
  cases left with
  | mk leftKeys leftNative leftObservation =>
    cases right with
    | mk rightKeys rightNative rightObservation =>
      dsimp only at keys native
      cases keys
      cases native
      congr 1
      funext key
      have same := rows key.val
      simpa only [rawAt, dif_pos key.property] using same

theorem frame_value_ext (runtime : LivingRuntimeState process) (left right : At runtime Key)
    (keys : left.keys = right.keys) (native : left.native = right.native)
    (values : ∀ key, value runtime left key = value runtime right key) : left = right := by
  apply frame_ext _ _ left right keys native
  intro key
  exact realize_injective runtime (values key)

end
end SourceRetainedCoarsening
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
