import H0mework.NavierStokes.ShellGluing.NativeMacroRequestedTimeReplayV2LocalTerminalWholeContinuousMildSerrin
import H0mework.NavierStokes.ShellGluing.NativeMacroRequestedTimeReplayV2LocalWholeContinuousMildSerrin

/-!
# Unconditional source-owned local whole-flow receipt

The V2 residual runtime runs on the positive horizon generated from the
actual source contact.  Its internal terminal/infinite exhaustion is now
consumed completely: either a finite stage has already closed the whole
punctured residual, or the actual strict-support replay converges to the
whole mild flow.  Both branches produce the same dependent whole unforced
receipt, so no branch, smallness witness, cutoff, target path, or
continuation certificate remains in the source-facing mouth.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalWholeUnforced

open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime.GeneratedRedirectedCompleteRoundInfiniteLineage
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeResidualCommonTimeReplay
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2Runtime
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalBudget
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalTerminalWholeContinuousMildSerrin
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalWholeContinuousMildSerrin
open
  ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness

noncomputable section

/-- The actual source contact unconditionally generates one whole unforced
Navier--Stokes update on its own positive local horizon. -/
noncomputable def generatedSourceOwnedLocalWholeContinuousMildSerrinReceipt
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν) :
    WholeContinuousMildSerrinReceipt
      ν (commonTimeReplayInitialState lineage)
        (sourceOwnedLocalReplayV2Duration lineage) := by
  let durationPos := sourceOwnedLocalReplayV2Duration_pos lineage
  cases
      generatedRequestedTimeReplayV2Disposition lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos with
  | terminal run =>
      exact
        generatedLocalReplayV2TerminalWholeContinuousMildSerrinReceipt run
  | infinite replay _startsAtInitial =>
      exact generatedLocalReplayV2WholeContinuousMildSerrinReceipt replay

end

end
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalWholeUnforced
end NavierStokes
end SaturationMonoid
