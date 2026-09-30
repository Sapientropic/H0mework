import H0mework.NavierStokes.ShellGluing.NativeMacroRequestedTimeReplayTerminalWholeContinuousMildSerrin
import H0mework.NavierStokes.ShellGluing.NativeMacroRequestedTimeReplayWholeContinuousMildSerrin
import H0mework.NavierStokes.WholeSpace.WholeContinuousMildSerrinOverlap

/-!
# Source-generated whole unforced receipts on arbitrary horizons

The requested-time source runtime has two native outcomes after the actual
initial lineage is known to lie below the fixed half-critical threshold:

* a finite terminal whose complete whole residual is zero;
* an infinite strict-support replay whose whole weak limit closes.

Both outcomes now compile to the same target object, so the branch is no
longer exposed to a caller.  For every positive requested horizon the source
itself produces one whole continuous mild/Serrin receipt.  Receipts generated
at different horizons agree on their actual overlap by whole-path
same-initial uniqueness.

Without the initial subcritical fact, the public theorem retains exactly the
remaining PDE alternative:

```text
initial half-critical crossing
or
source-generated whole unforced receipt on the requested horizon.
```

No branch, replay, terminal run, trajectory, target path, coverage family,
continuation witness, cutoff, smallness knob, or energy-payment certificate
is accepted from a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeWholeContinuousMildSerrin

open Set
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime.GeneratedRedirectedCompleteRoundInfiniteLineage
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeResidualCriticalLineage
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeResidualCommonTimeReplay
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayTerminalWholeContinuousMildSerrin
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayWholeContinuousMildSerrin
open
  ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open
  ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap

noncomputable section

/--
For a source lineage below the fixed initial half-critical threshold, the
maximal requested-time runtime itself chooses its terminal or infinite
branch and produces the corresponding whole unforced receipt.
-/
noncomputable def generatedRequestedTimeWholeContinuousMildSerrinReceipt
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0)
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime) :
    WholeContinuousMildSerrinReceipt
      ν (commonTimeReplayInitialState lineage) requestedTime := by
  cases
      generatedRequestedTimeReplayDisposition
        lineage initialSubcritical requestedTime requestedTimePos with
  | terminal run =>
      exact
        generatedRequestedTimeReplayTerminalWholeContinuousMildSerrinReceipt
          run
  | infinite replay _startsAtInitial =>
      exact
        generatedRequestedReplayWholeContinuousMildSerrinReceipt replay

/--
Unconditional source-facing hard-gate reduction on an arbitrary positive
horizon.  The returned sum retains an actual crossing proof on the left or
the generated whole unforced receipt itself on the right; it does not hide
the target object behind an existential certificate.
-/
noncomputable def
    generatedRequestedTimeHalfCriticalOrWholeContinuousMildSerrin
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime) :
    PLift (lineageHalfCriticalCrossing lineage 0) ⊕
      WholeContinuousMildSerrinReceipt
        ν (commonTimeReplayInitialState lineage) requestedTime := by
  by_cases crossing : lineageHalfCriticalCrossing lineage 0
  · exact Sum.inl ⟨crossing⟩
  · exact
      Sum.inr
        (generatedRequestedTimeWholeContinuousMildSerrinReceipt
          lineage crossing requestedTime requestedTimePos)

/--
The receipts generated from one source lineage on two positive horizons
are the same physical path on the shorter interval.  The overlap equality
is derived from their actual unforced equations; no overlap or restart
certificate is supplied.
-/
theorem generatedRequestedTimeWholeContinuousMildSerrinReceipt_overlap
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0)
    {smallerTime largerTime : ℝ}
    (smallerTimePos : 0 < smallerTime)
    (largerTimePos : 0 < largerTime)
    (timeLe : smallerTime ≤ largerTime) :
    (generatedRequestedTimeWholeContinuousMildSerrinReceipt
        lineage initialSubcritical smallerTime smallerTimePos).wholePath =
      (generatedRequestedTimeWholeContinuousMildSerrinReceipt
          lineage initialSubcritical largerTime largerTimePos).wholePath.compContinuous
        (commonTimeInclusion timeLe) :=
  wholeContinuousMildSerrin_overlap
    (generatedRequestedTimeWholeContinuousMildSerrinReceipt
      lineage initialSubcritical smallerTime smallerTimePos)
    (generatedRequestedTimeWholeContinuousMildSerrinReceipt
      lineage initialSubcritical largerTime largerTimePos)
    timeLe

end

end
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeWholeContinuousMildSerrin
end NavierStokes
end SaturationMonoid
