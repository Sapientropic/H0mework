import H0mework.NavierStokes.ShellGluing.NativeMacroRedirectPDEObstruction

/-!
# First shell responsibility on the redirected macro's actual PDE receipt

The redirected macro keeps the old maximal shell producer while making its
physical projection one actual unforced complete-support receipt.  This
module identifies the first old shell response with the time-zero tangent of
that very receipt, before any later shell occurrence or Fourier aggregation.

For every native macro edge the source itself generates exactly one of:

* the old shell responder is quiet and the redirected shell trace is zero;
* the first literal shell receipt is nonzero, its complete row starts at zero
  on the macro's actual physical receipt, and its old coefficient trace is
  exactly the receipt's unforced time-zero derivative.

The same complete carrier has zero whole-lattice PDE residual on every row
of that first shell.  No caller supplies a branch, response, output,
nonzero witness, trajectory, time, support, or coverage premise.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroFirstShellPDEBridge

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientNonlinearPairGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open
  ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPath
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellTraceCumulative
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellReflexiveWrite
open ThreeDimensionalVorticityCoefficientGeneratedScaleTimeShellRound
open ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedSupport
open
  ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedUnforcedReceipt
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime.GeneratedRedirectedCompleteRoundInfiniteLineage

noncomputable section

/-! ## Outer-shell rows belong to the complete responsibility carrier -/

theorem generatedOuterNonlinearShellModes_subset_activeNonlive
    (source : RawVorticityFourierSource)
    (shellSq : ℤ) :
    generatedOuterNonlinearShellModes source shellSq ⊆
      generatedActiveNonliveNonlinearModes source := by
  intro output outputMem
  have outerMem :
      output ∈ generatedActiveOuterNonlinearModes source :=
    ((mem_generatedOuterNonlinearShellModes_iff
      source shellSq output).mp outputMem).1
  unfold generatedActiveOuterNonlinearModes at outerMem
  split at outerMem
  · simp at outerMem
  · rcases Finset.mem_filter.mp outerMem with
      ⟨inventory, outputNonzero, notLive, _strictOuter,
        coefficientNonzero⟩
    exact
      (mem_generatedActiveNonliveNonlinearModes_iff
        source output).mpr
        ⟨inventory, outputNonzero, notLive, coefficientNonzero⟩

/-! ## Quiet and active source branches -/

private theorem cumulativeTrace_eq_zero_of_seed_stopped
    {seed terminal : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed terminal)
    (stopped : generatedIntegerShellRespond seed = none) :
    generatedIntegerShellCumulativeTrace arrival = 0 := by
  induction arrival with
  | initial =>
      rfl
  | @step prior arrival response generated inductionHypothesis =>
      have priorEq : prior = seed :=
        NativeReachable.eq_initial_of_respond_eq_none
          seed generatedIntegerShellRespond stopped arrival
      subst prior
      rw [stopped] at generated
      contradiction

private theorem shellTrace_eq_zero_of_firstResponder_none
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ)
    (stopped :
      generatedIntegerShellRespond
          (lineage.current index).physicalSource =
        none) :
    (lineage.step index).shellTrace = 0 := by
  unfold NativeRedirectedCompleteRoundStep.shellTrace
  exact
    cumulativeTrace_eq_zero_of_seed_stopped
      (lineage.round index).shellRun.arrival stopped

private theorem terminal_eq_seed_of_occurrence_eq_zero
    {seed terminal : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed terminal)
    (occurrenceZero : arrival.occurrence = 0) :
    terminal = seed := by
  cases arrival with
  | initial =>
      rfl
  | step arrival generated =>
      simp [NativeReachable.occurrence] at occurrenceZero

private theorem shellTrace_ne_zero_of_firstResponder_some
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ)
    (response :
      Response GeneratedIntegerShellStep
        (lineage.current index).physicalSource)
    (generated :
      generatedIntegerShellRespond
          (lineage.current index).physicalSource =
        some response) :
    (lineage.step index).shellTrace ≠ 0 := by
  have shellLengthNe :
      (lineage.round index).shellLength ≠ 0 := by
    intro shellLengthZero
    change
      (lineage.round index).shellRun.arrival.occurrence = 0
      at shellLengthZero
    have terminalEq :=
      terminal_eq_seed_of_occurrence_eq_zero
        (lineage.round index).shellRun.arrival shellLengthZero
    have terminalStopped :=
      (lineage.round index).shellRun.stopped
    rw [terminalEq] at terminalStopped
    change
      generatedIntegerShellRespond
          (lineage.current index).physicalSource =
        none
      at terminalStopped
    rw [generated] at terminalStopped
    contradiction
  have shellLengthPos :
      0 < (lineage.round index).shellLength :=
    Nat.pos_of_ne_zero shellLengthNe
  cases shellRedirectActivity lineage index with
  | quiet quietLength _traceZero =>
      exact (shellLengthNe quietLength).elim
  | active _activeLength traceNonzero =>
      exact traceNonzero

/-! ## Same-event old-q / actual-unforced-PDE bridge -/

/--
Every redirected macro edge internally exposes either a genuinely quiet old
shell producer, or a first literal old-q receipt on the exact physical
receipt of that macro.

In the active branch:

* the cumulative redirected shell trace is nonzero;
* the first whole shell is source-generated and inhabited;
* every selected row belongs to the complete responsibility carrier;
* that row starts at zero and has old `q` as the actual unforced derivative;
* every scalar coordinate of the old receipt trace is that same derivative;
* the complete time-zero Galerkin compiler has zero whole-lattice PDE
  residual on the row.
-/
theorem generatedFirstShellTrace_actualUnforcedPDE
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    (lineage.step index).shellTrace = 0 ∨
      ((lineage.step index).shellTrace ≠ 0 ∧
        ∃ receipt : GeneratedIntegerShellReceipt,
          receipt.current =
              (lineage.current index).physicalSource ∧
            receipt.wholeShellModes.Nonempty ∧
            ∀ output ∈ receipt.wholeShellModes,
              output ∈
                  generatedActiveNonliveNonlinearModes
                    (lineage.current index).physicalSource ∧
                (lineage.physicalReceipt index).trajectory
                    0 output =
                  0 ∧
                HasDerivAt
                  (fun time =>
                    (lineage.physicalReceipt index).trajectory
                      time output)
                  (generatedVorticityNonlinearCoefficientAt
                    (lineage.current index).physicalSource output)
                  0 ∧
                generatedVorticityNonlinearCoefficientAt
                    (lineage.current index).physicalSource output ≠
                  0 ∧
                (∀ coordinate,
                  generatedIntegerShellReceiptTrace receipt
                      (output, coordinate) =
                    generatedVorticityNonlinearCoefficientAt
                      (lineage.current index).physicalSource
                      output coordinate) ∧
                wholeLatticeVorticityFourierPDEResidualAt
                    ν.coeff
                    (generatedCompleteNonlinearInitialState
                      (lineage.current index).physicalSource)
                    (finiteStateVorticityGenerator
                      (generatedCompleteNonlinearGalerkinModes
                        (lineage.current index).physicalSource)
                      ν.coeff
                      (generatedCompleteNonlinearInitialState
                        (lineage.current index).physicalSource))
                    output =
                  0) := by
  cases generated :
      generatedIntegerShellRespond
        (lineage.current index).physicalSource with
  | none =>
      exact
        Or.inl
          (shellTrace_eq_zero_of_firstResponder_none
            lineage index generated)
  | some response =>
      let receipt :=
        receiptOfResponse
          (lineage.current index).physicalSource response generated
      refine
        Or.inr
          ⟨shellTrace_ne_zero_of_firstResponder_some
              lineage index response generated,
            receipt, rfl, receipt.wholeShellModes_nonempty, ?_⟩
      intro output outputMem
      have activeNonlive :
          output ∈
            generatedActiveNonliveNonlinearModes
              (lineage.current index).physicalSource :=
        generatedOuterNonlinearShellModes_subset_activeNonlive
          (lineage.current index).physicalSource
          receipt.selectedShellSq outputMem
      refine
        ⟨activeNonlive,
          completeOmittedPhysicalTimeReceipt_activeNonlive_initial_zero
            (lineage.current index).physicalSource ν activeNonlive,
          completeOmittedPhysicalTimeReceipt_activeNonlive_derivative
            (lineage.current index).physicalSource ν activeNonlive,
          generatedVorticityNonlinearCoefficientAt_ne_zero_of_mem_outerShell
            (lineage.current index).physicalSource
            receipt.selectedShellSq outputMem,
          ?_, ?_⟩
      · intro coordinate
        rw [generatedIntegerShellReceiptTrace_apply,
          if_pos outputMem]
        rfl
      · exact
          completeGalerkinFullPDEResidual_activeNonlive_eq_zero
            (lineage.current index).physicalSource
            ν.coeff activeNonlive

end

end
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroFirstShellPDEBridge
end NavierStokes
end SaturationMonoid
