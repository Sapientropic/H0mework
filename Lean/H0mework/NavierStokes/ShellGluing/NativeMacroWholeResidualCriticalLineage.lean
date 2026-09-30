import H0mework.NavierStokes.ShellGluing.NativeMacroWholeResidualCriticalPayment

/-!
# No-double-payment critical ledger on the native whole-residual lineage

The local whole-residual consumer pays every active occurrence by the
half-enstrophy drop of its own actual unforced receipt.  The remaining
variable-support seam is exact: the complete carrier of occurrence `i`
becomes the current carrier of occurrence `i+1`, while the next complete
carrier adds only zero-valued rows at time zero.

Consequently adjacent receipt half-enstrophies glue and arbitrary finite
prefixes telescope without shell injection or duplicate restart charges.
For every nonempty prefix the source itself exhausts:

```text
fixed half-critical crossing
or faithful whole-residual zero
or A_(1/2,ν) * Σ_i T_i³ Q_i / 12 < E_0 - E_n.
```

No margin, branch choice, local time, support, endpoint, horizon certificate,
or payment bound is supplied by the caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeResidualCriticalLineage

open scoped BigOperators

open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open
  ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open
  ThreeDimensionalVorticityCoefficientGeneratedPathCriticalAbsorption
open
  ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedSupport
open
  ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedUnforcedReceipt
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime.GeneratedRedirectedCompleteRoundInfiniteLineage
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroBoundaryTangentGluing
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeResidualLineage
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeResidualActualIntegralPayment
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeResidualCriticalPayment

noncomputable section

/-! ## Exact receipt energies and the variable-support seam -/

/-- Complete finite Galerkin carrier of one actual unforced macro receipt. -/
def lineageReceiptModes
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    Finset IntegerWavevector :=
  generatedSupport
    (completeOmittedPhysicalLiftSource
      (lineage.current index).physicalSource)

/-- Half-enstrophy at the actual start of one macro receipt. -/
def lineageReceiptInitialHalfEnstrophy
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) : ℝ :=
  finiteStateVorticityHalfEnstrophy
    (lineageReceiptModes lineage index)
    ((lineage.physicalReceipt index).trajectory 0)

/-- Half-enstrophy at the actual endpoint of one macro receipt. -/
def lineageReceiptEndpointHalfEnstrophy
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) : ℝ :=
  finiteStateVorticityHalfEnstrophy
    (lineageReceiptModes lineage index)
    ((lineage.physicalReceipt index).trajectory
      (lineage.physicalReceipt index).duration)

/-- Actual endpoint half-enstrophy drop of one unforced macro receipt. -/
def lineageReceiptHalfEnstrophyDrop
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) : ℝ :=
  lineageReceiptInitialHalfEnstrophy lineage index -
    lineageReceiptEndpointHalfEnstrophy lineage index

/-- Fixed source-independent half-critical crossing at one actual start. -/
def lineageHalfCriticalCrossing
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) : Prop :=
  (1 / 2 : ℝ) * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 <
    criticalEnstrophyLatticeConstant *
      finiteStateVorticityCoefficientEnstrophy
        (lineageReceiptModes lineage index)
        ((lineage.physicalReceipt index).trajectory 0)

/-- Cubic source-generated whole-residual charge at one occurrence. -/
def lineageWholeResidualCubicCharge
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ)
    (localTime : ℝ) : ℝ :=
  localTime ^ 3 *
      lineageWholeResidualEnstrophyQuantum lineage index /
    12

/--
Installing the complete missing inventory preserves the current
half-enstrophy: every newly added row is generated at zero.
-/
private theorem completeInitial_halfEnstrophy_eq_currentSupport
    (source : RawVorticityFourierSource) :
    finiteStateVorticityHalfEnstrophy
        (generatedCompleteNonlinearGalerkinModes source)
        (generatedCompleteNonlinearInitialState source) =
      finiteStateVorticityHalfEnstrophy
        (generatedSupport source)
        (generatedComplexVorticityState source
          (generatedSupport source)) := by
  rw [generatedCompleteNonlinearInitialState_eq_currentPhysicalState]
  unfold finiteStateVorticityHalfEnstrophy
  congr 1
  unfold finiteStateVorticityCoefficientEnstrophy
  symm
  rw [Finset.sum_subset
    (generatedSupport_subset_completeNonlinearGalerkinModes source)]
  intro wave waveInComplete waveNotInSupport
  have waveInMissing :
      wave ∈ generatedMissingNonlinearModes source := by
    have unionMem :
        wave ∈ generatedSupport source ∪
          generatedMissingNonlinearModes source := by
      simpa [generatedCompleteNonlinearGalerkinModes] using
        waveInComplete
    exact (Finset.mem_union.mp unionMem).resolve_left waveNotInSupport
  have activeMem :
      wave ∈ generatedActiveNonliveNonlinearModes source :=
    ((mem_generatedMissingNonlinearModes_iff source wave).mp
      waveInMissing).1
  have rowZero :=
    generatedCompleteNonlinearInitialState_activeNonlive_zero
      source activeMem
  rw [generatedCompleteNonlinearInitialState_eq_currentPhysicalState]
    at rowZero
  rw [rowZero]
  simp [complexCoordinateAmplitudeSq]

/--
Adjacent actual receipts have exactly the same half-enstrophy at their
common physical boundary, despite the next zero-filled support expansion.
-/
theorem adjacentPhysicalReceipts_halfEnstrophy_glue
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    lineageReceiptEndpointHalfEnstrophy lineage index =
      lineageReceiptInitialHalfEnstrophy lineage (index + 1) := by
  unfold lineageReceiptEndpointHalfEnstrophy
  unfold lineageReceiptInitialHalfEnstrophy
  unfold lineageReceiptModes
  calc
    finiteStateVorticityHalfEnstrophy
          (generatedSupport
            (completeOmittedPhysicalLiftSource
              (lineage.current index).physicalSource))
          ((lineage.physicalReceipt index).trajectory
            (lineage.physicalReceipt index).duration) =
        finiteStateVorticityHalfEnstrophy
          (generatedSupport
            (lineage.current (index + 1)).physicalSource)
          (generatedComplexVorticityState
            (lineage.current (index + 1)).physicalSource
            (generatedSupport
              (lineage.current (index + 1)).physicalSource)) := by
      rw [boundary_nextSource_state_eq_leftEndpoint lineage index,
        boundary_nextSource_support_eq_leftModes lineage index]
      rfl
    _ =
        finiteStateVorticityHalfEnstrophy
          (generatedCompleteNonlinearGalerkinModes
            (lineage.current (index + 1)).physicalSource)
          (generatedCompleteNonlinearInitialState
            (lineage.current (index + 1)).physicalSource) :=
      (completeInitial_halfEnstrophy_eq_currentSupport
        (lineage.current (index + 1)).physicalSource).symm
    _ =
        finiteStateVorticityHalfEnstrophy
          (generatedSupport
            (completeOmittedPhysicalLiftSource
              (lineage.current (index + 1)).physicalSource))
          ((lineage.physicalReceipt (index + 1)).trajectory 0) := by
      change
        finiteStateVorticityHalfEnstrophy
            (generatedCompleteNonlinearGalerkinModes
              (lineage.current (index + 1)).physicalSource)
            (generatedCompleteNonlinearInitialState
              (lineage.current (index + 1)).physicalSource) =
          finiteStateVorticityHalfEnstrophy
            (generatedSupport
              (completeOmittedPhysicalLiftSource
                (lineage.current (index + 1)).physicalSource))
            ((completeOmittedPhysicalTimeReceipt
              (lineage.current (index + 1)).physicalSource ν).trajectory 0)
      rw [completeOmittedPhysicalLiftSource_generatedSupport,
        completeOmittedPhysicalTimeReceipt_initial]

/-! ## Exact prefix telescope -/

/--
Endpoint drops telescope over every actual macro prefix.  The variable
support creates no hidden injection because each newly installed row is
zero at the common boundary.
-/
theorem sum_lineageReceiptHalfEnstrophyDrop_eq_initial_sub_boundary
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν) :
    ∀ length : ℕ,
      (∑ index ∈ Finset.range length,
        lineageReceiptHalfEnstrophyDrop lineage index) =
        lineageReceiptInitialHalfEnstrophy lineage 0 -
          lineageReceiptInitialHalfEnstrophy lineage length
  | 0 => by
      simp
  | length + 1 => by
      rw [Finset.sum_range_succ,
        sum_lineageReceiptHalfEnstrophyDrop_eq_initial_sub_boundary
          lineage length]
      unfold lineageReceiptHalfEnstrophyDrop
      rw [adjacentPhysicalReceipts_halfEnstrophy_glue
        lineage length]
      ring

/-! ## Internal prefix exhaustion -/

/--
Every actual finite prefix internally produces one of four exhaustive
outcomes:

* the empty prefix;
* a fixed half-critical crossing;
* a faithfully zero whole-PDE residual;
* source-generated positive local times whose complete cubic responsibility
  is strictly paid by the single telescoped half-enstrophy budget.

The final branch is the no-double-payment finite-prefix consumer.  Its
`localTime` function is generated in the conclusion from the actual
occurrences.
-/
theorem generatedWholeResidualRedirect_halfCriticalPrefixPayment
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (length : ℕ) :
    length = 0 ∨
      (∃ index : ℕ,
        index < length ∧
          lineageHalfCriticalCrossing lineage index) ∨
      (∃ index : ℕ,
        index < length ∧
          lineageOwnedWholeResidual lineage index = 0) ∨
      ∃ localTime : Fin length → ℝ,
        (∀ index : Fin length,
          0 < localTime index ∧
            localTime index <
              (lineage.physicalReceipt index.1).duration ∧
            criticalEnstrophyAbsorptionCoefficient (1 / 2) ν *
                  lineageWholeResidualCubicCharge
                    lineage index.1 (localTime index) <
              lineageReceiptHalfEnstrophyDrop
                lineage index.1) ∧
          criticalEnstrophyAbsorptionCoefficient (1 / 2) ν *
                (∑ index : Fin length,
                  lineageWholeResidualCubicCharge
                    lineage index.1 (localTime index)) <
            lineageReceiptInitialHalfEnstrophy lineage 0 -
              lineageReceiptInitialHalfEnstrophy lineage length := by
  by_cases lengthZero : length = 0
  · exact Or.inl lengthZero
  · right
    have lengthPositive : 0 < length := Nat.pos_of_ne_zero lengthZero
    by_cases hasCrossing :
        ∃ index : ℕ,
          index < length ∧
            lineageHalfCriticalCrossing lineage index
    · exact Or.inl hasCrossing
    · right
      by_cases hasZero :
          ∃ index : ℕ,
            index < length ∧
              lineageOwnedWholeResidual lineage index = 0
      · exact Or.inl hasZero
      · right
        have localPaid :
            ∀ index : Fin length,
              ∃ localTime : ℝ,
                0 < localTime ∧
                  localTime <
                    (lineage.physicalReceipt index.1).duration ∧
                  criticalEnstrophyAbsorptionCoefficient (1 / 2) ν *
                        lineageWholeResidualCubicCharge
                          lineage index.1 localTime <
                    lineageReceiptHalfEnstrophyDrop
                      lineage index.1 := by
          intro index
          rcases
              generatedWholeResidualRedirect_halfCriticalCubicPayment
                lineage index.1 with
            crossing | residualZero | paid
          · exact False.elim <|
              hasCrossing
                ⟨index.1, index.2,
                  by
                    simpa [lineageHalfCriticalCrossing,
                      lineageReceiptModes] using crossing⟩
          · exact False.elim <|
              hasZero ⟨index.1, index.2, residualZero⟩
          · rcases paid with
              ⟨residualNonzero, localTime, localTimePos,
                localTimeLtDuration, paid⟩
            exact
              ⟨localTime, localTimePos, localTimeLtDuration,
                by
                  simpa [lineageWholeResidualCubicCharge,
                    lineageReceiptHalfEnstrophyDrop,
                    lineageReceiptInitialHalfEnstrophy,
                    lineageReceiptEndpointHalfEnstrophy,
                    lineageReceiptModes] using paid⟩
        let localTime : Fin length → ℝ :=
          fun index => Classical.choose (localPaid index)
        have localTimeSpec :
            ∀ index : Fin length,
              0 < localTime index ∧
                localTime index <
                  (lineage.physicalReceipt index.1).duration ∧
                criticalEnstrophyAbsorptionCoefficient (1 / 2) ν *
                      lineageWholeResidualCubicCharge
                        lineage index.1 (localTime index) <
                  lineageReceiptHalfEnstrophyDrop
                    lineage index.1 := by
          intro index
          exact Classical.choose_spec (localPaid index)
        letI : Nonempty (Fin length) :=
          ⟨⟨0, lengthPositive⟩⟩
        have sumStrict :
            (∑ index : Fin length,
              criticalEnstrophyAbsorptionCoefficient (1 / 2) ν *
                lineageWholeResidualCubicCharge
                  lineage index.1 (localTime index)) <
              ∑ index : Fin length,
                lineageReceiptHalfEnstrophyDrop
                  lineage index.1 := by
          exact
            Finset.sum_lt_sum_of_nonempty
              Finset.univ_nonempty
              (fun index indexMem => (localTimeSpec index).2.2)
        have dropSum :
            (∑ index : Fin length,
              lineageReceiptHalfEnstrophyDrop
                lineage index.1) =
              lineageReceiptInitialHalfEnstrophy lineage 0 -
                lineageReceiptInitialHalfEnstrophy lineage length := by
          rw [Fin.sum_univ_eq_sum_range]
          exact
            sum_lineageReceiptHalfEnstrophyDrop_eq_initial_sub_boundary
              lineage length
        refine ⟨localTime, localTimeSpec, ?_⟩
        calc
          criticalEnstrophyAbsorptionCoefficient (1 / 2) ν *
                (∑ index : Fin length,
                  lineageWholeResidualCubicCharge
                    lineage index.1 (localTime index)) =
              ∑ index : Fin length,
                criticalEnstrophyAbsorptionCoefficient (1 / 2) ν *
                  lineageWholeResidualCubicCharge
                    lineage index.1 (localTime index) := by
            rw [Finset.mul_sum]
          _ < ∑ index : Fin length,
                lineageReceiptHalfEnstrophyDrop
                  lineage index.1 :=
            sumStrict
          _ =
              lineageReceiptInitialHalfEnstrophy lineage 0 -
                lineageReceiptInitialHalfEnstrophy lineage length :=
            dropSum

end

end
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeResidualCriticalLineage
end NavierStokes
end SaturationMonoid
