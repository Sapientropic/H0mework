import H0mework.NavierStokes.EndpointWork.ComplementNoSilentWrite
import H0mework.NavierStokes.EndpointWork.CollectiveCausalGapWrite

/-!
# Quadratic kinetic boundary cocycle on actual restart writes

Every old-run native velocity write is an actual unforced endpoint
difference and already carries its exact tangent/pair Duhamel compiler.  This
module evaluates that same write against its actual incoming velocity before
any quotient:

* the quadratic polarization term is exactly the one-edge kinetic boundary;
* kinetic monotonicity makes the boundary nonpositive;
* a nonzero write therefore has a strictly negative incoming-velocity
  pairing, and some generated Fourier row pays that pairing;
* the row remains the exact causal tangent plus complete pair innovation and
  enters the existing tangent-payment or pair/heat native exhaustion;
* finite actual paths telescope the same quadratic boundary without duplicate
  payment.

No cutoff, path, output, pair, branch, nonzero quantum, target state,
faithfulness law, or continuation certificate is supplied by a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomQuadraticBoundaryCocycle

open scoped BigOperators

open Set
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingUnforcedTangentPayment
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceRateSettlement
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelOccurrence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelTerminalTraceRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelKineticTriadRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelTangentInnovation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHeatCommutatorNativeVelocityPairRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointComponentOccurrenceMacroWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointComponentOccurrenceMacroWrite.WholeRestartEndpointComponentMacroPhase
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime.GeneratedWholeRestartEndpointMacroStep
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointCofinalPairDuhamelMacroWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomAlignedCausalWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomComplementNoSilentWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomCollectiveCausalGapWrite
open AffineRelaxation

noncomputable section

/-! ## One-edge quadratic boundary -/

/-- The actual native velocity update obeys the exact Hilbert polarization
identity on the same incoming and outgoing physical endpoint states. -/
theorem wholeRestartNativeCausalVelocityWrite_quadraticBoundary
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    ‖wholeRestartContactVelocityState current (index + 1)‖ ^ 2 =
      ‖wholeRestartContactVelocityState current index‖ ^ 2 +
        2 * RCLike.re (inner ℂ
          (wholeRestartContactVelocityState current index)
          (wholeRestartNativeCausalVelocityWrite current index)) +
        ‖wholeRestartNativeCausalVelocityWrite current index‖ ^ 2 := by
  have nextEq :
      wholeRestartContactVelocityState current (index + 1) =
        wholeRestartContactVelocityState current index +
          wholeRestartNativeCausalVelocityWrite current index := by
    rw [wholeRestartNativeCausalVelocityWrite_eq_adjacent]
    abel
  rw [nextEq, norm_add_sq (𝕜 := ℂ)]

/-- The quadratic boundary is literally the change in physical kinetic
square on this exact native edge. -/
theorem wholeRestartNativeCausalVelocityWrite_quadraticBoundary_eq_gap
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    2 * RCLike.re (inner ℂ
          (wholeRestartContactVelocityState current index)
          (wholeRestartNativeCausalVelocityWrite current index)) +
        ‖wholeRestartNativeCausalVelocityWrite current index‖ ^ 2 =
      ‖wholeRestartContactVelocityState current (index + 1)‖ ^ 2 -
        ‖wholeRestartContactVelocityState current index‖ ^ 2 := by
  rw [wholeRestartNativeCausalVelocityWrite_quadraticBoundary current index]
  ring

/-- Actual unforced kinetic monotonicity makes the same-edge quadratic
boundary nonpositive. -/
theorem wholeRestartNativeCausalVelocityWrite_quadraticBoundary_nonpos
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    2 * RCLike.re (inner ℂ
          (wholeRestartContactVelocityState current index)
          (wholeRestartNativeCausalVelocityWrite current index)) +
        ‖wholeRestartNativeCausalVelocityWrite current index‖ ^ 2 ≤ 0 := by
  have massLe :=
    run_contact_kineticMass_antitone current (Nat.le_succ index)
  have velocityNormLe :
      ‖wholeRestartContactVelocityState current (index + 1)‖ ^ 2 ≤
        ‖wholeRestartContactVelocityState current index‖ ^ 2 := by
    rw [wholeRestartContactVelocityState_norm_sq,
      wholeRestartContactVelocityState_norm_sq]
    simpa [Nat.succ_eq_add_one] using massLe
  rw [wholeRestartNativeCausalVelocityWrite_quadraticBoundary current index]
    at velocityNormLe
  linarith

/-! ## The generated energy-paying Duhamel row -/

/-- The real whole-carrier pairing is the sum of the pairings of the exact
generated Fourier rows. -/
theorem wholeRestartNativeCausalVelocityWrite_realInner_eq_tsum
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    RCLike.re (inner ℂ
        (wholeRestartContactVelocityState current index)
        (wholeRestartNativeCausalVelocityWrite current index)) =
      ∑' wave : NonzeroIntegerWavevector,
        RCLike.re (inner ℂ
          (wholeRestartContactVelocityState current index wave)
          (wholeRestartNativeCausalVelocityWrite current index wave)) := by
  rw [lp.inner_eq_tsum]
  exact Complex.reCLM.map_tsum
    (lp.summable_inner
      (wholeRestartContactVelocityState current index)
      (wholeRestartNativeCausalVelocityWrite current index))

/-- A changed actual edge cannot be kinetically silent: its incoming
velocity pairing is strictly negative. -/
theorem wholeRestartNativeCausalVelocityWrite_ne_zero_strictly_antiAligned
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (writeNonzero :
      wholeRestartNativeCausalVelocityWrite current index ≠ 0) :
    RCLike.re (inner ℂ
      (wholeRestartContactVelocityState current index)
      (wholeRestartNativeCausalVelocityWrite current index)) < 0 := by
  have writeNormSqPos :
      0 < ‖wholeRestartNativeCausalVelocityWrite current index‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr writeNonzero)
  have boundaryNonpos :=
    wholeRestartNativeCausalVelocityWrite_quadraticBoundary_nonpos
      current index
  linarith

/-- A changed actual edge internally selects a Fourier row with a strictly
negative kinetic pairing. -/
theorem
    wholeRestartNativeCausalVelocityWrite_ne_zero_generates_negativeKineticRow
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (writeNonzero :
      wholeRestartNativeCausalVelocityWrite current index ≠ 0) :
    ∃ wave : NonzeroIntegerWavevector,
      RCLike.re (inner ℂ
        (wholeRestartContactVelocityState current index wave)
        (wholeRestartNativeCausalVelocityWrite current index wave)) < 0 := by
  have totalNegative :=
    wholeRestartNativeCausalVelocityWrite_ne_zero_strictly_antiAligned
      current index writeNonzero
  by_contra noNegative
  push Not at noNegative
  have tsumNonnegative :
      0 ≤ ∑' wave : NonzeroIntegerWavevector,
        RCLike.re (inner ℂ
          (wholeRestartContactVelocityState current index wave)
          (wholeRestartNativeCausalVelocityWrite current index wave)) :=
    tsum_nonneg noNegative
  rw [← wholeRestartNativeCausalVelocityWrite_realInner_eq_tsum current index]
    at tsumNonnegative
  linarith

/-- The energy-paying row is the exact same-edge tangent plus complete pair
innovation, and one of those two generated responsibilities is nonzero. -/
theorem
    wholeRestartNativeCausalVelocityWrite_ne_zero_generates_energyPayingDuhamelRow
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (writeNonzero :
      wholeRestartNativeCausalVelocityWrite current index ≠ 0) :
    ∃ wave : NonzeroIntegerWavevector,
      RCLike.re (inner ℂ
        (wholeRestartContactVelocityState current index wave)
        (euclideanCoordinateRow
          (biotSavartVelocityCoefficient wave.1
            (wholeRestartCausalTangentGain current index wave.1 •
                wholeRestartCrossingUnforcedTangentRow
                  current index wave.1 +
              ∑' first : IntegerWavevector,
                wholeRestartPairDuhamelInnovationOccurrence
                  current index wave.1 first)))) < 0 ∧
      (wholeRestartCrossingUnforcedTangentRow
            current index wave.1 ≠ 0 ∨
        ∃ first : IntegerWavevector,
          wholeRestartPairDuhamelInnovationOccurrence
            current index wave.1 first ≠ 0) := by
  obtain ⟨wave, negative⟩ :=
    wholeRestartNativeCausalVelocityWrite_ne_zero_generates_negativeKineticRow
      current index writeNonzero
  rw [
    wholeRestartNativeCausalVelocityWrite_apply_eq_causalTangent_add_pairInnovation]
    at negative
  refine ⟨wave, negative, ?_⟩
  by_cases tangentNonzero :
      wholeRestartCrossingUnforcedTangentRow current index wave.1 ≠ 0
  · exact Or.inl tangentNonzero
  · right
    have tangentZero := not_ne_iff.mp tangentNonzero
    by_contra noPair
    push Not at noPair
    simp [tangentZero, noPair, euclideanCoordinateRow,
      biotSavartVelocityCoefficient] at negative

/-! ## Same-edge native exhaustion of the energy-paying row -/

/-- A changed actual edge does not merely have a nonzero Duhamel row.  The
source-selected energy-paying row enters the existing same-receipt tangent
payment or pair/heat-commutator native exhaustion. -/
theorem
    wholeRestartNativeCausalVelocityWrite_ne_zero_generates_energyPaying_nativeExhaustion
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (writeNonzero :
      wholeRestartNativeCausalVelocityWrite current index ≠ 0) :
    ∃ wave : NonzeroIntegerWavevector,
      RCLike.re (inner ℂ
        (wholeRestartContactVelocityState current index wave)
        (euclideanCoordinateRow
          (biotSavartVelocityCoefficient wave.1
            (wholeRestartCausalTangentGain current index wave.1 •
                wholeRestartCrossingUnforcedTangentRow
                  current index wave.1 +
              ∑' first : IntegerWavevector,
                wholeRestartPairDuhamelInnovationOccurrence
                  current index wave.1 first)))) < 0 ∧
      ((∃ tangentNonzero :
              wholeRestartCrossingUnforcedTangentRow current index ≠ 0,
          ∃ localTime : ℝ,
            0 < localTime ∧
              localTime < (run current index).nextContact.time.1 ∧
              localTime *
                    (wholeRestartCrossingContinuousUnforcedTangentDensity
                      current index tangentNonzero 0 / 2) ≤
                  ∫ time in (0 : ℝ)..localTime,
                    wholeRestartCrossingContinuousUnforcedTangentDensity
                      current index tangentNonzero time ∧
              0 <
                ∫ time in (0 : ℝ)..localTime,
                  wholeRestartCrossingContinuousUnforcedTangentDensity
                    current index tangentNonzero time ∧
              (∫ time in (0 : ℝ)..localTime,
                  wholeRestartCrossingContinuousUnforcedTangentDensity
                    current index tangentNonzero time) ≤
                ‖(run current index).nextContact.prefixReceipt.wholeTangent‖ ^ 2) ∨
        ∃ first : IntegerWavevector,
          wholeRestartPairDuhamelInnovationOccurrence
                current index wave.1 first ≠ 0 ∧
            (wholeRestartNextPairOccurrence
                  current index wave.1 first ≠ 0 ∨
              ∃ time :
                  Icc (0 : ℝ) (run current index).nextContact.time.1,
                wholeRestartPairOccurrenceTrace
                  current index wave.1 first time ≠ 0) ∧
            (wholeRestartVelocityTriadHeatCommutatorTrace
                  current index first (wave.1 - first) = 0 ∨
              ∃ time :
                  Icc (0 : ℝ) (run current index).nextContact.time.1,
                actualWholeVelocityBilinearEnergyOccurrence
                    (run current index).nextContact.prefixReceipt
                    first (wave.1 - first) time ≠ 0 ∧
                  actualWholeContinuousVelocityPairVector
                    (run current index).nextContact.prefixReceipt
                    first (wave.1 - first) time ≠ 0 ∧
                  (wholeRestartNextVelocityPairOccurrence
                        current index first (wave.1 - first) ≠ 0 ∨
                    (linearResidualTrace
                        wholeRestartSplicedVelocityPairOccurrenceTailKeep
                        (wholeRestartSplicedVelocityPairOccurrenceTail
                          current index time 0) 0)
                          first (wave.1 - first) ≠ 0) ∧
                  run current (index + 1) =
                    (run current index).next)) := by
  obtain ⟨wave, negative, tangentOrPair⟩ :=
    wholeRestartNativeCausalVelocityWrite_ne_zero_generates_energyPayingDuhamelRow
      current index writeNonzero
  refine ⟨wave, negative, ?_⟩
  rcases tangentOrPair with tangentRowNonzero | pair
  · left
    have tangentNonzero :
        wholeRestartCrossingUnforcedTangentRow current index ≠ 0 := by
      intro tangentZero
      exact tangentRowNonzero (congrFun tangentZero wave.1)
    exact
      ⟨tangentNonzero,
        wholeRestartCrossingUnforcedTangent_positiveTimePayment
          current index tangentNonzero⟩
  · right
    rcases pair with ⟨first, innovationNonzero⟩
    obtain ⟨pairResponsibility, heatExhaustion⟩ :=
      wholeRestartPairDuhamelInnovationOccurrence_ne_zero_generates_heatCommutator_nativeExhaustion
        current index wave.1 first innovationNonzero
    exact
      ⟨first, innovationNonzero, pairResponsibility, heatExhaustion⟩

/-! ## Positive atom to the same quadratic consumer -/

/-- A positive endpoint atom cofinally generates a changed actual native
velocity edge.  The nonzero witness comes from an actual Fourier coefficient
of that edge, not from a caller-supplied branch. -/
theorem
    physicalStageKineticEnergyAtom_pos_generates_cofinal_nonzeroNativeCausalVelocityWrite
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next)
    (atomPositive : 0 < step.physicalStageKineticEnergyAtom)
    (requested : ℕ) :
    ∃ index : ℕ,
      requested ≤ index ∧
        run current (index + 1) = (run current index).next ∧
        0 < (run current index).nextContact.time.1 ∧
        wholeRestartNativeCausalVelocityWrite current index ≠ 0 := by
  obtain ⟨_physicalWrite, active⟩ :=
    physicalStageKineticEnergyAtom_pos_generates_cofinal_writtenKineticOutputSquareCausalWrite
      step atomPositive
  obtain
      ⟨writtenEarlier, _writtenLater, start, _steps, index,
        requestedLeWritten, _writtenLt, startEq, _finishEq, _stepsPositive,
        _writtenSeparation, _pathLower, startLeIndex, _indexLt,
        _outputLower, _edgeLedger, outputExists, _disposition⟩ :=
    active requested
  let endpointReceipt :=
    (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      current step.elapsedBounded).family.endpointReceipt
  have writtenLeStart : writtenEarlier ≤ start := by
    rw [startEq]
    exact endpointReceipt.subsequence_strictMono.id_le writtenEarlier
  have requestedLeIndex : requested ≤ index :=
    requestedLeWritten.trans (writtenLeStart.trans startLeIndex)
  obtain ⟨output, coefficientNonzero⟩ := outputExists
  have writeNonzero :
      wholeRestartNativeCausalVelocityWrite current index ≠ 0 := by
    intro writeZero
    have atOutput := congrArg
      (fun state : WholeRestartVelocityEndpointState => state output)
      writeZero
    have coefficientZero :
        puncturedWholeVelocityEuclideanCoefficient
          ((run current index).nextContact.physicalState -
            (run current index).contact.physicalState) output = 0 := by
      simpa [wholeRestartNativeCausalVelocityWrite] using atOutput
    exact coefficientNonzero coefficientZero
  exact
    ⟨index, requestedLeIndex, rfl,
      (run current index).nextContact.time_pos, writeNonzero⟩

/-- One actual endpoint macro step writes its generated physical successor
and internally exhausts its kinetic atom against the quadratic PDE
consumer.  In the active branch every requested index has a later same-edge
energy-paying Duhamel row and its tangent-payment or pair/heat native
redirect. -/
theorem
    wholeRestartEndpointMacroStep_generates_zero_or_energyPayingQuadraticBoundary_nativeWholeWrite
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next) :
    (wholeRestartEndpointCausalMacroFrame current step.elapsedBounded
        (wholeRestartEndpointComponentMacroUpdate accumulationRead)).1 =
        next ∧
      (step.physicalStageKineticEnergyAtom = 0 ∨
        ∀ requested : ℕ,
          ∃ index : ℕ,
            requested ≤ index ∧
              run current (index + 1) = (run current index).next ∧
              0 < (run current index).nextContact.time.1 ∧
              ∃ wave : NonzeroIntegerWavevector,
                RCLike.re (inner ℂ
                  (wholeRestartContactVelocityState current index wave)
                  (euclideanCoordinateRow
                    (biotSavartVelocityCoefficient wave.1
                      (wholeRestartCausalTangentGain
                            current index wave.1 •
                          wholeRestartCrossingUnforcedTangentRow
                            current index wave.1 +
                        ∑' first : IntegerWavevector,
                          wholeRestartPairDuhamelInnovationOccurrence
                            current index wave.1 first)))) < 0 ∧
                ((∃ tangentNonzero :
                        wholeRestartCrossingUnforcedTangentRow
                          current index ≠ 0,
                    ∃ localTime : ℝ,
                      0 < localTime ∧
                        localTime <
                          (run current index).nextContact.time.1 ∧
                        localTime *
                              (wholeRestartCrossingContinuousUnforcedTangentDensity
                                current index tangentNonzero 0 / 2) ≤
                            ∫ time in (0 : ℝ)..localTime,
                              wholeRestartCrossingContinuousUnforcedTangentDensity
                                current index tangentNonzero time ∧
                        0 <
                          ∫ time in (0 : ℝ)..localTime,
                            wholeRestartCrossingContinuousUnforcedTangentDensity
                              current index tangentNonzero time ∧
                        (∫ time in (0 : ℝ)..localTime,
                            wholeRestartCrossingContinuousUnforcedTangentDensity
                              current index tangentNonzero time) ≤
                          ‖(run current index).nextContact.prefixReceipt.wholeTangent‖ ^ 2) ∨
                  ∃ first : IntegerWavevector,
                    wholeRestartPairDuhamelInnovationOccurrence
                          current index wave.1 first ≠ 0 ∧
                      (wholeRestartNextPairOccurrence
                            current index wave.1 first ≠ 0 ∨
                        ∃ time :
                            Icc (0 : ℝ)
                              (run current index).nextContact.time.1,
                          wholeRestartPairOccurrenceTrace
                            current index wave.1 first time ≠ 0) ∧
                      (wholeRestartVelocityTriadHeatCommutatorTrace
                            current index first (wave.1 - first) = 0 ∨
                        ∃ time :
                            Icc (0 : ℝ)
                              (run current index).nextContact.time.1,
                          actualWholeVelocityBilinearEnergyOccurrence
                              (run current index).nextContact.prefixReceipt
                              first (wave.1 - first) time ≠ 0 ∧
                            actualWholeContinuousVelocityPairVector
                              (run current index).nextContact.prefixReceipt
                              first (wave.1 - first) time ≠ 0 ∧
                            (wholeRestartNextVelocityPairOccurrence
                                  current index first (wave.1 - first) ≠ 0 ∨
                              (linearResidualTrace
                                  wholeRestartSplicedVelocityPairOccurrenceTailKeep
                                  (wholeRestartSplicedVelocityPairOccurrenceTail
                                    current index time 0) 0)
                                    first (wave.1 - first) ≠ 0) ∧
                            run current (index + 1) =
                              (run current index).next))) := by
  constructor
  · cases step with
    | advance elapsedBounded =>
        exact
          (wholeRestartEndpointCausalMacroFrame_physical_update
              elapsedBounded).trans
            (sourceGeneratedWholeRestartVelocityEndpointNextCurrent_eq_rootCofinalPhysicalNext
              current elapsedBounded)
  · let endpointReceipt :=
      (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
        current step.elapsedBounded).family.endpointReceipt
    rcases endpointReceipt.kineticReceipt.defect_disposition with
      defectPositive | defectZero
    · right
      have atomPositive :
          0 < step.physicalStageKineticEnergyAtom := by
        rw [step.physicalStageKineticEnergyAtom_eq_defect]
        exact defectPositive
      intro requested
      obtain ⟨index, requestedLe, runEq, timePositive, writeNonzero⟩ :=
        physicalStageKineticEnergyAtom_pos_generates_cofinal_nonzeroNativeCausalVelocityWrite
          step atomPositive requested
      obtain ⟨wave, negative, exhaustion⟩ :=
        wholeRestartNativeCausalVelocityWrite_ne_zero_generates_energyPaying_nativeExhaustion
          current index writeNonzero
      exact
        ⟨index, requestedLe, runEq, timePositive,
          wave, negative, exhaustion⟩
    · left
      rw [step.physicalStageKineticEnergyAtom_eq_defect]
      exact defectZero.1

/-! ## Finite actual-path telescope -/

/-- The exact quadratic boundary telescopes along every actual finite native
path.  Each occurrence is charged once on its source-owned edge. -/
theorem wholeRestartFiniteCausalKineticBoundary_telescope
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν)
    (start steps : ℕ) :
    (∑ offset ∈ Finset.range steps,
      (2 * RCLike.re (inner ℂ
          (wholeRestartContactVelocityState current (start + offset))
          (wholeRestartNativeCausalVelocityWrite current (start + offset))) +
        ‖wholeRestartNativeCausalVelocityWrite
          current (start + offset)‖ ^ 2)) =
      ‖wholeRestartContactVelocityState current (start + steps)‖ ^ 2 -
        ‖wholeRestartContactVelocityState current start‖ ^ 2 := by
  simp_rw [wholeRestartNativeCausalVelocityWrite_quadraticBoundary_eq_gap]
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    Finset.sum_range_sub
      (fun offset : ℕ =>
        ‖wholeRestartContactVelocityState current (start + offset)‖ ^ 2)
      steps

/-- The finite telescope is nonpositive by the actual native kinetic
descent. -/
theorem wholeRestartFiniteCausalKineticBoundary_nonpos
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν)
    (start steps : ℕ) :
    (∑ offset ∈ Finset.range steps,
      (2 * RCLike.re (inner ℂ
          (wholeRestartContactVelocityState current (start + offset))
          (wholeRestartNativeCausalVelocityWrite current (start + offset))) +
        ‖wholeRestartNativeCausalVelocityWrite
          current (start + offset)‖ ^ 2)) ≤ 0 := by
  rw [wholeRestartFiniteCausalKineticBoundary_telescope]
  have massLe :=
    run_contact_kineticMass_antitone current
      (Nat.le_add_right start steps)
  have velocityNormLe :
      ‖wholeRestartContactVelocityState current (start + steps)‖ ^ 2 ≤
        ‖wholeRestartContactVelocityState current start‖ ^ 2 := by
    rw [wholeRestartContactVelocityState_norm_sq,
      wholeRestartContactVelocityState_norm_sq]
    exact massLe
  linarith

/-- The finite quadratic telescope retains the complete tangent/pair Duhamel
compiler inside each actual edge pairing. -/
theorem wholeRestartFiniteCausalDuhamelKineticBoundary_telescope
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν)
    (start steps : ℕ) :
    (∑ offset ∈ Finset.range steps,
      (2 * RCLike.re
          (∑' wave : NonzeroIntegerWavevector,
            inner ℂ
              (wholeRestartContactVelocityState
                current (start + offset) wave)
              (euclideanCoordinateRow
                (biotSavartVelocityCoefficient wave.1
                  (wholeRestartCausalTangentGain
                        current (start + offset) wave.1 •
                      wholeRestartCrossingUnforcedTangentRow
                        current (start + offset) wave.1 +
                    ∑' first : IntegerWavevector,
                      wholeRestartPairDuhamelInnovationOccurrence
                        current (start + offset) wave.1 first)))) +
        ‖wholeRestartNativeCausalVelocityWrite
          current (start + offset)‖ ^ 2)) =
      ‖wholeRestartContactVelocityState current (start + steps)‖ ^ 2 -
        ‖wholeRestartContactVelocityState current start‖ ^ 2 := by
  rw [← wholeRestartFiniteCausalKineticBoundary_telescope]
  apply Finset.sum_congr rfl
  intro offset _offsetMem
  congr 2
  rw [lp.inner_eq_tsum]
  apply congrArg (fun value : ℂ => RCLike.re value)
  apply tsum_congr
  intro wave
  rw [
    wholeRestartNativeCausalVelocityWrite_apply_eq_causalTangent_add_pairInnovation]

/-- The exact Duhamel quadratic boundary is nonpositive on every generated
finite native path. -/
theorem wholeRestartFiniteCausalDuhamelKineticBoundary_nonpos
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν)
    (start steps : ℕ) :
    (∑ offset ∈ Finset.range steps,
      (2 * RCLike.re
          (∑' wave : NonzeroIntegerWavevector,
            inner ℂ
              (wholeRestartContactVelocityState
                current (start + offset) wave)
              (euclideanCoordinateRow
                (biotSavartVelocityCoefficient wave.1
                  (wholeRestartCausalTangentGain
                        current (start + offset) wave.1 •
                      wholeRestartCrossingUnforcedTangentRow
                        current (start + offset) wave.1 +
                    ∑' first : IntegerWavevector,
                      wholeRestartPairDuhamelInnovationOccurrence
                        current (start + offset) wave.1 first)))) +
        ‖wholeRestartNativeCausalVelocityWrite
          current (start + offset)‖ ^ 2)) ≤ 0 := by
  rw [wholeRestartFiniteCausalDuhamelKineticBoundary_telescope]
  have massLe :=
    run_contact_kineticMass_antitone current
      (Nat.le_add_right start steps)
  have velocityNormLe :
      ‖wholeRestartContactVelocityState current (start + steps)‖ ^ 2 ≤
        ‖wholeRestartContactVelocityState current start‖ ^ 2 := by
    rw [wholeRestartContactVelocityState_norm_sq,
      wholeRestartContactVelocityState_norm_sq]
    exact massLe
  linarith

/-- A positive endpoint atom and its cofinally generated collective velocity
gap lie on the same exact quadratic Duhamel boundary telescope.  This is the
native bridge from the completion obstruction into the physical kinetic
consumer; the source chooses the complete finite path. -/
theorem
    physicalStageKineticEnergyAtom_pos_generates_cofinal_collectiveGap_with_quadraticDuhamelBoundary
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next)
    (atomPositive : 0 < step.physicalStageKineticEnergyAtom)
    (requestedStart : ℕ) :
    ∃ start steps : ℕ,
      requestedStart ≤ start ∧
        0 < steps ∧
        wholeRestartCollectiveCausalVelocityWrite current start steps =
          wholeRestartContactVelocityState current (start + steps) -
            wholeRestartContactVelocityState current start ∧
        step.physicalStageKineticEnergyAtom / 2 <
          ‖wholeRestartCollectiveCausalVelocityWrite
            current start steps‖ ^ 2 ∧
        (∑ offset ∈ Finset.range steps,
          (2 * RCLike.re
              (∑' wave : NonzeroIntegerWavevector,
                inner ℂ
                  (wholeRestartContactVelocityState
                    current (start + offset) wave)
                  (euclideanCoordinateRow
                    (biotSavartVelocityCoefficient wave.1
                      (wholeRestartCausalTangentGain
                            current (start + offset) wave.1 •
                          wholeRestartCrossingUnforcedTangentRow
                            current (start + offset) wave.1 +
                        ∑' first : IntegerWavevector,
                          wholeRestartPairDuhamelInnovationOccurrence
                            current (start + offset) wave.1 first)))) +
            ‖wholeRestartNativeCausalVelocityWrite
              current (start + offset)‖ ^ 2)) =
          ‖wholeRestartContactVelocityState current (start + steps)‖ ^ 2 -
            ‖wholeRestartContactVelocityState current start‖ ^ 2 ∧
        (∑ offset ∈ Finset.range steps,
          (2 * RCLike.re
              (∑' wave : NonzeroIntegerWavevector,
                inner ℂ
                  (wholeRestartContactVelocityState
                    current (start + offset) wave)
                  (euclideanCoordinateRow
                    (biotSavartVelocityCoefficient wave.1
                      (wholeRestartCausalTangentGain
                            current (start + offset) wave.1 •
                          wholeRestartCrossingUnforcedTangentRow
                            current (start + offset) wave.1 +
                        ∑' first : IntegerWavevector,
                          wholeRestartPairDuhamelInnovationOccurrence
                            current (start + offset) wave.1 first)))) +
            ‖wholeRestartNativeCausalVelocityWrite
              current (start + offset)‖ ^ 2)) ≤ 0 ∧
        ∀ wave : NonzeroIntegerWavevector,
          wholeRestartCollectiveCausalVelocityWrite
                current start steps wave =
            ∑ offset ∈ Finset.range steps,
              euclideanCoordinateRow
                (biotSavartVelocityCoefficient wave.1
                  (wholeRestartCausalTangentGain
                        current (start + offset) wave.1 •
                      wholeRestartCrossingUnforcedTangentRow
                        current (start + offset) wave.1 +
                    ∑' first : IntegerWavevector,
                      wholeRestartPairDuhamelInnovationOccurrence
                        current (start + offset) wave.1 first)) := by
  obtain
      ⟨start, steps, requestedLe, stepsPositive, gapEq,
        collectiveLower, compiler⟩ :=
    physicalStageKineticEnergyAtom_pos_generates_cofinal_collectiveCausalGapWrite
      step atomPositive requestedStart
  exact
    ⟨start, steps, requestedLe, stepsPositive, gapEq, collectiveLower,
      wholeRestartFiniteCausalDuhamelKineticBoundary_telescope
        current start steps,
      wholeRestartFiniteCausalDuhamelKineticBoundary_nonpos
        current start steps,
      compiler⟩

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomQuadraticBoundaryCocycle
end NavierStokes
end SaturationMonoid
