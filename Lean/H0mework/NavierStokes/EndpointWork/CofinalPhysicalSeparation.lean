import H0mework.NavierStokes.EndpointWork.NativeCausalRedirect
import H0mework.NavierStokes.KineticRestart.KineticDefectZeroVelocityCompletion

/-!
# A positive endpoint kinetic atom generates cofinal physical separation

The endpoint residual is weakly null while its square norm converges to the
source-generated kinetic atom.  A positive atom therefore does more than
prevent eventual stationarity.  After every requested native index, the
source-selected weak-endpoint lineage contains two later actual contacts
whose physical velocity distance has square strictly larger than half of the
atom.

The proof selects the second contact only after reading the first one.  Weak
nullity forces their inner product below one quarter of the atom, while both
residual square norms remain above one half of the atom.  The existing exact
velocity/kinetic isometry then transports the resulting whole-carrier
separation to the physical velocity carrier.

No index, pair of contacts, Fourier cutoff, time window, separation quantum,
branch, target state, or compactness witness is supplied by a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomCofinalPhysicalSeparation

open Filter Set
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticEndpointResidualCarrier
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDefectZeroVelocityCompletion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime.GeneratedWholeRestartEndpointMacroStep
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomNativeCausalRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingUnforcedTangentPayment
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceRateSettlement
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelTerminalTraceRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelTangentInnovation

noncomputable section

/-- A weakly null Hilbert sequence whose square norms converge to a positive
quantity is cofinally separated by more than half that quantity.  The
separation indices are generated from the two convergence laws; no modulus
or pair of indices is supplied by a caller. -/
theorem weaklyNull_normSq_tendsto_positive_generates_cofinal_separation
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    (residual : ℕ → E)
    (quantum : ℝ)
    (quantumPositive : 0 < quantum)
    (weakTendstoZero :
      ∀ test : E,
        Tendsto (fun index => inner ℂ (residual index) test)
          atTop (nhds 0))
    (normSqTendsto :
      Tendsto (fun index => ‖residual index‖ ^ 2)
        atTop (nhds quantum))
    (requestedStart : ℕ) :
    ∃ earlier later : ℕ,
      requestedStart ≤ earlier ∧
        earlier < later ∧
        quantum / 2 <
          ‖residual later - residual earlier‖ ^ 2 := by
  have eventuallyResidualLarge :
      ∀ᶠ index : ℕ in atTop,
        quantum / 2 < ‖residual index‖ ^ 2 := by
    exact normSqTendsto (eventually_gt_nhds (by linarith))
  obtain ⟨largeThreshold, residualLarge⟩ :=
    eventually_atTop.1 eventuallyResidualLarge
  let earlier := max requestedStart largeThreshold
  have requestedLeEarlier : requestedStart ≤ earlier :=
    Nat.le_max_left _ _
  have earlierResidualLarge :
      quantum / 2 < ‖residual earlier‖ ^ 2 :=
    residualLarge earlier (Nat.le_max_right _ _)
  have innerTendsto :
      Tendsto
        (fun index =>
          (inner ℂ (residual index) (residual earlier)).re)
        atTop (nhds 0) := by
    exact
      (Complex.continuous_re.tendsto 0).comp
        (weakTendstoZero (residual earlier))
  have eventuallyInnerSmall :
      ∀ᶠ index : ℕ in atTop,
        (inner ℂ (residual index) (residual earlier)).re <
          quantum / 4 := by
    exact innerTendsto (eventually_lt_nhds (by linarith))
  obtain ⟨laterThreshold, laterSpec⟩ :=
    eventually_atTop.1
      (eventuallyResidualLarge.and eventuallyInnerSmall)
  let later := max (earlier + 1) laterThreshold
  have laterGeThreshold : laterThreshold ≤ later :=
    Nat.le_max_right _ _
  have earlierLtLater : earlier < later :=
    (Nat.lt_succ_self earlier).trans_le (Nat.le_max_left _ _)
  have laterResidualLarge :
      quantum / 2 < ‖residual later‖ ^ 2 :=
    (laterSpec later laterGeThreshold).1
  have innerSmall :
      (inner ℂ (residual later) (residual earlier)).re <
        quantum / 4 :=
    (laterSpec later laterGeThreshold).2
  change
    RCLike.re (inner ℂ (residual later) (residual earlier)) <
      quantum / 4 at innerSmall
  have separation :
      quantum / 2 <
        ‖residual later - residual earlier‖ ^ 2 := by
    rw [norm_sub_sq (𝕜 := ℂ)]
    linarith
  exact
    ⟨earlier, later, requestedLeEarlier, earlierLtLater, separation⟩

theorem norm_adjacent_path_sq_le_count_mul_sum_sq
    {E : Type*}
    [SeminormedAddCommGroup E]
    (state : ℕ → E)
    (start steps : ℕ) :
    ‖state (start + steps) - state start‖ ^ 2 ≤
      (steps : ℝ) *
        ∑ offset ∈ Finset.range steps,
          ‖state (start + offset + 1) -
              state (start + offset)‖ ^ 2 := by
  have telescope :
      (∑ offset ∈ Finset.range steps,
          (state (start + offset + 1) -
            state (start + offset))) =
        state (start + steps) - state start := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Finset.sum_range_sub
        (fun offset : ℕ => state (start + offset)) steps
  have normLe :
      ‖state (start + steps) - state start‖ ≤
        ∑ offset ∈ Finset.range steps,
          ‖state (start + offset + 1) -
            state (start + offset)‖ := by
    rw [← telescope]
    exact norm_sum_le _ _
  have normSqLe :
      ‖state (start + steps) - state start‖ ^ 2 ≤
        (∑ offset ∈ Finset.range steps,
          ‖state (start + offset + 1) -
            state (start + offset)‖) ^ 2 := by
    exact
      (sq_le_sq₀
        (norm_nonneg _)
        (Finset.sum_nonneg fun _ _ => norm_nonneg _)).2 normLe
  have cauchy :=
    Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.range steps)
      (fun _ => (1 : ℝ))
      (fun offset =>
        ‖state (start + offset + 1) -
          state (start + offset)‖)
  have count :
      (∑ _offset ∈ Finset.range steps, (1 : ℝ)) =
        (steps : ℝ) := by
    simp
  simp only [one_mul, one_pow] at cauchy
  rw [count] at cauchy
  exact normSqLe.trans cauchy

theorem exists_native_edge_above_diluted_path_quantum
    (values : ℕ → ℝ)
    {steps : ℕ}
    (stepsPositive : 0 < steps)
    {quantum : ℝ}
    (pathLower :
      quantum / 2 <
        (steps : ℝ) *
          ∑ offset ∈ Finset.range steps, values offset) :
    ∃ offset ∈ Finset.range steps,
      quantum / (2 * (steps : ℝ) ^ 2) < values offset := by
  by_contra noLargeEdge
  have eachLe :
      ∀ offset ∈ Finset.range steps,
        values offset ≤ quantum / (2 * (steps : ℝ) ^ 2) := by
    intro offset offsetMem
    by_contra notLe
    exact noLargeEdge
      ⟨offset, offsetMem, lt_of_not_ge notLe⟩
  have sumLe :
      (∑ offset ∈ Finset.range steps, values offset) ≤
        ∑ _offset ∈ Finset.range steps,
          quantum / (2 * (steps : ℝ) ^ 2) :=
    Finset.sum_le_sum eachLe
  have constantSum :
      (∑ _offset ∈ Finset.range steps,
          quantum / (2 * (steps : ℝ) ^ 2)) =
        (steps : ℝ) *
          (quantum / (2 * (steps : ℝ) ^ 2)) := by
    simp
  rw [constantSum] at sumLe
  have stepsRealPositive : 0 < (steps : ℝ) := by
    exact_mod_cast stepsPositive
  have scaledLe :=
    mul_le_mul_of_nonneg_left sumLe stepsRealPositive.le
  have scaleIdentity :
      (steps : ℝ) *
          ((steps : ℝ) *
            (quantum / (2 * (steps : ℝ) ^ 2))) =
        quantum / 2 := by
    field_simp [stepsRealPositive.ne']
  rw [scaleIdentity] at scaledLe
  exact (not_lt_of_ge scaledLe) pathLower

theorem nativeVelocityIncrement_norm_sq_eq_tsum
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    ‖wholeRestartContactVelocityState initial (index + 1) -
        wholeRestartContactVelocityState initial index‖ ^ 2 =
      ∑' wave :
          ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger.NonzeroIntegerWavevector,
        ‖puncturedWholeVelocityEuclideanCoefficient
          ((run initial index).nextContact.physicalState -
            (run initial index).contact.physicalState) wave‖ ^ 2 := by
  unfold wholeRestartContactVelocityState
  rw [run_succ]
  change
    ‖puncturedWholeVelocityEuclideanState
          (run initial index).nextContact.physicalState -
        puncturedWholeVelocityEuclideanState
          (run initial index).contact.physicalState‖ ^ 2 = _
  rw [← puncturedWholeVelocityEuclideanState_sub]
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
      puncturedWholeVelocityEuclideanState_apply] using
    (lp.norm_rpow_eq_tsum
      (p := (2 : ENNReal)) (by norm_num)
      (puncturedWholeVelocityEuclideanState
        ((run initial index).nextContact.physicalState -
          (run initial index).contact.physicalState)))

/-- A velocity coefficient visible before the Fourier quotient belongs to
the same native physical edge as its vorticity increment.  Its nonzero
visibility therefore enters the exact tangent/pair next-or-trace
disposition at that output; no separate output or crossing branch is
chosen by a caller. -/
theorem nativeVelocityCoefficient_ne_zero_generates_causalResponsibility
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (wave :
      ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger.NonzeroIntegerWavevector)
    (coefficientNonzero :
      puncturedWholeVelocityEuclideanCoefficient
        ((run initial index).nextContact.physicalState -
          (run initial index).contact.physicalState) wave ≠ 0) :
    wave.1 ≠ 0 ∧
      (run initial index).nextContact.physicalState wave.1 -
          (run initial index).contact.physicalState wave.1 ≠ 0 ∧
      (run initial index).nextContact.physicalState wave.1 -
            (run initial index).contact.physicalState wave.1 =
          wholeRestartCausalTangentGain initial index wave.1 •
              wholeRestartCrossingUnforcedTangentRow
                initial index wave.1 +
            (∑' first : IntegerWavevector,
              wholeRestartPairDuhamelInnovationOccurrence
                initial index wave.1 first) ∧
      (wholeRestartCrossingUnforcedTangentRow
            initial index wave.1 ≠ 0 ∨
        ∃ first : IntegerWavevector,
          wholeRestartPairDuhamelInnovationOccurrence
                initial index wave.1 first ≠ 0 ∧
            (wholeRestartNextPairOccurrence
                  initial index wave.1 first ≠ 0 ∨
              ∃ time :
                  Icc (0 : ℝ)
                    (run initial index).nextContact.time.1,
                wholeRestartPairOccurrenceTrace
                  initial index wave.1 first time ≠ 0)) := by
  have rowNonzero :
      (run initial index).nextContact.physicalState wave.1 -
          (run initial index).contact.physicalState wave.1 ≠ 0 := by
    intro rowZero
    apply coefficientNonzero
    unfold puncturedWholeVelocityEuclideanCoefficient
    have differenceZero :
        ((run initial index).nextContact.physicalState -
            (run initial index).contact.physicalState) wave.1 = 0 := by
      rw [lp.coeFn_sub]
      exact rowZero
    rw [differenceZero, biotSavartVelocityCoefficient_zero_vorticity]
    rfl
  obtain ⟨outputNonzero, causalSplit, responsibility⟩ :=
    nativeOutputIncrement_ne_zero_generates_causalResponsibility
      initial index wave.1 rowNonzero
  exact
    ⟨outputNonzero, rowNonzero, causalSplit, responsibility⟩

/-- A positive endpoint atom generates two cofinally late actual native
contacts separated by more than half that atom in physical velocity square
distance.  The positive quantum is the atom generated by the macro stage
itself. -/
theorem
    physicalStageKineticEnergyAtom_pos_generates_cofinal_physicalSeparation
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next)
    (atomPositive : 0 < step.physicalStageKineticEnergyAtom)
    (requestedStart : ℕ) :
    ∃ earlier later : ℕ,
      requestedStart ≤ earlier ∧
        earlier < later ∧
        step.physicalStageKineticEnergyAtom / 2 <
          ‖wholeRestartContactVelocityState current later -
              wholeRestartContactVelocityState current earlier‖ ^ 2 := by
  let endpointReceipt :=
    (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      current step.elapsedBounded).family.endpointReceipt
  let receipt :=
    endpointReceipt.kineticReceipt.toGeneratedWholeRestartKineticWeakEndpoint
  have weakTendstoZero :
      ∀ test : WholeRestartKineticEndpointState,
        Tendsto
          (fun index =>
            inner ℂ
              (wholeRestartKineticEndpointResidual
                current receipt index) test)
          atTop (nhds 0) :=
    wholeRestartKineticEndpointResidual_weak_tendsto_zero receipt
  have normSqTendsto :
      Tendsto
        (fun index =>
          ‖wholeRestartKineticEndpointResidual
            current receipt index‖ ^ 2)
        atTop
        (nhds step.physicalStageKineticEnergyAtom) := by
    simpa only [step.physicalStageKineticEnergyAtom_eq_defect] using
      wholeRestartKineticEndpointResidual_norm_sq_tendsto_defect receipt
  obtain
      ⟨earlierSelected, laterSelected, requestedLeSelected,
        earlierSelectedLtLater, residualSeparation⟩ :=
    weaklyNull_normSq_tendsto_positive_generates_cofinal_separation
      (fun index =>
        wholeRestartKineticEndpointResidual current receipt index)
      step.physicalStageKineticEnergyAtom atomPositive
      weakTendstoZero normSqTendsto requestedStart
  let earlier := receipt.subsequence earlierSelected
  let later := receipt.subsequence laterSelected
  have requestedLeEarlier : requestedStart ≤ earlier := by
    exact
      requestedLeSelected.trans
        (receipt.subsequence_strictMono.id_le earlierSelected)
  have earlierLtLater : earlier < later :=
    receipt.subsequence_strictMono earlierSelectedLtLater
  have kineticDifference :
      wholeRestartKineticEndpointResidual current receipt laterSelected -
          wholeRestartKineticEndpointResidual current receipt earlierSelected =
        wholeRestartContactKineticState current later -
          wholeRestartContactKineticState current earlier := by
    simp only [wholeRestartKineticEndpointResidual, later, earlier]
    abel
  have kineticSeparation :
      step.physicalStageKineticEnergyAtom / 2 <
        ‖wholeRestartContactKineticState current later -
            wholeRestartContactKineticState current earlier‖ ^ 2 := by
    rw [← kineticDifference]
    exact residualSeparation
  refine ⟨earlier, later, requestedLeEarlier, earlierLtLater, ?_⟩
  rw [wholeRestartContactVelocityState_sub_norm_sq_eq_kinetic]
  exact kineticSeparation

/-- The same source-generated separation is paid on the literal finite
native gap.  The right side is the square ledger of every adjacent physical
velocity increment before any Fourier or pair quotient; the only dilution
factor is the actual number of native edges generated between the two
selected contacts. -/
theorem
    physicalStageKineticEnergyAtom_pos_generates_cofinal_nativeGapSquare
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next)
    (atomPositive : 0 < step.physicalStageKineticEnergyAtom)
    (requestedStart : ℕ) :
    ∃ start steps : ℕ,
      requestedStart ≤ start ∧
        0 < steps ∧
        step.physicalStageKineticEnergyAtom / 2 <
          (steps : ℝ) *
            ∑ offset ∈ Finset.range steps,
              ‖wholeRestartContactVelocityState
                    current (start + offset + 1) -
                  wholeRestartContactVelocityState
                    current (start + offset)‖ ^ 2 := by
  obtain ⟨earlier, later, requestedLe, earlierLtLater, separation⟩ :=
    physicalStageKineticEnergyAtom_pos_generates_cofinal_physicalSeparation
      step atomPositive requestedStart
  let steps := later - earlier
  have stepsPositive : 0 < steps := by
    dsimp only [steps]
    omega
  have laterEq : later = earlier + steps := by
    dsimp only [steps]
    omega
  have pathBound :=
    norm_adjacent_path_sq_le_count_mul_sum_sq
      (wholeRestartContactVelocityState current) earlier steps
  rw [← laterEq] at pathBound
  exact
    ⟨earlier, steps, requestedLe, stepsPositive,
      separation.trans_le pathBound⟩

/-- The quantitative native-gap square and its actual causal write are
generated together.  The source selects a changed literal edge inside the
same gap that carries the `atom / 2` path responsibility, and that edge
enters the exact tangent/pair next-or-trace disposition. -/
theorem
    physicalStageKineticEnergyAtom_pos_generates_cofinal_nativeGapCausalSettlement
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next)
    (atomPositive : 0 < step.physicalStageKineticEnergyAtom)
    (requestedStart : ℕ) :
    ∃ start steps : ℕ,
      requestedStart ≤ start ∧
        0 < steps ∧
        step.physicalStageKineticEnergyAtom / 2 <
          (steps : ℝ) *
            ∑ offset ∈ Finset.range steps,
              ‖wholeRestartContactVelocityState
                    current (start + offset + 1) -
                  wholeRestartContactVelocityState
                    current (start + offset)‖ ^ 2 ∧
        ∃ index : ℕ,
          start ≤ index ∧
            index < start + steps ∧
            step.physicalStageKineticEnergyAtom /
                  (2 * (steps : ℝ) ^ 2) <
                ‖wholeRestartContactVelocityState current (index + 1) -
                    wholeRestartContactVelocityState current index‖ ^ 2 ∧
            ∃ output : IntegerWavevector,
              output ≠ 0 ∧
                (run current index).nextContact.physicalState output -
                    (run current index).contact.physicalState output ≠ 0 ∧
                (run current index).nextContact.physicalState output -
                      (run current index).contact.physicalState output =
                    wholeRestartCausalTangentGain
                          current index output •
                        wholeRestartCrossingUnforcedTangentRow
                          current index output +
                      (∑' first : IntegerWavevector,
                        wholeRestartPairDuhamelInnovationOccurrence
                          current index output first) ∧
                (wholeRestartCrossingUnforcedTangentRow
                      current index output ≠ 0 ∨
                  ∃ first : IntegerWavevector,
                    wholeRestartPairDuhamelInnovationOccurrence
                          current index output first ≠ 0 ∧
                      (wholeRestartNextPairOccurrence
                            current index output first ≠ 0 ∨
                        ∃ time :
                            Icc (0 : ℝ)
                              (run current index).nextContact.time.1,
                          wholeRestartPairOccurrenceTrace
                            current index output first time ≠ 0)) := by
  obtain ⟨earlier, later, requestedLe, earlierLtLater, separation⟩ :=
    physicalStageKineticEnergyAtom_pos_generates_cofinal_physicalSeparation
      step atomPositive requestedStart
  let steps := later - earlier
  have stepsPositive : 0 < steps := by
    dsimp only [steps]
    omega
  have laterEq : later = earlier + steps := by
    dsimp only [steps]
    omega
  have pathBound :=
    norm_adjacent_path_sq_le_count_mul_sum_sq
      (wholeRestartContactVelocityState current) earlier steps
  rw [← laterEq] at pathBound
  have pathLower :
      step.physicalStageKineticEnergyAtom / 2 <
        (steps : ℝ) *
          ∑ offset ∈ Finset.range steps,
            ‖wholeRestartContactVelocityState
                  current (earlier + offset + 1) -
                wholeRestartContactVelocityState
                  current (earlier + offset)‖ ^ 2 :=
    separation.trans_le pathBound
  obtain ⟨offset, offsetMem, edgeLarge⟩ :=
    exists_native_edge_above_diluted_path_quantum
      (fun offset =>
        ‖wholeRestartContactVelocityState
              current (earlier + offset + 1) -
            wholeRestartContactVelocityState
              current (earlier + offset)‖ ^ 2)
      stepsPositive pathLower
  let index := earlier + offset
  have offsetLt : offset < steps :=
    Finset.mem_range.mp offsetMem
  have earlierLeIndex : earlier ≤ index :=
    Nat.le_add_right earlier offset
  have indexLtLater : index < later := by
    rw [laterEq]
    exact Nat.add_lt_add_left offsetLt earlier
  have edgeLargeAtIndex :
      step.physicalStageKineticEnergyAtom /
            (2 * (steps : ℝ) ^ 2) <
        ‖wholeRestartContactVelocityState current (index + 1) -
            wholeRestartContactVelocityState current index‖ ^ 2 := by
    simpa [index, Nat.add_assoc] using edgeLarge
  have stepsRealPositive : 0 < (steps : ℝ) := by
    exact_mod_cast stepsPositive
  have dilutedQuantumPositive :
      0 <
        step.physicalStageKineticEnergyAtom /
          (2 * (steps : ℝ) ^ 2) := by
    exact div_pos atomPositive
      (mul_pos (by norm_num) (sq_pos_of_pos stepsRealPositive))
  have velocityEdgeNe :
      wholeRestartContactVelocityState current (index + 1) ≠
        wholeRestartContactVelocityState current index := by
    intro velocityEq
    rw [velocityEq, sub_self, norm_zero] at edgeLargeAtIndex
    norm_num at edgeLargeAtIndex
    linarith
  have nativeStateNe :
      (run current index).nextContact.physicalState ≠
        (run current index).contact.physicalState := by
    intro nextEq
    apply velocityEdgeNe
    unfold wholeRestartContactVelocityState
    rw [run_succ]
    change
      puncturedWholeVelocityEuclideanState
          (run current index).nextContact.physicalState =
        puncturedWholeVelocityEuclideanState
          (run current index).contact.physicalState
    rw [nextEq]
  have causalResponsibility :=
    nativePhysicalChange_generates_causalResponsibility
      current index nativeStateNe
  exact
    ⟨earlier, steps, requestedLe, stepsPositive,
      pathLower,
      index, earlierLeIndex, by simpa [laterEq] using indexLtLater,
      edgeLargeAtIndex,
      causalResponsibility⟩

/-- The source-generated positive atom reaches the pre-quotient Fourier
carrier on one quantitatively large native edge.  The complete velocity
square is retained as an exact sum over all nonzero output occurrences,
that support is nonempty, and every visible occurrence on the selected edge
has its own same-edge tangent/pair next-or-trace settlement.  Hence a
coefficient cancellation after projection cannot erase an unpaid output
responsibility. -/
theorem
    physicalStageKineticEnergyAtom_pos_generates_cofinal_outputSquareCausalSettlement
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next)
    (atomPositive : 0 < step.physicalStageKineticEnergyAtom)
    (requestedStart : ℕ) :
    ∃ start steps index : ℕ,
      requestedStart ≤ start ∧
        0 < steps ∧
        start ≤ index ∧
        index < start + steps ∧
        step.physicalStageKineticEnergyAtom / 2 <
          (steps : ℝ) *
            ∑ offset ∈ Finset.range steps,
              ‖wholeRestartContactVelocityState
                    current (start + offset + 1) -
                  wholeRestartContactVelocityState
                    current (start + offset)‖ ^ 2 ∧
        step.physicalStageKineticEnergyAtom /
              (2 * (steps : ℝ) ^ 2) <
            ∑' wave :
                ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger.NonzeroIntegerWavevector,
              ‖puncturedWholeVelocityEuclideanCoefficient
                ((run current index).nextContact.physicalState -
                  (run current index).contact.physicalState) wave‖ ^ 2 ∧
        ‖wholeRestartContactVelocityState current (index + 1) -
            wholeRestartContactVelocityState current index‖ ^ 2 =
          ∑' wave :
              ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger.NonzeroIntegerWavevector,
            ‖puncturedWholeVelocityEuclideanCoefficient
              ((run current index).nextContact.physicalState -
                (run current index).contact.physicalState) wave‖ ^ 2 ∧
        (∃ wave :
            ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger.NonzeroIntegerWavevector,
          puncturedWholeVelocityEuclideanCoefficient
            ((run current index).nextContact.physicalState -
              (run current index).contact.physicalState) wave ≠ 0) ∧
        ∀ wave :
            ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger.NonzeroIntegerWavevector,
          puncturedWholeVelocityEuclideanCoefficient
              ((run current index).nextContact.physicalState -
                (run current index).contact.physicalState) wave ≠ 0 →
            wave.1 ≠ 0 ∧
              (run current index).nextContact.physicalState wave.1 -
                  (run current index).contact.physicalState wave.1 ≠ 0 ∧
              (run current index).nextContact.physicalState wave.1 -
                    (run current index).contact.physicalState wave.1 =
                  wholeRestartCausalTangentGain
                        current index wave.1 •
                      wholeRestartCrossingUnforcedTangentRow
                        current index wave.1 +
                    (∑' first : IntegerWavevector,
                      wholeRestartPairDuhamelInnovationOccurrence
                        current index wave.1 first) ∧
              (wholeRestartCrossingUnforcedTangentRow
                    current index wave.1 ≠ 0 ∨
                ∃ first : IntegerWavevector,
                  wholeRestartPairDuhamelInnovationOccurrence
                        current index wave.1 first ≠ 0 ∧
                    (wholeRestartNextPairOccurrence
                          current index wave.1 first ≠ 0 ∨
                      ∃ time :
                          Icc (0 : ℝ)
                            (run current index).nextContact.time.1,
                        wholeRestartPairOccurrenceTrace
                          current index wave.1 first time ≠ 0)) := by
  obtain
    ⟨start, steps, requestedLe, stepsPositive, pathLower,
      index, startLeIndex, indexLtEnd, edgeLarge, _⟩ :=
    physicalStageKineticEnergyAtom_pos_generates_cofinal_nativeGapCausalSettlement
      step atomPositive requestedStart
  have edgeLedger :=
    nativeVelocityIncrement_norm_sq_eq_tsum current index
  have outputSquareLower :
      step.physicalStageKineticEnergyAtom /
            (2 * (steps : ℝ) ^ 2) <
          ∑' wave :
              ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger.NonzeroIntegerWavevector,
            ‖puncturedWholeVelocityEuclideanCoefficient
              ((run current index).nextContact.physicalState -
                (run current index).contact.physicalState) wave‖ ^ 2 := by
    rw [← edgeLedger]
    exact edgeLarge
  have stepsRealPositive : 0 < (steps : ℝ) := by
    exact_mod_cast stepsPositive
  have dilutedQuantumPositive :
      0 <
        step.physicalStageKineticEnergyAtom /
          (2 * (steps : ℝ) ^ 2) := by
    exact div_pos atomPositive
      (mul_pos (by norm_num) (sq_pos_of_pos stepsRealPositive))
  have outputExists :
      ∃ wave :
          ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger.NonzeroIntegerWavevector,
        puncturedWholeVelocityEuclideanCoefficient
          ((run current index).nextContact.physicalState -
            (run current index).contact.physicalState) wave ≠ 0 := by
    by_contra noOutput
    simp only [not_exists, not_not] at noOutput
    have outputSquareZero :
        (∑' wave :
            ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger.NonzeroIntegerWavevector,
          ‖puncturedWholeVelocityEuclideanCoefficient
            ((run current index).nextContact.physicalState -
              (run current index).contact.physicalState) wave‖ ^ 2) = 0 := by
      simp [noOutput]
    rw [outputSquareZero] at outputSquareLower
    linarith
  refine
    ⟨start, steps, index, requestedLe, stepsPositive,
      startLeIndex, indexLtEnd, pathLower, outputSquareLower,
      edgeLedger, outputExists, ?_⟩
  intro wave coefficientNonzero
  exact
    nativeVelocityCoefficient_ne_zero_generates_causalResponsibility
      current index wave coefficientNonzero

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomCofinalPhysicalSeparation
end NavierStokes
end SaturationMonoid
