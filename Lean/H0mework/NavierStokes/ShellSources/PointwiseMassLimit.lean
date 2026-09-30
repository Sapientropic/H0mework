import H0mework.NavierStokes.ShellSources.CriticalSerrinWeakLimit

/-!
# Pointwise mass inherited by the generated whole-state limit

The strict-critical source trajectories have a cutoff-independent
coefficient-enstrophy ceiling at every physical time.  Strong convergence
in the actual whole space-time `L²` carrier yields a further subsequence
converging pointwise almost everywhere.  The same ceiling therefore passes
to the generated whole-state limit.

The final theorem converts the ambient `ℓ²(ℤ³; ℂ³_sup)` bound to the
Euclidean Fourier mass needed by the nonlinear negative-one estimate.  Its
factor `3` is exactly the fixed coordinate comparison, not a shell-count
loss.  No pointwise limit, convergence witness, mass bound, cutoff, or
restart state is supplied as a premise.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPointwiseMassLimit

open scoped BigOperators ENNReal Topology

open Set
open Filter
open MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientGeneratedPathCriticalAbsorption
open ThreeDimensionalVorticityCoefficientGeneratedPathFiniteObservedCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare.GeneratedIntegerShellInfiniteLineage
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageCriticalPathCompactness
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellCriticalSerrinWeakLimit

noncomputable section

/-! ## Exact Euclidean mass continuity on the whole carrier -/

/--
One physical coordinate observed across every integer Fourier row.

Keeping the three coordinate slices separate makes Euclidean Fourier mass
a continuous quadratic functional of the actual whole state; no conversion
through the row sup norm is needed.
-/
def pointwiseMassCoordinateSliceCLM
    (coordinate : Coordinate) :
    ComplexVorticityHilbertState →L[ℂ]
      lp (fun _ : IntegerWavevector => ℂ) 2 :=
  lp.mapCLM 2
    (fun _wave =>
      (ContinuousLinearMap.proj coordinate :
        ComplexCoordinateVector →L[ℂ] ℂ))
    zero_le_one
    (fun _wave => by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro vector
      simpa only [one_mul, ContinuousLinearMap.proj_apply] using
        norm_le_pi_norm vector coordinate)

@[simp] theorem pointwiseMassCoordinateSliceCLM_apply
    (coordinate : Coordinate)
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) :
    pointwiseMassCoordinateSliceCLM coordinate state wave =
      state wave coordinate :=
  rfl

/--
The physical Euclidean Fourier mass is exactly the finite sum of the
squared norms of its three whole-lattice coordinate slices.
-/
theorem wholeVorticityEuclideanMass_eq_pointwiseMassCoordinateSlices
    (state : ComplexVorticityHilbertState) :
    wholeVorticityEuclideanMass state =
      ∑ coordinate : Coordinate,
        ‖pointwiseMassCoordinateSliceCLM coordinate state‖ ^ 2 := by
  unfold wholeVorticityEuclideanMass
  rw [show
    (fun wave : IntegerWavevector =>
      vorticityRowAmplitude state wave ^ 2) =
        (fun wave : IntegerWavevector =>
          complexCoordinateAmplitudeSq (state wave)) by
      funext wave
      exact vorticityRowAmplitude_sq state wave]
  unfold complexCoordinateAmplitudeSq
  simp_rw [Complex.normSq_eq_norm_sq]
  have coordinateSummable :
      ∀ coordinate : Coordinate,
        Summable fun wave : IntegerWavevector =>
          ‖state wave coordinate‖ ^ 2 := by
    intro coordinate
    have summableSlice :=
      (lp.hasSum_norm
        (p := (2 : ℝ≥0∞)) (by norm_num)
        (pointwiseMassCoordinateSliceCLM coordinate state)).summable
    convert summableSlice using 1
    all_goals
      norm_num [pointwiseMassCoordinateSliceCLM_apply]
  rw [Summable.tsum_finsetSum
    (fun coordinate _coordinateMem =>
      coordinateSummable coordinate)]
  apply Finset.sum_congr rfl
  intro coordinate coordinateMem
  have normIdentity :=
    lp.norm_rpow_eq_tsum
      (p := (2 : ℝ≥0∞)) (by norm_num)
      (pointwiseMassCoordinateSliceCLM coordinate state)
  norm_num at normIdentity
  rw [normIdentity]

/--
Strong convergence in the actual whole Fourier carrier preserves exact
Euclidean coordinate mass, not merely its three-times-sup-norm envelope.
-/
theorem tendsto_wholeVorticityEuclideanMass
    {α : Type*}
    {filter : Filter α}
    {states : α → ComplexVorticityHilbertState}
    {limit : ComplexVorticityHilbertState}
    (statesTendsto : Tendsto states filter (𝓝 limit)) :
    Tendsto
      (fun index =>
        wholeVorticityEuclideanMass (states index))
      filter
      (𝓝 (wholeVorticityEuclideanMass limit)) := by
  rw [show
      (fun index =>
        wholeVorticityEuclideanMass (states index)) =
        (fun index =>
          ∑ coordinate : Coordinate,
            ‖pointwiseMassCoordinateSliceCLM coordinate
              (states index)‖ ^ 2) by
        funext index
        exact
          wholeVorticityEuclideanMass_eq_pointwiseMassCoordinateSlices
            (states index)]
  rw [wholeVorticityEuclideanMass_eq_pointwiseMassCoordinateSlices limit]
  apply tendsto_finsetSum Finset.univ
  intro coordinate coordinateMem
  exact
    (((pointwiseMassCoordinateSliceCLM coordinate).continuous.tendsto
      limit).comp statesTendsto).norm.pow 2

/--
Every actual generated finite-cutoff trajectory satisfies the common
whole-carrier pointwise ceiling.  The bound is read directly from its
critical enstrophy barrier and physical support law.
-/
theorem GeneratedCriticalScalePath.generatedWholeTrajectory_norm_sq_le_ceiling
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    (θLtOne : θ < 1)
    (requestedTimePos : 0 < requestedTime)
    (path : GeneratedCriticalScalePath ν θ)
    (time : Icc (0 : ℝ) requestedTime) :
    ‖generatedWholeTrajectory
        θLtOne requestedTimePos path time‖ ^ 2 ≤
      criticalCoefficientEnstrophyCeiling ν θ := by
  let budget :=
    path.commonTimeBudget θLtOne requestedTimePos
  have currentEnstrophyLeInitial :
      finiteStateVorticityCoefficientEnstrophy
          (generatedSupport path.current)
          (budget.trajectory time.1) ≤
        finiteStateVorticityCoefficientEnstrophy
          (generatedSupport path.current)
          (budget.trajectory 0) := by
    have halfLe :=
      (budget.criticalBarrier time.1 time.2).1
    unfold finiteStateVorticityHalfEnstrophy at halfLe
    linarith
  have initialEnstrophyLe :
      finiteStateVorticityCoefficientEnstrophy
          (generatedSupport path.current)
          (budget.trajectory 0) ≤
        criticalCoefficientEnstrophyCeiling ν θ := by
    rw [budget.initial]
    exact path.initialEnstrophy_le_ceiling
  have ambientSqLe :
      ‖budget.trajectory time.1‖ ^ 2 ≤
        finiteStateVorticityCoefficientEnstrophy
          (generatedSupport path.current)
          (budget.trajectory time.1) :=
    complexVorticityHilbertState_norm_sq_le_coefficientEnstrophy
      (generatedSupport path.current)
      (budget.trajectory time.1)
      (budget.physicalProperties time.1 time.2).2.1
  change ‖budget.trajectory time.1‖ ^ 2 ≤ _
  exact
    ambientSqLe.trans
      (currentEnstrophyLeInitial.trans initialEnstrophyLe)

/--
Every actual finite-cutoff trajectory satisfies the same critical ceiling
in the physical Euclidean coefficient mass itself.
-/
theorem
    GeneratedCriticalScalePath.generatedWholeTrajectory_euclideanMass_le_ceiling
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    (θLtOne : θ < 1)
    (requestedTimePos : 0 < requestedTime)
    (path : GeneratedCriticalScalePath ν θ)
    (time : Icc (0 : ℝ) requestedTime) :
    wholeVorticityEuclideanMass
        (generatedWholeTrajectory
          θLtOne requestedTimePos path time) ≤
      criticalCoefficientEnstrophyCeiling ν θ := by
  let budget :=
    path.commonTimeBudget θLtOne requestedTimePos
  have currentEnstrophyLeInitial :
      finiteStateVorticityCoefficientEnstrophy
          (generatedSupport path.current)
          (budget.trajectory time.1) ≤
        finiteStateVorticityCoefficientEnstrophy
          (generatedSupport path.current)
          (budget.trajectory 0) := by
    have halfLe :=
      (budget.criticalBarrier time.1 time.2).1
    unfold finiteStateVorticityHalfEnstrophy at halfLe
    linarith
  have initialEnstrophyLe :
      finiteStateVorticityCoefficientEnstrophy
          (generatedSupport path.current)
          (budget.trajectory 0) ≤
        criticalCoefficientEnstrophyCeiling ν θ := by
    rw [budget.initial]
    exact path.initialEnstrophy_le_ceiling
  have supported :
      ∀ wave : IntegerWavevector,
        wave ∉ generatedSupport path.current →
          budget.trajectory time.1 wave = 0 :=
    (budget.physicalProperties time.1 time.2).2.1
  change
    wholeVorticityEuclideanMass
        (budget.trajectory time.1) ≤
      criticalCoefficientEnstrophyCeiling ν θ
  rw [wholeVorticityEuclideanMass_eq_finite_of_supported
    (generatedSupport path.current)
    (budget.trajectory time.1) supported]
  exact currentEnstrophyLeInitial.trans initialEnstrophyLe

/--
The `Lp` representative of every generated finite-cutoff trajectory obeys
the same pointwise ceiling almost everywhere.
-/
theorem generatedCriticalSpaceTimePath_norm_sq_ae_le_ceiling
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    (θLtOne : θ < 1)
    (requestedTimePos : 0 < requestedTime)
    (path : GeneratedCriticalScalePath ν θ) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      ‖generatedCriticalSpaceTimePath
          θLtOne requestedTimePos path time‖ ^ 2 ≤
        criticalCoefficientEnstrophyCeiling ν θ := by
  have coeFnEq :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure requestedTime)
      ℂ
      (generatedWholeBoundedPath
        θLtOne requestedTimePos path)
  filter_upwards [coeFnEq] with time timeEq
  change
    ‖((BoundedContinuousFunction.toLp 2
        (commonTimeMeasure requestedTime) ℂ)
        (generatedWholeBoundedPath
          θLtOne requestedTimePos path)) time‖ ^ 2 ≤ _
  rw [timeEq]
  exact
    GeneratedCriticalScalePath.generatedWholeTrajectory_norm_sq_le_ceiling
      θLtOne requestedTimePos path time

/--
The actual time-`L²` representative retains the Euclidean coefficient
ceiling almost everywhere, before any limit is taken.
-/
theorem generatedCriticalSpaceTimePath_euclideanMass_ae_le_ceiling
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    (θLtOne : θ < 1)
    (requestedTimePos : 0 < requestedTime)
    (path : GeneratedCriticalScalePath ν θ) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      wholeVorticityEuclideanMass
          (generatedCriticalSpaceTimePath
            θLtOne requestedTimePos path time) ≤
        criticalCoefficientEnstrophyCeiling ν θ := by
  have coeFnEq :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure requestedTime)
      ℂ
      (generatedWholeBoundedPath
        θLtOne requestedTimePos path)
  filter_upwards [coeFnEq] with time timeEq
  change
    wholeVorticityEuclideanMass
        (((BoundedContinuousFunction.toLp 2
          (commonTimeMeasure requestedTime) ℂ)
          (generatedWholeBoundedPath
            θLtOne requestedTimePos path)) time) ≤ _
  rw [timeEq]
  exact
    GeneratedCriticalScalePath.generatedWholeTrajectory_euclideanMass_le_ceiling
      θLtOne requestedTimePos path time

/--
Strong convergence of the generated Galerkin sequence transports the
pointwise whole-carrier ceiling to the actual weak-limit state.

The almost-everywhere convergent subsequence is generated from the receipt's
own `state_tendsto`; it is not supplied by the caller.
-/
theorem CriticalSerrinWeakLimitReceipt.stateLimit_norm_sq_ae_le_generated
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}
    (receipt :
      CriticalSerrinWeakLimitReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      ‖receipt.stateLimit time‖ ^ 2 ≤
        criticalCoefficientEnstrophyCeiling ν θ := by
  obtain
      ⟨pointwiseSubsequence, _pointwiseSubsequenceMono,
        pointwiseTendsto⟩ :=
    (tendstoInMeasure_of_tendsto_Lp
      receipt.state_tendsto).exists_seq_tendsto_ae
  have approximantBounds :
      ∀ index : ℕ,
        ∀ᵐ time ∂(commonTimeMeasure requestedTime),
          ‖puncturedCanonicalCriticalSpaceTimePath
              lineage ν θ θLtOne criticalMargin
              requestedTime requestedTimePos
              (receipt.subsequence
                (pointwiseSubsequence index)) time‖ ^ 2 ≤
            criticalCoefficientEnstrophyCeiling ν θ := by
    intro index
    simpa only [puncturedCanonicalCriticalSpaceTimePath] using
      generatedCriticalSpaceTimePath_norm_sq_ae_le_ceiling
        θLtOne requestedTimePos
        (puncturedCanonicalCriticalScalePath
          lineage ν θ criticalMargin
          (receipt.subsequence
            (pointwiseSubsequence index)))
  have allApproximantBounds :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        ∀ index : ℕ,
          ‖puncturedCanonicalCriticalSpaceTimePath
              lineage ν θ θLtOne criticalMargin
              requestedTime requestedTimePos
              (receipt.subsequence
                (pointwiseSubsequence index)) time‖ ^ 2 ≤
            criticalCoefficientEnstrophyCeiling ν θ :=
    eventually_countable_forall.2 approximantBounds
  filter_upwards
      [pointwiseTendsto, allApproximantBounds] with
      time timeTendsto timeBounds
  apply le_of_tendsto (timeTendsto.norm.pow 2)
  exact Filter.Eventually.of_forall timeBounds

/--
The same source-generated pointwise subsequence transports the exact
Euclidean coefficient ceiling to the whole-state limit.  Each approximant
already satisfies this physical mass bound, and coordinate-slice
continuity preserves it without the earlier fixed factor `3`.
-/
theorem
    CriticalSerrinWeakLimitReceipt.stateLimit_wholeVorticityEuclideanMass_ae_le_ceiling
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}
    (receipt :
      CriticalSerrinWeakLimitReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      wholeVorticityEuclideanMass
          (receipt.stateLimit time) ≤
        criticalCoefficientEnstrophyCeiling ν θ := by
  obtain
      ⟨pointwiseSubsequence, _pointwiseSubsequenceMono,
        pointwiseTendsto⟩ :=
    (tendstoInMeasure_of_tendsto_Lp
      receipt.state_tendsto).exists_seq_tendsto_ae
  have approximantBounds :
      ∀ index : ℕ,
        ∀ᵐ time ∂(commonTimeMeasure requestedTime),
          wholeVorticityEuclideanMass
              (puncturedCanonicalCriticalSpaceTimePath
                lineage ν θ θLtOne criticalMargin
                requestedTime requestedTimePos
                (receipt.subsequence
                  (pointwiseSubsequence index)) time) ≤
            criticalCoefficientEnstrophyCeiling ν θ := by
    intro index
    simpa only [puncturedCanonicalCriticalSpaceTimePath] using
      generatedCriticalSpaceTimePath_euclideanMass_ae_le_ceiling
        θLtOne requestedTimePos
        (puncturedCanonicalCriticalScalePath
          lineage ν θ criticalMargin
          (receipt.subsequence
            (pointwiseSubsequence index)))
  have allApproximantBounds :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        ∀ index : ℕ,
          wholeVorticityEuclideanMass
              (puncturedCanonicalCriticalSpaceTimePath
                lineage ν θ θLtOne criticalMargin
                requestedTime requestedTimePos
                (receipt.subsequence
                  (pointwiseSubsequence index)) time) ≤
            criticalCoefficientEnstrophyCeiling ν θ :=
    eventually_countable_forall.2 approximantBounds
  filter_upwards
      [pointwiseTendsto, allApproximantBounds] with
      time timeTendsto timeBounds
  apply le_of_tendsto
    (tendsto_wholeVorticityEuclideanMass timeTendsto)
  exact Filter.Eventually.of_forall timeBounds

/--
The actual limit has cutoff-free Euclidean coefficient mass bounded almost
everywhere by the generated ceiling.  The only loss is the fixed
three-coordinate comparison between row sup norm and Euclidean amplitude.
-/
theorem
    CriticalSerrinWeakLimitReceipt.wholeVorticityEuclideanMass_ae_le_generated
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}
    (receipt :
      CriticalSerrinWeakLimitReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      wholeVorticityEuclideanMass
          (receipt.stateLimit time) ≤
        3 * criticalCoefficientEnstrophyCeiling ν θ := by
  filter_upwards
      [CriticalSerrinWeakLimitReceipt.stateLimit_norm_sq_ae_le_generated
        receipt] with
      time timeNormSqLe
  exact
    (wholeVorticityEuclideanMass_le_three_mul_norm_sq
      (receipt.stateLimit time)).trans
        (mul_le_mul_of_nonneg_left timeNormSqLe (by norm_num))

end

end ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPointwiseMassLimit
end NavierStokes
end SaturationMonoid
