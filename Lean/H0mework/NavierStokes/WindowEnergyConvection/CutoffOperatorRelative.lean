import H0mework.NavierStokes.WindowEnergyConvection.CutoffOperatorKernel

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowTraceCutRelative
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativePhysicalFourier NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWindowStressOseenTest
open NativeUnheatedStressProduct NativeWindowAugmentedTestProduct
open NativeWindowAugmentedCoercivity (productCap)
open NativeWindowTraceCutOperator
open NativeWindowConvectionCutoffAction (primitiveField primitiveField_norm)
open NativeWindowStressHeatSource (physical)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

private theorem difference_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (M F : Finset IntegerWavevector)
    (v : physicalSpace M) (zero : 0∉M) (closedM : FiniteModeNegClosed M) (closedF : FiniteModeNegClosed F)
    (delta : ℝ) (nonnegative : 0≤delta) (small : ∀ i,‖primitiveField seed F 0 time i i‖≤delta) :
    |differenceForm seed time M F v v|≤9*delta*productCap*gradientMass (complexSharpSupportProjection M v.1) := by
  have fieldBound : ‖differenceField seed time F‖≤3*delta :=
    (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => small i).trans_eq (by simp))
  have row (i : Coordinate) : |inner ℝ (differenceField seed time F) (physical (evaluate M F i v*evaluate M F i v))|≤
      3*delta*productCap*gradientMass (complexSharpSupportProjection M v.1) := by
    apply (abs_real_inner_le_norm _ _).trans
    have tested := (product_bound M F v zero closedM closedF i i).trans
      (mul_le_mul_of_nonneg_left (projected_gradient_le M F v) (by positivity))
    exact (mul_le_mul fieldBound tested (norm_nonneg _) (by positivity)).trans_eq (by unfold productCap; ring)
  change |∑ i : Coordinate,inner ℝ (differenceField seed time F) (physical (evaluate M F i v*evaluate M F i v))| ≤ _
  exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun i _ => row i).trans_eq (by simp; ring))

theorem source_relative_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) : ∃ low : ℕ,∀ radius≥low,∀ cutoff≥low,
      ∀ M : Finset IntegerWavevector,0∉M →FiniteModeNegClosed M →∀ time∈Icc 0 horizon,∀ v : physicalSpace M,
        |pairing M v (test seed time M M (integerWaveFrequencyCube cutoff) radius v)-
          pairing M v (NativeWindowTraceOperator.test seed time M M (integerWaveFrequencyCube cutoff) radius v)|≤
            epsilon*pairing M v (NativeWindowTraceOperator.test seed time M M (integerWaveFrequencyCube cutoff) radius v) := by
  let delta:=epsilon*nu.coeff*(2*Real.pi)^2/(18*(productCap+1))
  have deltaPos : 0<delta := by dsimp only [delta,productCap]; positivity [nu.coeff_pos]
  obtain ⟨space,small⟩ := NativeWindowConvectionCutoffWindow.primitive_small seed 0 horizon nonnegative delta deltaPos
  obtain ⟨core,coercive⟩ := NativeWindowTraceOperator.source_coercivity seed horizon nonnegative
  refine ⟨max space core,fun radius above cutoff covered M zero closed time inside v => ?_⟩
  let F:=integerWaveFrequencyCube cutoff
  have source (i : Coordinate) : ‖primitiveField seed F 0 time i i‖≤delta := by
    rw [primitiveField_norm]
    exact (small cutoff ((le_max_left _ _).trans covered) time inside i i).le
  have paid := difference_bound seed time M F v zero closed (NativeWindowFiniteGramFourier.cube_closed cutoff) delta deltaPos.le source
  have G0 : 0≤gradientMass (complexSharpSupportProjection M v.1) := tsum_nonneg (density_nonnegative _)
  have fraction : 9*delta*productCap≤epsilon*(nu.coeff/2)*(2*Real.pi)^2 := by
    have denominator : 0<18*(productCap+1) := by unfold productCap; positivity
    have same : delta*(18*(productCap+1))=epsilon*nu.coeff*(2*Real.pi)^2 := div_mul_cancel₀ _ denominator.ne'
    nlinarith only [same,deltaPos]
  have cost := mul_le_mul_of_nonneg_right fraction G0
  rw [mul_assoc (epsilon*(nu.coeff/2)),← curl_original M v zero] at cost
  have mass : 0≤pairing M v v := by
    change (0 : ℝ) ≤ inner ℝ (coefficients M v) (coefficients M v)
    exact real_inner_self_nonneg
  have complete := coercive radius ((le_max_right _ _).trans above) M F zero closed
    (NativeWindowFiniteGramFourier.cube_closed cutoff) time inside v
  have relative : epsilon*((nu.coeff/2)*curlPair M v.1 v.1)≤
      epsilon*pairing M v (NativeWindowTraceOperator.test seed time M M F radius v) :=
    mul_le_mul_of_nonneg_left (by linarith only [complete,mass]) positive.le
  have same : pairing M v (test seed time M M F radius v)-pairing M v (NativeWindowTraceOperator.test seed time M M F radius v)=
      -differenceForm seed time M F v v := by
    rw [test,LinearMap.sub_apply,map_sub,difference_pairing]
    ring
  rw [same,abs_neg]
  exact paid.trans (cost.trans (by simpa only [mul_assoc] using relative))

theorem source_equivalent (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∀ radius≥low,∀ cutoff≥low,∀ M : Finset IntegerWavevector,0∉M →FiniteModeNegClosed M →
      ∀ time∈Icc 0 horizon,∀ v : physicalSpace M,
        (1/2 : ℝ)*pairing M v (NativeWindowTraceOperator.test seed time M M (integerWaveFrequencyCube cutoff) radius v)≤
          pairing M v (test seed time M M (integerWaveFrequencyCube cutoff) radius v) ∧
        pairing M v (test seed time M M (integerWaveFrequencyCube cutoff) radius v)≤
          (3/2 : ℝ)*pairing M v (NativeWindowTraceOperator.test seed time M M (integerWaveFrequencyCube cutoff) radius v) := by
  obtain ⟨low,paid⟩ := source_relative_bound seed horizon nonnegative (1/2) (by norm_num)
  refine ⟨low,fun radius above cutoff covered M zero closed time inside v => ?_⟩
  have bound := paid radius above cutoff covered M zero closed time inside v
  exact ⟨by linarith only [(abs_le.mp bound).1],by linarith only [(abs_le.mp bound).2]⟩

end
end SaturationMonoid.NavierStokes.NativeWindowTraceCutRelative
