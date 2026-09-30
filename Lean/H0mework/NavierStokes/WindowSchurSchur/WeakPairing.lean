import H0mework.NavierStokes.WindowHistoryAnnihilation.Rows
import H0mework.NavierStokes.WindowSchurSchur.Action

set_option autoImplicit false
open scoped BigOperators Topology ComplexConjugate
namespace SaturationMonoid.NavierStokes.NativeWindowHistorySchurWeakPairing
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWholeResolvent NativePhysicalPairing
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativePhysicalFourier
open NativeWindowHistoryOseen (H)
open NativeWindowHistoryMeanAction (creation)
open NativeWindowHistoryMeanBlocks (annihilation)
open NativeWindowHistoryCreationGeometry (square gradientSquare transport advection)
open NativeWindowHistoryCreationCovariance (centered trace)
open NativeWindowHistoryAnnihilationRows (input)
open NativeWindowStressOseenTest (evaluate)
open NativeWindowAugmentedGradient (derivative)
open NativeWindowStressHeatSource (physical)
open NativeWindowFiniteGramFourier (fourierRead)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

theorem scalar_pairing (M : Finset IntegerWavevector) (closed : FiniteModeNegClosed M)
    (v : physicalSpace M) (i : Coordinate) (f : C(Torus,ℝ)) :
    inner ℝ (physical (evaluate M M i v)) (physical f)=
      ∑ k∈M,(conj (v.1 k i)*fourierRead k f).re := by
  rw [NativeWindowTraceTerminalCubic.real_pairing,← (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.inner_map_map,
    lp.inner_eq_tsum]
  have row (k : IntegerWavevector) :
      (UnitAddTorus.mFourierBasis (d := Coordinate)).repr (physical (evaluate M M i v)) k=
        if k∈M then v.1 k i else 0 := by
    rw [UnitAddTorus.mFourierBasis_repr,NativeWindowTraceTerminalSynthesis.evaluate_physical M M closed closed,
      NativeWindowStressHeatEnergy.field_fourier,NativeWindowStressHeatEnergy.finiteSequence_apply]
  simp only [row,UnitAddTorus.mFourierBasis_repr,NativeWindowTraceTerminalCubic.physical_fourier,RCLike.inner_apply]
  rw [tsum_eq_sum (s := M) (fun k absent => by simp only [if_neg absent,map_zero,mul_zero])]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro k included
  simp only [if_pos included,mul_comm]

theorem transport_pairing (M : Finset IntegerWavevector) (zero : 0∉M) (closed : FiniteModeNegClosed M)
    (nu : Viscosity) (u v w : physicalSpace M) :
    pairing M v (transport M zero closed nu u w)=
      ∑ i : Coordinate,inner ℝ (physical (evaluate M M i v)) (physical (advection M zero closed u w i)) := by
  rw [pairing_eq]
  simp only [scalar_pairing M closed]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k included
  rw [NativeWindowHistoryCreationGeometry.transport_row,if_pos included,
    complexCoordinateRealInner_transverseProjection k _ _ (fun h => zero (h ▸ included)) (physical_transverse v k included)]
  simp only [complexCoordinateRealInner,Complex.mul_re,Complex.conj_re,Complex.conj_im]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem square_integral (M : Finset IntegerWavevector) (closed : FiniteModeNegClosed M) (v : physicalSpace M) :
    (∫point : Torus,square M v point)=pairing M v v := by
  have paid (i : Coordinate) : Integrable (fun point : Torus => (evaluate M M i v point)^2) :=
    ((evaluate M M i v).continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have same : (∫point : Torus,square M v point)=∑ i : Coordinate,‖physical (evaluate M M i v)‖^2 := by
    simp only [NativeWindowTraceTerminalSynthesis.physical_square]
    rw [← integral_finsetSum Finset.univ (fun i _ => paid i)]
    apply integral_congr_ae
    filter_upwards with point
    simp only [square,ContinuousMap.sum_apply,ContinuousMap.mul_apply,pow_two]
  rw [same]
  simp only [NativeWindowTraceTerminalSynthesis.evaluate_physical M M closed closed,
    NativeWindowTraceHalfKernel.scalar_norm_square,NativeWindowHistoryCreationGeometry.pairing_mass]
  rw [Finset.sum_comm]

theorem gradient_integral (M : Finset IntegerWavevector) (zero : 0∉M) (closed : FiniteModeNegClosed M)
    (v : physicalSpace M) : (∫point : Torus,gradientSquare M zero closed v point)=curlPair M v.1 v.1 := by
  have paid (j : Coordinate) : Integrable (fun point : Torus => square M (derivative M zero closed j v) point) :=
    (square M (derivative M zero closed j v)).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change (∫point : Torus,∑ j : Coordinate,square M (derivative M zero closed j v) point)=_
  rw [integral_finsetSum Finset.univ (fun j _ => paid j)]
  simp only [square_integral M closed]
  exact NativeWindowHistoryCreationGeometry.derivative_mass M zero closed v

private theorem point_young (a : ℝ) (u v : Coordinate → ℝ) (d : Coordinate → Coordinate → ℝ) :
    2*a*(-∑ i : Coordinate,∑ j : Coordinate,u j*v i*d j i) ≤
      a^2*(∑ j : Coordinate,(u j)^2)*(∑ i : Coordinate,(v i)^2)+∑ j : Coordinate,∑ i : Coordinate,(d j i)^2 := by
  have paid:=Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun j _ =>
    Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun i _ =>
      show -2*a*(u j*v i*d j i) ≤ a^2*(u j)^2*(v i)^2+(d j i)^2 by nlinarith [sq_nonneg (a*u j*v i+d j i)]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul] at paid
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)] at paid
  nlinarith only [paid]

theorem transport_young (M : Finset IntegerWavevector) (zero : 0∉M) (closed : FiniteModeNegClosed M)
    (nu : Viscosity) (u v w : physicalSpace M) (a : ℝ) :
    2*a*pairing M v (transport M zero closed nu u w) ≤
      a^2*(∫point : Torus,square M u point*square M v point)+curlPair M w.1 w.1 := by
  have pairingRead : pairing M v (transport M zero closed nu u w)=
      ∫point : Torus,-∑ i : Coordinate,∑ j : Coordinate,
        evaluate M M j u point*evaluate M M i v point*evaluate M M i (derivative M zero closed j w) point := by
    rw [transport_pairing]
    simp only [NativeWindowStressHeatSource.physical_inner]
    have rowPaid (i : Coordinate) : Integrable (fun point : Torus => evaluate M M i v point*advection M zero closed u w i point) :=
      ((evaluate M M i v).continuous.mul (advection M zero closed u w i).continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [← integral_finsetSum Finset.univ (fun i _ => rowPaid i)]
    apply integral_congr_ae
    filter_upwards with point
    simp only [advection,ContinuousMap.neg_apply,ContinuousMap.sum_apply,ContinuousMap.mul_apply,
      mul_neg,Finset.sum_neg_distrib,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [pairingRead,← gradient_integral M zero closed,← integral_const_mul,← integral_const_mul,← integral_add]
  · have continuousLeft : Continuous (fun point : Torus => 2*a*(-∑ i : Coordinate,∑ j : Coordinate,
        evaluate M M j u point*evaluate M M i v point*evaluate M M i (derivative M zero closed j w) point)) := by fun_prop
    apply integral_mono
      (continuousLeft.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      ((continuous_const.mul ((square M u).continuous.mul (square M v).continuous)).add
        (gradientSquare M zero closed w).continuous |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    intro point
    have source:=point_young a (fun j => evaluate M M j u point)
      (fun i => evaluate M M i v point) (fun j i => evaluate M M i (derivative M zero closed j w) point)
    simp only [square,gradientSquare,ContinuousMap.sum_apply,ContinuousMap.mul_apply,Pi.add_apply,Pi.mul_apply]
    simpa only [pow_two,mul_assoc] using source
  · exact (continuous_const.mul ((square M u).continuous.mul (square M v).continuous)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact (gradientSquare M zero closed w).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def potential (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : physicalSpace (modes M)) : ℝ :=
  ∫point : Torus,trace seed M time point*square (modes M) v point

private def testing (f : C(Torus,ℝ)) : C(Torus,ℝ) →L[ℝ] ℝ := (innerSL ℝ (physical f)).comp physical

private theorem testing_apply (f w : C(Torus,ℝ)) : testing w f=∫point : Torus,f point*w point := by
  rw [testing,ContinuousLinearMap.comp_apply,innerSL_apply_apply,NativeWindowStressHeatSource.physical_inner]
  apply integral_congr_ae
  filter_upwards with point
  ring

theorem potential_integrable (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : physicalSpace (modes M)) :
    Integrable (fun lag => ∫point : Torus,square (modes M) (centered seed M time (time-lag)) point*square (modes M) v point) averageMeasure := by
  simpa only [testing_apply] using
    (testing (square (modes M) v)).integrable_comp (NativeWindowHistoryCreationCovariance.trace_integrable seed M time)

theorem potential_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : physicalSpace (modes M)) :
    (∫lag,(∫point : Torus,square (modes M) (centered seed M time (time-lag)) point*square (modes M) v point) ∂averageMeasure)=
      potential seed M time v := by
  simpa only [testing_apply,potential,trace] using
    (testing (square (modes M) v)).integral_comp_comm (NativeWindowHistoryCreationCovariance.trace_integrable seed M time)

private def finitePairing (M : ℕ) (v : physicalSpace (modes M)) : physicalSpace (modes M) →L[ℝ] ℝ :=
  (innerSL ℝ (coefficients (modes M) v)).comp (LinearMap.toContinuousLinearMap (coefficients (modes M)))

theorem annihilation_pairing (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (v : physicalSpace (modes M)) (r : H) :
    inner ℝ (includeCLM (modes M) (modes_closed M) v) (annihilation seed M time r)=
      ∫lag,pairing (modes M) v (transport (modes M) (modes_zero M) (modes_closed M) nu
        (centered seed M time (time-lag)) (input M r lag)) ∂averageMeasure := by
  rw [← NativeWindowHistoryAnnihilationRows.output_include seed M time r,
    include_inner (modes M) (modes_zero M),restrict_include]
  change finitePairing M v (NativeWindowHistoryAnnihilationRows.output seed M time r)=_
  rw [NativeWindowHistoryAnnihilationRows.output_integral]
  exact ((finitePairing M v).integral_comp_comm
    ((NativeWindowHistoryAnnihilationRows.transport_memLp seed M time r).integrable (by norm_num))).symm

theorem creation_young (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (v : physicalSpace (modes M)) (r : H) (a : ℝ) :
    2*a*inner ℝ (creation seed M time (includeCLM (modes M) (modes_closed M) v)) r ≤
      a^2*potential seed M time v+NativeWindowTraceWholeHistory.gradient M r := by
  let pair:=fun lag => pairing (modes M) v (transport (modes M) (modes_zero M) (modes_closed M) nu
    (centered seed M time (time-lag)) (input M r lag))
  have pairPaid : Integrable pair averageMeasure :=
    (finitePairing M v).integrable_comp ((NativeWindowHistoryAnnihilationRows.transport_memLp seed M time r).integrable (by norm_num))
  have gradientPaid : Integrable (fun lag => curlPair (modes M) (input M r lag).1 (input M r lag).1) averageMeasure :=
    NativeWindowTraceWholeHistory.gradient_integrable nu M r
  have bound:=integral_mono (pairPaid.const_mul (2*(-a)))
    (((potential_integrable seed M time v).const_mul ((-a)^2)).add gradientPaid)
    (fun lag => transport_young (modes M) (modes_zero M) (modes_closed M) nu _ v (input M r lag) (-a))
  simp only [Pi.add_apply] at bound
  rw [integral_add ((potential_integrable seed M time v).const_mul ((-a)^2)) gradientPaid,
    integral_const_mul,integral_const_mul,potential_original] at bound
  change 2*(-a)*(∫lag,pair lag ∂averageMeasure) ≤ (-a)^2*potential seed M time v+NativeWindowTraceWholeHistory.gradient M r at bound
  have pairingRead:=annihilation_pairing seed M time v r
  have green:=NativeWindowHistoryMeanBlocks.coupling_green seed M time (includeCLM (modes M) (modes_closed M) v) r
  change inner ℝ (includeCLM (modes M) (modes_closed M) v) (annihilation seed M time r)=∫lag,pair lag ∂averageMeasure at pairingRead
  have read:(∫lag,pair lag ∂averageMeasure)=-inner ℝ (creation seed M time (includeCLM (modes M) (modes_closed M) v)) r := by
    linarith only [pairingRead,green]
  rw [read] at bound
  simpa only [neg_sq,mul_neg,neg_mul,neg_neg] using bound

theorem potential_nonnegative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : physicalSpace (modes M)) :
    0 ≤ potential seed M time v := by
  apply integral_nonneg
  intro point
  apply mul_nonneg (NativeWindowHistoryCreationCovariance.trace_nonnegative seed M time point)
  simp only [square,ContinuousMap.sum_apply,ContinuousMap.mul_apply]
  exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _

theorem potential_stress_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (nonnegative : 0 ≤ time)
    (v : physicalSpace (modes M)) : potential seed M time v ≤
      ∫point : Torus,NativeWindowTraceGradient.traceStress seed time (integerWaveFrequencyCube M) point*square (modes M) v point := by
  apply integral_mono
    (((trace seed M time).continuous.mul (square (modes M) v).continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (((NativeWindowTraceGradient.traceStress seed time (integerWaveFrequencyCube M)).continuous.mul
      (square (modes M) v).continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  intro point
  apply mul_le_mul_of_nonneg_right (NativeWindowHistoryCreationCovariance.trace_le_stress seed M time nonnegative point)
  simp only [square,ContinuousMap.sum_apply,ContinuousMap.mul_apply]
  exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _

theorem source_potential_bound (seed : GeneratedWholeRestartCurrent nu) (horizon epsilon : ℝ) (positive : 0 < epsilon)
    (M : ℕ) (time : ℝ) (inside : time∈Icc 0 horizon) (v : physicalSpace (modes M)) :
    potential seed M time v ≤ epsilon*curlPair (modes M) v.1 v.1+
      NativeWindowHistoryCreationSource.budget seed horizon epsilon*pairing (modes M) v v := by
  have paid:=(potential_stress_bound seed M time inside.1 v).trans
    (NativeWindowHistoryCreationGeometry.square_absorption _ (modes M) (modes_zero M) (modes_closed M) v epsilon positive)
  have power:=pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    (mul_le_mul_of_nonneg_left (NativeWindowHistoryCreationSource.trace_bound seed M time horizon inside)
      (Real.sqrt_nonneg NativeWindowGreenTestForm.testKernel.cap)) 8
  have cap:NativeWindowHistoryCreationForm.budget
      ‖physical (NativeWindowTraceGradient.traceStress seed time (integerWaveFrequencyCube M))‖ (epsilon*(2*Real.pi)^2) ≤
        NativeWindowHistoryCreationSource.budget seed horizon epsilon :=
    add_le_add le_rfl (mul_le_mul_of_nonneg_right power (by positivity))
  have nonnegative:0 ≤ pairing (modes M) v v := real_inner_self_nonneg (x := coefficients (modes M) v)
  exact paid.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right cap nonnegative))

end
end SaturationMonoid.NavierStokes.NativeWindowHistorySchurWeakPairing
