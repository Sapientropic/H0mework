import H0mework.Versions.X.NavierStokes.WindowEnergyAugmented.PreparationPrimitive
import H0mework.Versions.X.NavierStokes.WindowEnergyAugmented.TimeForm

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowPreparedAugmentedControl
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativePhysicalFourier NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWindowStressOseenTest
open NativeUnheatedStressProduct NativeWindowAugmentedTestProduct NativeWindowAugmentedFixedOperator
open NativeWindowAugmentedCoercivity (productCap)
open NativeWindowAugmentedTimeForm (matrixJet quadraticJet actual_hasDerivAt)
open NativeWindowSobolevStress (quarter quarter_positive)
open NativeWindowFiniteStressUniform (window)
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open RationalVorticityEvaluator (butterflyGainViscosity)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local notation "ν₀" => butterflyGainViscosity.coeff

theorem window_zero_row (radius : ℕ) (time : ℝ) (valid : -2≤time)
    (wave : IntegerWavevector) (output input : Coordinate) :
    window stackedShortCurrent radius 0 time wave (output,input)=-(quarter wave : ℂ)*UnitAddTorus.mFourierCoeff
      (fun point => (NativeWindowFiniteGramFourier.stress stackedShortCurrent time (integerWaveFrequencyCube radius) output input point : ℂ)) wave := by
  let F := integerWaveFrequencyCube radius
  let observed := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Coordinate×Coordinate => ℂ) (output,input)
  have original (shift : ℝ) : quarter wave • NativeCompleteStressCarrier.tensor
      (NativeCompleteStressCarrier.read (NativeUnheatedWindowStress.finiteStress stackedShortCurrent F (time-shift)) wave)=
        NativeWindowFiniteStressConvergence.weightedRead wave (NativeUnheatedWindowStress.finiteStress stackedShortCurrent F (time-shift)) := by
    ext entry
    change quarter wave • ((NativeCompleteStressCarrier.weight wave)⁻¹ •
      NativeUnheatedWindowStress.finiteStress stackedShortCurrent F (time-shift) wave entry)=_
    exact (mul_smul _ _ _).symm
  have paid : Integrable (fun shift => quarter wave • NativeCompleteStressCarrier.tensor
      (NativeCompleteStressCarrier.read (NativeUnheatedWindowStress.finiteStress stackedShortCurrent F (time-shift)) wave))
        NativeForwardWindowPairingReadout.averageMeasure := by
    simpa only [original] using (NativeWindowFiniteStressConvergence.weightedRead wave).integrable_comp
      (NativeWindowFiniteDensityCoefficient.finite_integrable stackedShortCurrent F time)
  change observed (window stackedShortCurrent radius 0 time wave)=_
  rw [NativeWindowPreparedSobolevWindow.window_row radius 0 time valid wave]
  simp only [NativeForwardWindowJets.kernelJet,iteratedDeriv_zero]
  rw [← NativeForwardWindowPairingReadout.density_integral,← observed.integral_comp_comm paid]
  change (∫ shift,quarter wave • NativeCompleteStressCarrier.read
    (NativeUnheatedWindowStress.finiteStress stackedShortCurrent F (time-shift)) wave output input
      ∂NativeForwardWindowPairingReadout.averageMeasure)=_
  rw [integral_smul,NativeWindowFiniteGramFourier.stress_fourier stackedShortCurrent time F
    (NativeWindowFiniteGramFourier.cube_closed radius) output input wave]
  simp only [Complex.real_smul,neg_mul_neg]

theorem stressJet_zero (radius : ℕ) (time : ℝ) (valid : -2≤time) (output input : Coordinate) :
    NativeWindowAugmentedPayment.stressJet stackedShortCurrent radius 0 time output input=
      NativeWindowStressHeatSource.physical (NativeWindowFiniteGramFourier.stress stackedShortCurrent time
        (integerWaveFrequencyCube radius) output input) := by
  apply (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.injective
  apply lp.ext
  funext wave
  change (UnitAddTorus.mFourierBasis (d := Coordinate)).repr
    ((UnitAddTorus.mFourierBasis (d := Coordinate)).repr.symm
      (NativeWindowAugmentedPayment.restore output input (window stackedShortCurrent radius 0 time))) wave=_
  rw [LinearIsometryEquiv.apply_symm_apply]
  change -(quarter wave)⁻¹ • window stackedShortCurrent radius 0 time wave (output,input)=_
  rw [window_zero_row radius time valid wave output input,UnitAddTorus.mFourierBasis_repr]
  change _=UnitAddTorus.mFourierCoeff (((Complex.ofRealCLM.compLeftContinuous ℝ Torus)
    (NativeWindowFiniteGramFourier.stress stackedShortCurrent time (integerWaveFrequencyCube radius) output input)).toLp 2 volume ℂ) wave
  rw [UnitAddTorus.mFourierCoeff_toLp]
  simp only [Complex.real_smul,Complex.ofReal_neg]
  rw [← mul_assoc,neg_mul_neg,← Complex.ofReal_mul,inv_mul_cancel₀ (quarter_positive wave).ne',Complex.ofReal_one,one_mul]
  rfl

theorem stressJet_original (radius order : ℕ) (time : ℝ) (valid : -2≤time) (output input : Coordinate) :
    NativeWindowAugmentedPayment.stressJet stackedShortCurrent radius order time output input=
      NativeWindowStressHeatSource.physical (NativeWindowStressHeatTime.jet stackedShortCurrent
        (integerWaveFrequencyCube radius) output input order time) := by
  induction order generalizing time with
  | zero => simpa only [NativeWindowStressHeatTime.jet_zero] using stressJet_zero radius time valid output input
  | succ order ih =>
    have first := (NativeWindowAugmentedPayment.stressJet_hasDerivAt stackedShortCurrent radius order time output input).hasDerivWithinAt (s := Ici (-2 : ℝ))
    have last := (NativeWindowStressHeatSource.physical.hasFDerivAt.comp_hasDerivAt time
      (NativeWindowStressHeatTime.jet_hasDerivAt stackedShortCurrent (integerWaveFrequencyCube radius) output input order time)).hasDerivWithinAt (s := Ici (-2 : ℝ))
    have same := last.congr_of_mem (fun sample inside => ih sample inside) valid
    have equal := congrArg (fun f : ℝ→L[ℝ] ScalarField => f 1) ((uniqueDiffOn_Ici (-2 : ℝ)).eq valid first same)
    simpa only [ContinuousLinearMap.toSpanSingleton_apply,one_smul] using equal

theorem stressJet_bound (radius order : ℕ) (time horizon : ℝ) (nonnegative : 0≤horizon)
    (inside : time∈Icc (-2 : ℝ) horizon) (output input : Coordinate) :
    ‖NativeWindowAugmentedPayment.stressJet stackedShortCurrent radius order time output input‖≤
      NativeWindowPreparedSobolevWindow.budget order horizon := by
  change ‖(UnitAddTorus.mFourierBasis (d := Coordinate)).repr.symm _‖≤_
  rw [LinearIsometryEquiv.norm_map]
  exact (NativeWindowAugmentedPayment.restore_bound output input _).trans
    (NativeWindowPreparedSobolevWindow.window_bound radius order time horizon nonnegative inside)

theorem source_coercivity (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∀ radius≥low,∀ M F : Finset IntegerWavevector,0∉M →FiniteModeNegClosed M →FiniteModeNegClosed F →
      ∀ time∈Icc (-2 : ℝ) horizon,∀ value : physicalSpace M,
        pairing M value value+(ν₀/2)*curlPair M value.1 value.1≤
          pairing M value (test stackedShortCurrent time M M F radius value) := by
  let delta := ν₀*(2*Real.pi)^2/(18*(productCap+1))
  have deltaPos : 0<delta := by dsimp only [delta,productCap]; positivity [butterflyGainViscosity.coeff_pos]
  obtain ⟨low,paid⟩ := NativeWindowPreparedPrimitiveControl.correctionJet_small 0 horizon nonnegative delta deltaPos
  refine ⟨low,fun radius above M F zero closedM closedF time inside value => ?_⟩
  have small (output input : Coordinate) : ‖NativeWindowPressureStrainHistory.correction stackedShortCurrent F radius time output input‖≤delta := by
    simpa only [NativeWindowJointNormalForm.correctionJet_zero] using (paid radius above F time inside output input).le
  have negative := neg_abs_le (NativeWindowAugmentedCoercivity.correctionForm stackedShortCurrent time M F radius value)
  have bound := NativeWindowAugmentedCoercivity.correction_bound stackedShortCurrent time M F radius value zero closedM closedF delta deltaPos.le small
  have gram := form_positive stackedShortCurrent time M F value
  have G0 : 0≤gradientMass (complexSharpSupportProjection M value.1) := tsum_nonneg (density_nonnegative _)
  have fraction : 9*delta*productCap≤(ν₀/2)*(2*Real.pi)^2 := by
    have denominator : 18*(productCap+1)>0 := by unfold productCap; positivity
    have same : delta*(18*(productCap+1))=ν₀*(2*Real.pi)^2 := div_mul_cancel₀ _ denominator.ne'
    nlinarith only [same,deltaPos]
  have cost := mul_le_mul_of_nonneg_right fraction G0
  rw [mul_assoc (ν₀/2),← curl_original M value zero] at cost
  rw [NativeWindowAugmentedCoercivity.actual_diagonal stackedShortCurrent time M F radius value zero]
  linarith only [negative,bound,gram,cost]

theorem source_time_bound (horizon : ℝ) (nonnegative : 0≤horizon) (order : ℕ) :
    ∃ low : ℕ,∃ C : ℝ,0≤C ∧ ∀ radius≥low,∀ outerRadius,∀ M : Finset IntegerWavevector,
      0∉M →FiniteModeNegClosed M →∀ time∈Icc (-2 : ℝ) horizon,∀ value : physicalSpace M,
        |quadraticJet stackedShortCurrent M (integerWaveFrequencyCube outerRadius) radius order time value|≤
          C*pairing M value (test stackedShortCurrent time M M (integerWaveFrequencyCube outerRadius) radius value) := by
  let B := NativeWindowPreparedSobolevWindow.budget order horizon+1
  have B0 : 0≤B := by
    have paid := (norm_nonneg _).trans (stressJet_bound 0 order 0 horizon nonnegative ⟨by norm_num,nonnegative⟩ 0 0)
    dsimp only [B]
    linarith
  let C := 18*B*productCap/(ν₀*(2*Real.pi)^2)
  have C0 : 0≤C := by dsimp only [C,productCap]; positivity [butterflyGainViscosity.coeff_pos]
  obtain ⟨first,coercive⟩ := source_coercivity horizon nonnegative
  obtain ⟨last,small⟩ := NativeWindowPreparedPrimitiveControl.correctionJet_small order horizon nonnegative 1 (by norm_num)
  refine ⟨max first last,C,C0,fun radius above outerRadius M zero closed time inside value => ?_⟩
  let F := integerWaveFrequencyCube outerRadius
  have fieldBound (output input : Coordinate) : ‖matrixJet stackedShortCurrent F radius order time output input‖≤B := by
    rw [NativeWindowAugmentedTimeForm.matrixJet,← stressJet_original outerRadius order time inside.1]
    exact (norm_add_le _ _).trans (add_le_add (stressJet_bound outerRadius order time horizon nonnegative inside output input)
      (small radius ((le_max_right first last).trans above) F time inside output input).le)
  have row (output input : Coordinate) : |inner ℝ (matrixJet stackedShortCurrent F radius order time output input)
      (NativeWindowStressHeatSource.physical (evaluate M F output value*evaluate M F input value))|≤
        B*productCap*gradientMass (complexSharpSupportProjection M value.1) := by
    apply (abs_real_inner_le_norm _ _).trans
    have tested := (product_bound M F value zero closed (NativeWindowFiniteGramFourier.cube_closed outerRadius) output input).trans
      (mul_le_mul_of_nonneg_left (projected_gradient_le M F value) (by positivity))
    exact (mul_le_mul (fieldBound output input) tested (norm_nonneg _) B0).trans_eq (by unfold productCap; ring)
  have budget : |quadraticJet stackedShortCurrent M F radius order time value|≤9*B*productCap*gradientMass (complexSharpSupportProjection M value.1) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    have summed := Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun output _ =>
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun input _ => row output input)
    exact summed.trans_eq (by simp; ring)
  have mass0 : 0≤pairing M value value := by
    change (0 : ℝ) ≤ inner ℝ (coefficients M value) (coefficients M value)
    rw [real_inner_self_eq_norm_sq]
    positivity
  have control := coercive radius ((le_max_left first last).trans above) M F zero closed
    (NativeWindowFiniteGramFourier.cube_closed outerRadius) time inside value
  have relative := mul_le_mul_of_nonneg_left control C0
  have cancel : C*((ν₀/2)*curlPair M value.1 value.1)=9*B*productCap*gradientMass (complexSharpSupportProjection M value.1) := by
    rw [curl_original M value zero]
    dsimp only [C]
    field_simp [butterflyGainViscosity.coeff_pos.ne',Real.pi_ne_zero]
    ring
  rw [mul_add,cancel] at relative
  exact budget.trans (by linarith only [relative,mul_nonneg C0 mass0])

theorem source_energy_time_control (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∃ C : ℝ,0≤C ∧ ∀ radius≥low,∀ outerRadius,∀ M : Finset IntegerWavevector,
      0∉M →FiniteModeNegClosed M →∀ time∈Icc (-2 : ℝ) horizon,∀ value : physicalSpace M,
        |deriv (fun t => pairing M value (test stackedShortCurrent t M M (integerWaveFrequencyCube outerRadius) radius value)) time|≤
          C*pairing M value (test stackedShortCurrent time M M (integerWaveFrequencyCube outerRadius) radius value) := by
  obtain ⟨low,C,C0,paid⟩ := source_time_bound horizon nonnegative 1
  refine ⟨low,C,C0,fun radius above outerRadius M zero closed time inside value => ?_⟩
  rw [(actual_hasDerivAt stackedShortCurrent M (integerWaveFrequencyCube outerRadius) radius time value).deriv]
  exact paid radius above outerRadius M zero closed time inside value

end
end SaturationMonoid.NavierStokes.NativeWindowPreparedAugmentedControl
