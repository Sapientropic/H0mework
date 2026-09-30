import H0mework.Versions.X.NavierStokes.WindowEnergyJoint.HalfTest

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Pointwise ComplexConjugate
namespace SaturationMonoid.NavierStokes.NativeWindowJointLowPressure
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier NativeWindowStressHeatEnergy NativeEndpointVelocityCarrier
open NativeWindowPressureSectors (force)
open NativeWindowStressHeatSource (polynomial)
open NativeWindowHighPressurePhysical (realSynthesis)
open NativeWindowPressureStrainHistory (relative)
open NativeWindowJointHalfTest (test test_read)
open NativeWindowFiniteGramFourier (fourierRead)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

private theorem real_product (F : Finset IntegerWavevector) (closed : ∀ k,k∈F →waveNeg k∈F)
    (a b : IntegerWavevector → ℂ) (ar : ∀ k,a (waveNeg k)=conj (a k)) (br : ∀ k,b (waveNeg k)=conj (b k)) :
    NativeWindowStressHeatSource.physical (realSynthesis F a*realSynthesis F b)=
      (polynomial F a 0 0*polynomial F b 0 0).toLp 2 volume ℂ := by
  change ((Complex.ofRealCLM.compLeftContinuous ℝ Torus) (_*_)).toLp 2 volume ℂ=_
  congr 1
  ext point
  change ((realSynthesis F a point*realSynthesis F b point:ℝ):ℂ)=_
  rw [Complex.ofReal_mul]
  exact congrArg₂ HMul.hMul
    (congrArg (fun f : C(Torus,ℂ) => f point) (NativeWindowHighPressurePhysical.realSynthesis_complex F closed a ar))
    (congrArg (fun f : C(Torus,ℂ) => f point) (NativeWindowHighPressurePhysical.realSynthesis_complex F closed b br))

private theorem tensor_physical (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F →waveNeg k∈F) (radius : ℕ) (time : ℝ)
    (value : ComplexVorticityHilbertState) (reality : FiniteStateFourierReality value) :
    NativeWindowPressureLowInputs.tensorWork value value value F (test seed F radius time)=
      ∑ output : Coordinate,∑ input : Coordinate,inner ℂ (relative seed F radius time output input)
        (NativeWindowStressHeatSource.physical (NativeWindowHighPressurePhysical.pressurePair value F output input)) := by
  simp only [NativeWindowPressureLowInputs.tensorWork,NativeWindowHighPressurePhysical.pressurePair,map_add,inner_add_right]
  apply Finset.sum_congr rfl
  intro output _
  apply Finset.sum_congr rfl
  intro input _
  have velocity (k : IntegerWavevector) (i : Coordinate) : value (waveNeg k) i=conj (value k i) := congrFun (reality k) i
  rw [real_product F closed _ _ (fun k => NativeWindowHighPressurePhysical.force_reality value reality k output) (fun k => velocity k input),
    real_product F closed _ _ (fun k => NativeWindowHighPressurePhysical.force_reality value reality k input) (fun k => velocity k output)]
  rw [NativeWindowPressureSectors.trilinear_physical value value value F output input _ _ (test_read seed F closed radius time output input),
    NativeWindowPressureSectors.trilinear_physical value value value F input output _ _ (test_read seed F closed radius time output input)]

theorem remainder_physical (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F →waveNeg k∈F) (radius : ℕ) (time sample : ℝ) (nonnegative : 0 ≤ sample) :
    NativeWindowPressureLowInputs.remainder (NativeUnheatedSourceQuadraticApprox.physicalSource seed sample)
      (integerWaveFrequencyCube radius) F (test seed F radius time)=
        ∑ output : Coordinate,∑ input : Coordinate,inner ℂ (relative seed F radius time output input)
          (NativeWindowStressHeatSource.physical (NativeWindowRetainedPressure.sourceLow seed radius F sample output input)) := by
  have original : wholeVelocity (NativeUnheatedSourceQuadraticApprox.physicalSource seed sample).1=
      NativeWindowHighPressureCurrent.velocity seed sample := by
    rw [NativeUnheatedSourceQuadraticApprox.physicalSource,dif_pos nonnegative]
    rfl
  have reality : FiniteStateFourierReality (NativeWindowHighPressureCurrent.velocity seed sample) :=
    wholeVelocity_reality _ (NativeCompletePairedAction.source seed sample).reality
  have high : NativeWindowPressureLowInputs.high (NativeWindowHighPressureCurrent.velocity seed sample) (integerWaveFrequencyCube radius)=
      NativeWindowHighPressureCurrent.value seed radius sample := rfl
  simp only [NativeWindowPressureLowInputs.remainder,original,high]
  rw [tensor_physical seed F closed radius time _ reality,
    tensor_physical seed F closed radius time _ (NativeWindowHighPressurePhysical.source_reality seed radius sample)]
  simp only [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro output _
  apply Finset.sum_congr rfl
  intro input _
  have split := NativeWindowRetainedPressure.pressure_split (NativeWindowHighPressureCurrent.velocity seed sample)
    (complexSharpSupportProjection (integerWaveFrequencyCube radius) (NativeWindowHighPressureCurrent.velocity seed sample)) F output input
  change _=NativeWindowRetainedPressure.sourceLow seed radius F sample output input+
    NativeWindowHighPressurePhysical.pressurePair (NativeWindowHighPressureCurrent.value seed radius sample) F output input at split
  rw [split,map_add,inner_add_right,add_sub_cancel_right]

private theorem finite_pairing (G : Finset IntegerWavevector) (a : IntegerWavevector → ℂ) (value : ScalarField) :
    inner ℂ (field (finiteSequence G a)) value=
      ∑ k ∈ G,star (a k)*UnitAddTorus.mFourierCoeff value k := by
  have source := (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.inner_map_map (field (finiteSequence G a)) value
  rw [field,LinearIsometryEquiv.apply_symm_apply] at source
  change inner ℂ (finiteSequence G a) ((UnitAddTorus.mFourierBasis (d := Coordinate)).repr value)=
    inner ℂ (field (finiteSequence G a)) value at source
  rw [← source,lp.inner_eq_tsum]
  rw [tsum_eq_sum (s := G) (fun k outside => by simp [finiteSequence_apply,if_neg outside])]
  apply Finset.sum_congr rfl
  intro k member
  simp only [finiteSequence_apply,if_pos member,RCLike.inner_apply,starRingEnd_apply,UnitAddTorus.mFourierBasis_repr,mul_comm]

private theorem relative_pairing (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F →waveNeg k∈F) (radius : ℕ) (time : ℝ) (output input : Coordinate) (value : ScalarField) :
    inner ℂ (relative seed F radius time output input) value=
      ∑ k ∈ NativeWindowJointHeat.frequencies F,star (-NativeWindowJointHeat.coefficients seed F radius time k output input)*
        UnitAddTorus.mFourierCoeff value k := by
  rw [NativeWindowJointHeat.relative_original seed F radius time closed,inner_neg_left,finite_pairing]
  simp only [star_neg,neg_mul,Finset.sum_neg_distrib]

private theorem physical_fourier (f : C(Torus,ℝ)) (k : IntegerWavevector) :
    UnitAddTorus.mFourierCoeff (NativeWindowStressHeatSource.physical f) k=fourierRead k f := by
  change UnitAddTorus.mFourierCoeff (((Complex.ofRealCLM.compLeftContinuous ℝ Torus) f).toLp 2 volume ℂ) k=_
  rw [UnitAddTorus.mFourierCoeff_toLp,NativeWindowFiniteGramFourier.fourierRead_apply]
  rfl

theorem window_physical (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F →waveNeg k∈F) (radius : ℕ) (time : ℝ) (nonnegative : 0≤time) :
    NativeWindowPressureLowInputs.window seed time (integerWaveFrequencyCube radius) F (test seed F radius time)=
      ∑ output : Coordinate,∑ input : Coordinate,inner ℂ (relative seed F radius time output input)
        (NativeWindowJointEnergyGate.lowPressureField seed F radius time output input) := by
  have entry (output input : Coordinate) (k : IntegerWavevector) : Integrable (fun shift =>
      star (-NativeWindowJointHeat.coefficients seed F radius time k output input)*fourierRead k
        (NativeWindowRetainedPressure.sourceLow seed radius F (time-shift) output input)) averageMeasure :=
    ((integrable_withDensity_iff_integrable_smul NativeForwardWindowPairingReadout.density_measurable).mpr
      (NativeWindowJointEnergyGate.low_integrable seed F closed radius time output input k)).const_mul _
  rw [NativeWindowPressureLowInputs.window]
  have actual : (fun shift => NativeWindowPressureLowInputs.remainder (NativeUnheatedSourceQuadraticApprox.physicalSource seed (time-shift))
      (integerWaveFrequencyCube radius) F (test seed F radius time)) =ᵐ[averageMeasure]
        fun shift => ∑ output : Coordinate,∑ input : Coordinate,inner ℂ (relative seed F radius time output input)
          (NativeWindowStressHeatSource.physical (NativeWindowRetainedPressure.sourceLow seed radius F (time-shift) output input)) := by
    filter_upwards [NativeWindowHistoryGNS.average_support] with shift support
    exact remainder_physical seed F closed radius time (time-shift) (by linarith)
  rw [integral_congr_ae actual]
  simp only [relative_pairing seed F closed radius time,physical_fourier,
    NativeWindowJointEnergyGate.lowPressureField_fourier seed F closed radius]
  rw [integral_finsetSum Finset.univ (fun output _ => integrable_finsetSum Finset.univ
    (fun input _ => integrable_finsetSum _ (fun k _ => entry output input k)))]
  apply Finset.sum_congr rfl
  intro output _
  rw [integral_finsetSum Finset.univ (fun input _ => integrable_finsetSum _ (fun k _ => entry output input k))]
  apply Finset.sum_congr rfl
  intro input _
  rw [integral_finsetSum _ (fun k _ => entry output input k)]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_const_mul,NativeForwardWindowPairingReadout.density_integral]
  rfl

private theorem real_pairing (first last : ScalarField) : inner ℝ first last=(inner ℂ first last).re := by
  rw [L2.inner_def,L2.inner_def]
  change (∫ point : Torus,RCLike.re (inner ℂ (first point) (last point)))=
    RCLike.re (∫ point : Torus,inner ℂ (first point) (last point))
  exact integral_re (L2.integrable_inner first last)

theorem work_original (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F →waveNeg k∈F) (radius : ℕ) (time : ℝ) (nonnegative : 0≤time) :
    NativeWindowJointEnergyGate.lowPressureWork seed F radius time=
      -(NativeWindowPressureLowInputs.window seed time (integerWaveFrequencyCube radius) F (test seed F radius time)).re := by
  rw [window_physical seed F closed radius time nonnegative]
  simp only [NativeWindowJointEnergyGate.lowPressureWork,real_pairing,Complex.re_sum]

def coefficient (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (radius : ℕ) : ℝ :=
  NativeWindowPressureLowInputs.sectorBudget seed (integerWaveFrequencyCube radius)*
    (1+NativeWindowFiniteStressUniform.kernelBound 0*
      NativeUnheatedGlobalGradient.budget (NativeEventualTailControl.terminal seed) (horizon+2))

theorem coefficient_nonnegative (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) (radius : ℕ) :
    0≤coefficient seed horizon radius := by
  have G0 : 0≤NativeWindowFiniteStressUniform.kernelBound 0*
      NativeUnheatedGlobalGradient.budget (NativeEventualTailControl.terminal seed) (horizon+2) :=
    (integral_nonneg (fun shift => NativeUnheatedSourceGradient.mass_nonnegative seed (0-shift))).trans
      (NativeWindowStressOseenDiffusion.weighted_mass_horizon seed 0 horizon ⟨le_rfl,nonnegative⟩)
  exact mul_nonneg (NativeWindowPressureLowInputs.sectorBudget_nonnegative seed _) (by positivity)

theorem work_bound (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F →waveNeg k∈F) (radius : ℕ) (time horizon : ℝ) (inside : time∈Icc 0 horizon) :
    |NativeWindowJointEnergyGate.lowPressureWork seed F radius time|≤coefficient seed horizon radius*‖test seed F radius time‖ := by
  rw [work_original seed F closed radius time inside.1,abs_neg]
  apply (Complex.abs_re_le_norm _).trans
  exact (NativeWindowPressureLowInputs.window_bound seed time horizon inside (integerWaveFrequencyCube radius) F
    (test seed F radius time)).trans_eq (by unfold coefficient; ring)

def energyCoefficient (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (radius : ℕ) : ℝ :=
  nu.coeff/2+(coefficient seed horizon radius)^2/nu.coeff

theorem source_absorption (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ)
    (radius : ℕ) (F : Finset IntegerWavevector) (closed : ∀ k,k∈F →waveNeg k∈F) (time : ℝ) (inside : time∈Icc 0 horizon) :
    |NativeWindowJointEnergyGate.lowPressureWork seed F radius time|≤
      (nu.coeff/4)*NativeWindowJointHeat.dirichlet seed F radius time+
        energyCoefficient seed horizon radius*(1+NativeWindowJointNormalForm.energy seed F radius time) := by
  have normed := NativeWindowJointHalfTest.test_norm_square seed F closed radius time
  have source := work_bound seed F closed radius time horizon inside
  have young := sq_nonneg (nu.coeff*‖test seed F radius time‖-2*coefficient seed horizon radius)
  have variance : 0≤(coefficient seed horizon radius)^2/nu.coeff := div_nonneg (sq_nonneg _) nu.coeff_pos.le
  have same : ((coefficient seed horizon radius)^2/nu.coeff)*nu.coeff=(coefficient seed horizon radius)^2 :=
    div_mul_cancel₀ _ nu.coeff_pos.ne'
  have energy0 : 0≤NativeWindowJointNormalForm.energy seed F radius time := by
    unfold NativeWindowJointNormalForm.energy
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have square : (nu.coeff/4)*‖test seed F radius time‖^2≤
      (nu.coeff/4)*(2*NativeWindowJointNormalForm.energy seed F radius time+NativeWindowJointHeat.dirichlet seed F radius time) :=
    mul_le_mul_of_nonneg_left normed (by positivity [nu.coeff_pos])
  have first : coefficient seed horizon radius*‖test seed F radius time‖≤
      (nu.coeff/4)*‖test seed F radius time‖^2+(coefficient seed horizon radius)^2/nu.coeff := by
    nlinarith only [young,same,nu.coeff_pos]
  unfold energyCoefficient
  nlinarith only [source,first,square,mul_nonneg variance energy0,nu.coeff_pos]

theorem uniform_absorption (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (radius : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ F : Finset IntegerWavevector,(∀ k,k∈F →waveNeg k∈F) →∀ time∈Icc 0 horizon,
      |NativeWindowJointEnergyGate.lowPressureWork seed F radius time|≤
        (nu.coeff/4)*NativeWindowJointHeat.dirichlet seed F radius time+
          C*(1+NativeWindowJointNormalForm.energy seed F radius time) := by
  refine ⟨energyCoefficient seed horizon radius,?_,fun F closed time inside => source_absorption seed horizon radius F closed time inside⟩
  unfold energyCoefficient
  positivity [nu.coeff_pos]

end
end SaturationMonoid.NavierStokes.NativeWindowJointLowPressure
