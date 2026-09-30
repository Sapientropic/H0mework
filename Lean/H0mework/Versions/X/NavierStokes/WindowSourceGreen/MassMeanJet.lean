import H0mework.Versions.X.NavierStokes.WindowSourceGreen.MassField

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowMeanSpatialJet
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open NativePhysicalFourier (Torus ScalarField realValue realField)
open NativeWindowGreenSourceForm (velocity gradientValue)
open NativeWindowHistoryFirstJet (physicalJet)
open NativeWindowMassField (State)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance physicalHaar : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs AddCircle.haarAddCircle.IsAddHaarMeasure
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
variable {nu : Viscosity}

def axis (i : Coordinate) : ℂ →L[ℝ] PhysicalSpace :=
  (ContinuousLinearMap.toSpanSingleton ℝ (PiLp.single 2 i (1:ℝ) : PhysicalSpace)).comp Complex.reCLM

def lift (i : Coordinate) : ScalarField →L[ℝ] State := (axis i).compLpL 2 volume

def assemble (f : Coordinate → ScalarField) : State := lift 0 (f 0)+lift 1 (f 1)+lift 2 (f 2)

theorem assemble_ae (f : Coordinate → ScalarField) : assemble f=ᵐ[volume]
    fun x => WithLp.toLp 2 (fun i => (f i x).re) := by
  have each (i : Coordinate) : lift i (f i)=ᵐ[volume] fun x => axis i (f i x) := (axis i).coeFn_compLpL (f i)
  filter_upwards [Lp.coeFn_add (lift 0 (f 0)+lift 1 (f 1)) (lift 2 (f 2)),
    Lp.coeFn_add (lift 0 (f 0)) (lift 1 (f 1)),each 0,each 1,each 2] with x first second a b c
  change assemble f x=_ at first
  rw [first,Pi.add_apply,second,Pi.add_apply,a,b,c]
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [axis,PiLp.add_apply,PiLp.smul_apply]

def gradient (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1<time) (j : Coordinate) : State :=
  assemble (physicalJet seed time valid.le j)

theorem gradient_ae (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1<time) (j : Coordinate) :
    gradient seed time valid j=ᵐ[volume] gradientValue seed time valid j := assemble_ae _

def shifted (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (j : Coordinate) (z : ℝ) : State :=
  assemble (fun i => NativePhysicalTranslation.translate (NativePhysicalTranslation.displacement j z)
    (NativePhysicalFourier.scalarField (velocity seed time) i))

theorem shifted_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1<time) (j : Coordinate) :
    HasDerivAt (shifted seed time j) (gradient seed time valid j) 0 := by
  have each (i : Coordinate) : HasDerivAt (fun z => lift i
      (NativePhysicalTranslation.translate (NativePhysicalTranslation.displacement j z)
        (NativePhysicalFourier.scalarField (velocity seed time) i))) (lift i (physicalJet seed time valid.le j i)) 0 := by
    apply (lift i).hasFDerivAt.comp_hasDerivAt
    simpa only [velocity,NativeForwardWindowEvolution.velocityJet,NativeForwardWindowJets.jet_zero] using
      NativeWindowHistoryFirstJet.physical_translation_hasDerivAt seed time valid.le j i
  exact ((each 0).add (each 1)).add (each 2)

theorem shifted_ae (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (j : Coordinate) (z : ℝ) :
    shifted seed time j z=ᵐ[volume]
      fun x => realValue (velocity seed time) (x+NativePhysicalTranslation.displacement j z) := by
  have each (i : Coordinate) := NativePhysicalTranslation.translate_apply (NativePhysicalTranslation.displacement j z)
    (NativePhysicalFourier.scalarField (velocity seed time) i)
  filter_upwards [assemble_ae (fun i => NativePhysicalTranslation.translate (NativePhysicalTranslation.displacement j z)
      (NativePhysicalFourier.scalarField (velocity seed time) i)),ae_all_iff.mpr each] with x actual rows
  change shifted seed time j z x=_ at actual
  rw [actual]
  apply PiLp.ext
  intro i
  exact congrArg Complex.re (rows i)

theorem shifted_zero (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (j : Coordinate) :
    shifted seed time j 0=realField (velocity seed time) := by
  apply Lp.ext
  filter_upwards [shifted_ae seed time j 0,NativePhysicalFourier.realField_apply (velocity seed time)] with x first last
  rw [first,last]
  simp only [NativePhysicalTranslation.displacement,AddCircle.coe_zero,Pi.single_zero,add_zero]

theorem physicalJet_bound (seed : GeneratedWholeRestartCurrent nu) (time horizon : ℝ)
    (valid : -1<time) (before : time ≤ horizon) (j i : Coordinate) :
    ‖physicalJet seed time valid.le j i‖^2 ≤ (2*Real.pi)^2*NativeWindowSobolevVelocity.budget seed 0 horizon := by
  let B:=UnitAddTorus.mFourierBasis (d := Coordinate)
  have each (k : IntegerWavevector) :
      ‖B.repr (physicalJet seed time valid.le j i) k‖^2 ≤
        (2*Real.pi)^2*NativeWindowSobolevVelocity.wholeDensity seed 0 time k := by
    have component:‖velocity seed time k i‖^2 ≤ complexCoordinateAmplitudeSq (velocity seed time k) := by
      rw [← Complex.normSq_eq_norm_sq]
      exact Finset.single_le_sum (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
    have coordinate:(k j:ℝ)^2 ≤ integerWaveNormSq k :=
      Finset.single_le_sum (fun r _ => sq_nonneg ((k r:ℝ))) (Finset.mem_univ j)
    have root:1 ≤ Real.sqrt (1+integerWaveNormSq k) := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show 1 ≤ 1+integerWaveNormSq k by linarith [integerWaveNormSq_nonneg k])
    have frequency:(k j:ℝ)^2 ≤ (1+integerWaveNormSq k)*Real.sqrt (1+integerWaveNormSq k) :=
      coordinate.trans ((by linarith : integerWaveNormSq k ≤ 1+integerWaveNormSq k).trans
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left root (by positivity [integerWaveNormSq_nonneg k])))
    change ‖UnitAddTorus.mFourierBasis.repr (physicalJet seed time valid.le j i) k‖^2 ≤ _
    rw [UnitAddTorus.mFourierBasis_repr,NativeWindowHistoryFirstJet.physicalJet_fourier,norm_mul,mul_pow,
      NativePhysicalGradient.multiplier_norm_sq]
    have source : NativeEndpointVelocityCarrier.wholeVelocity (NativeForwardWindowSource.source seed time).fst k i=
        velocity seed time k i := by simp only [velocity,NativeForwardWindowEvolution.velocityJet,NativeForwardWindowJets.jet_zero]
    rw [source,mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg (2*Real.pi))
    exact (mul_le_mul_of_nonneg_right frequency (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_left component (by positivity [integerWaveNormSq_nonneg k]))
  have finite:Summable (fun k => ‖B.repr (physicalJet seed time valid.le j i) k‖^2) :=
    NativeWindowGreenTestForm.square_summable (B.repr (physicalJet seed time valid.le j i))
  have bounded:=(finite.tsum_le_tsum each
    ((NativeWindowSobolevVelocity.whole_summable seed 0 time valid).mul_left ((2*Real.pi)^2)))
  rw [← NativeWindowGreenTestForm.norm_square,LinearIsometryEquiv.norm_map,tsum_mul_left] at bounded
  exact bounded.trans (mul_le_mul_of_nonneg_left
    (NativeWindowSobolevVelocity.whole_bound_on_interval seed 0 time horizon valid before) (sq_nonneg _))

def scalarBudget (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : ℝ :=
  (2*Real.pi)*Real.sqrt (max 0 (NativeWindowSobolevVelocity.budget seed 0 horizon))

theorem scalarBudget_nonnegative (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : 0 ≤ scalarBudget seed horizon := by
  unfold scalarBudget
  positivity

theorem scalar_bound (seed : GeneratedWholeRestartCurrent nu) (time horizon : ℝ)
    (valid : -1<time) (before : time ≤ horizon) (j i : Coordinate) :
    ‖physicalJet seed time valid.le j i‖ ≤ scalarBudget seed horizon := by
  apply (sq_le_sq₀ (norm_nonneg _) (scalarBudget_nonnegative seed horizon)).mp
  rw [scalarBudget,mul_pow,Real.sq_sqrt (le_max_left _ _)]
  exact (physicalJet_bound seed time horizon valid before j i).trans
    (mul_le_mul_of_nonneg_left (le_max_right _ _) (sq_nonneg _))

def budget (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : ℝ :=
  (‖lift 0‖+‖lift 1‖+‖lift 2‖)*scalarBudget seed horizon

theorem budget_nonnegative (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : 0 ≤ budget seed horizon := by
  exact mul_nonneg (by positivity) (scalarBudget_nonnegative seed horizon)

theorem gradient_bound (seed : GeneratedWholeRestartCurrent nu) (time horizon : ℝ)
    (valid : -1<time) (before : time ≤ horizon) (j : Coordinate) : ‖gradient seed time valid j‖ ≤ budget seed horizon := by
  have each (i : Coordinate) : ‖lift i (physicalJet seed time valid.le j i)‖ ≤ ‖lift i‖*scalarBudget seed horizon :=
    ((lift i).le_opNorm _).trans (mul_le_mul_of_nonneg_left (scalar_bound seed time horizon valid before j i) (norm_nonneg _))
  change ‖lift 0 _+lift 1 _+lift 2 _‖ ≤ _
  exact (norm_add_le _ _).trans ((add_le_add ((norm_add_le _ _).trans (add_le_add (each 0) (each 1))) (each 2)).trans_eq
    (by unfold budget; ring))

end
end SaturationMonoid.NavierStokes.NativeWindowMeanSpatialJet
