import H0mework.Versions.X.NavierStokes.WindowEnergyCrossHistory.Action
import H0mework.NavierStokes.Fourier.UnitCellDivergence

set_option autoImplicit false
open scoped BigOperators Topology ContDiff ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowCrossHistoryGreen
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalPeriodicCoarseVectorCalculus
open ThreeDimensionalPeriodicUnitCellDivergence ThreeDimensionalVorticityCoefficientPhysicalCompiler
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier NativeWindowCrossHistoryAction
noncomputable section
variable {nu : Viscosity}

def vector (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ) (x : PhysicalSpace) : PhysicalSpace :=
  WithLp.toLp 2 fun i => velocity seed F time i (NativeFullOrderSynthesis.circlePoint x)

theorem vector_original (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ) :
    vector seed F time = finiteRealComplexFourierField F
      (NativeEndpointVelocityCarrier.wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst) := by
  funext x
  apply PiLp.ext
  intro i
  simp only [vector,PiLp.toLp_apply,velocity,NativeWindowStressHeatTime.field_original,
    NativeWindowFiniteGramFourier.read_physical,NativeWindowFiniteGramSource.fieldRead_original]

theorem vector_smooth (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ) :
    ContDiff ℝ ∞ (vector seed F time) := by
  rw [vector_original]
  exact finiteRealComplexFourierField_contDiff _ _

theorem vector_periodic (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ) :
    LatticePeriodic (vector seed F time) := by
  rw [vector_original]
  exact finiteRealComplexFourierField_latticePeriodic _ _

theorem pair_inner (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (first last : ℝ) (x : PhysicalSpace) :
    pair (velocity seed F first) (velocity seed F last) (NativeFullOrderSynthesis.circlePoint x) =
      inner ℝ (vector seed F first x) (vector seed F last x) := by
  simp only [pair,ContinuousMap.sum_apply,ContinuousMap.mul_apply,PiLp.inner_apply,vector,RCLike.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

def flux (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (first last : ℝ) (x : PhysicalSpace) : PhysicalSpace :=
  inner ℝ (vector seed F first x) (vector seed F last x)^2 • (vector seed F first x+vector seed F last x)

theorem flux_smooth (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (first last : ℝ) :
    ContDiff ℝ ∞ (flux seed F first last) :=
  (((vector_smooth seed F first).inner ℝ (vector_smooth seed F last)).pow 2).smul
    ((vector_smooth seed F first).add (vector_smooth seed F last))

theorem flux_periodic (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (first last : ℝ) :
    LatticePeriodic (flux seed F first last) := by
  intro shift x
  simp only [flux,vector_periodic seed F first shift x,vector_periodic seed F last shift x]

theorem flux_coordinate (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (first last : ℝ)
    (x : PhysicalSpace) (i : Coordinate) : flux seed F first last x i =
      ((velocity seed F first i+velocity seed F last i)*pair (velocity seed F first) (velocity seed F last)^2)
        (NativeFullOrderSynthesis.circlePoint x) := by
  rw [flux,← pair_inner]
  simp only [PiLp.smul_apply,PiLp.add_apply,vector,ContinuousMap.mul_apply,ContinuousMap.add_apply,ContinuousMap.pow_apply,smul_eq_mul]
  ring

theorem flux_divergence (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (first last : ℝ)
    (first0 : 0 ≤ first) (last0 : 0 ≤ last) (x : PhysicalSpace) :
    velocityDivergence (flux seed F first last) x = 2*(pair (velocity seed F first) (velocity seed F last)*
      common (velocity seed F first) (velocity seed F last) (gradient seed F first) (gradient seed F last))
        (NativeFullOrderSynthesis.circlePoint x) := by
  have diagonal (j : Coordinate) : (fderiv ℝ (flux seed F first last) x (EuclideanSpace.single j 1)) j =
      (((gradient seed F first j j+gradient seed F last j j)*pair (velocity seed F first) (velocity seed F last)^2+
        (2 : ℝ) • ((velocity seed F first j+velocity seed F last j)*pair (velocity seed F first) (velocity seed F last)*
          crossDerivative (velocity seed F first) (velocity seed F last) (gradient seed F first) (gradient seed F last) j))
        (NativeFullOrderSynthesis.circlePoint x)) := by
    have source := flux_derivative seed F first last j x 0
    have path := (hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single j (1 : ℝ)) |>.const_add x
    have actual := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Coordinate => ℝ) j).hasFDerivAt.comp_hasDerivAt 0
      (((flux_smooth seed F first last).differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt 0 path)
    simp only [Function.comp_def,id_eq,zero_smul,add_zero,one_smul,
      PiLp.proj_apply,flux_coordinate,NativeWindowFiniteGramSource.line] at actual source
    exact actual.unique source
  change (∑ j : Coordinate, (fderiv ℝ (flux seed F first last) x (EuclideanSpace.single j 1)) j) = _
  simp_rw [diagonal]
  have firstZero := congrArg (fun f : C(Torus,ℝ) => f (NativeFullOrderSynthesis.circlePoint x)) (gradient_trace_zero seed F first first0)
  have lastZero := congrArg (fun f : C(Torus,ℝ) => f (NativeFullOrderSynthesis.circlePoint x)) (gradient_trace_zero seed F last last0)
  simp only [ContinuousMap.sum_apply,ContinuousMap.zero_apply] at firstZero lastZero
  simp only [common,ContinuousMap.sum_apply,ContinuousMap.add_apply,ContinuousMap.mul_apply,ContinuousMap.pow_apply,
    ContinuousMap.smul_apply,smul_eq_mul,Finset.sum_add_distrib,← Finset.sum_mul,Finset.mul_sum]
  rw [firstZero,lastZero]
  ring

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem torus_cell (field : C(Torus,ℝ)) : (∫ point : Torus, field point) =
    ∫ x in coordinateUnitCube, field (NativeFullOrderSynthesis.circlePoint (coordinateEquiv.symm x)) := by
  rw [UnitAddTorus.integral_preimage (fun point => field point) (0 : Coordinate → ℝ)]
  simp only [Pi.zero_apply,zero_add]
  rw [show {x : Coordinate → ℝ | ∀ i, x i ∈ Ioc (0 : ℝ) 1} = Set.pi univ (fun _ : Coordinate => Ioc (0 : ℝ) 1) by ext x; simp]
  change (∫ x in Set.pi univ (fun _ : Coordinate => Ioc (0 : ℝ) 1), field (fun i => (x i : UnitAddCircle))) = _
  have same : (Set.pi univ (fun _ : Coordinate => Ioc (0 : ℝ) 1)) =ᵐ[(volume : Measure (Coordinate → ℝ))]
      Icc (0 : Coordinate → ℝ) (fun _ => 1) :=
    MeasureTheory.Measure.univ_pi_Ioc_ae_eq_Icc (μ := fun _ : Coordinate => (volume : Measure ℝ))
  rw [setIntegral_congr_set same]
  rfl

theorem common_integral_zero (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (first last : ℝ)
    (first0 : 0 ≤ first) (last0 : 0 ≤ last) :
    (∫ point : Torus, (pair (velocity seed F first) (velocity seed F last)*
      common (velocity seed F first) (velocity seed F last) (gradient seed F first) (gradient seed F last)) point) = 0 := by
  have source := coordinateUnitCube_velocityDivergence_integral_eq_zero (flux seed F first last)
    ((flux_smooth seed F first last).of_le (by simp)) (flux_periodic seed F first last)
  simp only [flux_divergence seed F first last first0 last0] at source
  rw [integral_const_mul] at source
  rw [torus_cell]
  linarith

theorem paired_work_green (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (first last : ℝ)
    (first0 : 0 ≤ first) (last0 : 0 ≤ last) :
    (∫ point : Torus, (pair (velocity seed F first) (velocity seed F last)*pairAction seed F first last) point) =
      -(1/2 : ℝ)*(∫ point : Torus, (pair (velocity seed F first) (velocity seed F last)*
        increment (velocity seed F first) (velocity seed F last) (gradient seed F first) (gradient seed F last)) point)+
      (∫ point : Torus, (pair (velocity seed F first) (velocity seed F last)*
        (pair (retained seed F first) (velocity seed F last)+pair (velocity seed F first) (retained seed F last))) point) := by
  have original : pair (velocity seed F first) (velocity seed F last)*pairAction seed F first last =
      -(1/2 : ℝ) • (pair (velocity seed F first) (velocity seed F last)*
        common (velocity seed F first) (velocity seed F last) (gradient seed F first) (gradient seed F last))-
      (1/2 : ℝ) • (pair (velocity seed F first) (velocity seed F last)*
        increment (velocity seed F first) (velocity seed F last) (gradient seed F first) (gradient seed F last))+
      pair (velocity seed F first) (velocity seed F last)*
        (pair (retained seed F first) (velocity seed F last)+pair (velocity seed F first) (retained seed F last)) := by
    rw [source_split]
    ext point
    simp only [ContinuousMap.mul_apply,ContinuousMap.add_apply,ContinuousMap.sub_apply,ContinuousMap.smul_apply,smul_eq_mul]
    ring
  rw [original]
  have paid (field : C(Torus,ℝ)) : Integrable field := field.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace field)
  have addition (f g : C(Torus,ℝ)) : (∫ point : Torus, (f+g) point) = (∫ point, f point)+(∫ point, g point) :=
    integral_add (paid f) (paid g)
  have subtraction (f g : C(Torus,ℝ)) : (∫ point : Torus, (f-g) point) = (∫ point, f point)-(∫ point, g point) :=
    integral_sub (paid f) (paid g)
  rw [addition,subtraction]
  have scaling (r : ℝ) (f : C(Torus,ℝ)) : (∫ point : Torus, (r • f) point) = r*(∫ point, f point) :=
    integral_smul r (fun point => f point)
  rw [scaling,scaling,common_integral_zero seed F first last first0 last0]
  ring

open NativeUnheatedStressPairEvolution

theorem nonlinear_work_double (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (observation : ℝ) (nonnegative : 0 ≤ observation) :
    NativeWindowStressHeatBalance.nonlinearWork seed observation F =
      ∑ output : Coordinate, ∑ input : Coordinate,
        ∫ times : ℝ × ℝ, kernelWeight 0 observation 0 times.1*kernelWeight 0 observation 0 times.2*
          (∫ point : Torus, NativeWindowStressHeatTime.product seed F output input times.1 point*
            NativeWindowStressHeatTime.nonlinearPair seed F output input times.2 point)
          ∂(volume.restrict (Ioc (observation+1) (observation+2))).prod
            (volume.restrict (Ioc (observation+1) (observation+2))) := by
  unfold NativeWindowStressHeatBalance.nonlinearWork
  apply Finset.sum_congr rfl
  intro output _
  apply Finset.sum_congr rfl
  intro input _
  let P := fun time => kernelWeight 0 observation 0 time • NativeWindowStressHeatTime.product seed F output input time
  let Q := fun time => kernelWeight 0 observation 0 time • NativeWindowStressHeatTime.nonlinearPair seed F output input time
  have pi : IntervalIntegrable P volume (observation+1) (observation+2) :=
    ((NativeWindowStressHeatTime.product_ac seed F output input (observation+1) (observation+2)
      (by linarith) (by linarith)).continuousOn.intervalIntegrable (μ := volume)).continuousOn_smul
      (kernelWeight_continuous 0 observation 0).continuousOn
  have qi : IntervalIntegrable Q volume (observation+1) (observation+2) :=
    (NativeWindowStressHeatBalance.nonlinear_integrable seed F output input (observation+1) (observation+2)
      (by linarith) (by linarith)).continuousOn_smul (kernelWeight_continuous 0 observation 0).continuousOn
  have average : (∫ time in observation+1..observation+2, P time) =
      NativeWindowFiniteGramFourier.stress seed observation F output input := by
    rw [← NativeWindowStressHeatTime.jet_zero seed F output input observation]
    exact (NativeWindowStressHeatTime.kernel_integral (NativeWindowStressHeatTime.product seed F output input) 0 observation).symm
  have computed := integral_prod_bilin (innerSL ℝ (E := NativePhysicalFourier.ScalarField))
    (NativeWindowStressHeatSource.physical.integrable_comp pi.1)
    (NativeWindowStressHeatSource.physical.integrable_comp qi.1)
  rw [NativeWindowStressHeatSource.physical.integral_comp_comm pi.1,
    NativeWindowStressHeatSource.physical.integral_comp_comm qi.1] at computed
  rw [← intervalIntegral.integral_of_le (show observation+1 ≤ observation+2 by linarith),
    ← intervalIntegral.integral_of_le (show observation+1 ≤ observation+2 by linarith),average] at computed
  simp only [NativeWindowStressHeatBalance.sigma,NativeWindowStressHeatBalance.nonlinearWindow,map_neg,inner_neg_neg]
  refine computed.symm.trans ?_
  apply integral_congr_ae
  filter_upwards with times
  change inner ℝ (NativeWindowStressHeatSource.physical (P times.1)) (NativeWindowStressHeatSource.physical (Q times.2)) = _
  simp only [P,Q,map_smul,real_inner_smul_left,real_inner_smul_right,NativeWindowStressHeatSource.physical_inner]
  ring


end
end SaturationMonoid.NavierStokes.NativeWindowCrossHistoryGreen
