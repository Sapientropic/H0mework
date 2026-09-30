import H0mework.NavierStokes.WindowEnergyTimeIncrement.Source
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
open scoped Topology BigOperators ENNReal TensorProduct
namespace SaturationMonoid.NavierStokes.NativeWindowLowAdvectorHistory
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeForwardWindowPairingReadout NativeWindowFiniteGramSource NativePhysicalFourier
noncomputable section

abbrev jointMeasure := averageMeasure.prod averageMeasure

def synthesis (first last : Coordinate → H) (times : ℝ × ℝ) : ℝ :=
  ∑ i : Coordinate, first i times.1*last i times.2

theorem scalar_product_integrable (first last : H) :
    Integrable (fun time => first time*last time) averageMeasure := by
  simpa only [RCLike.inner_apply,conj_trivial,mul_comm] using L2.integrable_inner (𝕜 := ℝ) first last

theorem scalar_product_integral (first last : H) :
    (∫ time, first time*last time ∂averageMeasure) = inner ℝ first last := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards with time
  change first time*last time = last time*first time
  ring

theorem row_product_integrable (f g u v : Coordinate → H) (i j : Coordinate) :
    Integrable (fun times : ℝ × ℝ => (f i times.1*g i times.2)*(u j times.1*v j times.2)) jointMeasure := by
  have paid := (scalar_product_integrable (f i) (u j)).mul_prod (scalar_product_integrable (g i) (v j))
  convert! paid using 1
  ext times
  ring

theorem product_integrable (f g u v : Coordinate → H) :
    Integrable (fun times => synthesis f g times*synthesis u v times) jointMeasure := by
  have paid := integrable_finsetSum Finset.univ fun j _ =>
    integrable_finsetSum Finset.univ fun i _ => row_product_integrable f g u v i j
  simpa only [synthesis,Finset.sum_mul,Finset.mul_sum] using paid

theorem product_integral (f g u v : Coordinate → H) :
    (∫ times, synthesis f g times*synthesis u v times ∂jointMeasure) =
      inner ℝ (NativeWindowCrossHistoryAction.tensorPair f g) (NativeWindowCrossHistoryAction.tensorPair u v) := by
  simp only [synthesis,Finset.sum_mul,Finset.mul_sum,NativeWindowCrossHistoryAction.tensorPair,sum_inner,inner_sum,TensorProduct.inner_tmul]
  rw [integral_finsetSum Finset.univ (fun j _ => integrable_finsetSum Finset.univ (fun i _ => row_product_integrable f g u v i j))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum Finset.univ (fun i _ => row_product_integrable f g u v i j)]
  apply Finset.sum_congr rfl
  intro i _
  have same : (fun times : ℝ × ℝ => (f i times.1*g i times.2)*(u j times.1*v j times.2)) =
      fun times => (f i times.1*u j times.1)*(g i times.2*v j times.2) := by ext times; ring
  rw [same]
  exact (integral_prod_mul (μ := averageMeasure) (ν := averageMeasure)
    (fun time => f i time*u j time) (fun time => g i time*v j time)).trans (by
      rw [scalar_product_integral,scalar_product_integral])

theorem square_integral (f g : Coordinate → H) :
    (∫ times, synthesis f g times^2 ∂jointMeasure) = ‖NativeWindowCrossHistoryAction.tensorPair f g‖^2 := by
  rw [show (fun times => synthesis f g times^2) = (fun times => synthesis f g times*synthesis f g times) by ext; ring,
    product_integral]
  exact real_inner_self_eq_norm_sq (NativeWindowCrossHistoryAction.tensorPair f g)

theorem difference_square_integrable (f g u v : Coordinate → H) :
    Integrable (fun times => (synthesis f g times-synthesis u v times)^2) jointMeasure := by
  have paid := ((product_integrable f g f g).sub ((product_integrable f g u v).const_mul 2)).add (product_integrable u v u v)
  convert! paid using 1
  ext times
  simp only [Pi.add_apply,Pi.sub_apply]
  ring

theorem difference_square_integral (f g u v : Coordinate → H) :
    (∫ times, (synthesis f g times-synthesis u v times)^2 ∂jointMeasure) =
      ‖NativeWindowCrossHistoryAction.tensorPair f g-NativeWindowCrossHistoryAction.tensorPair u v‖^2 := by
  have same : (fun times => (synthesis f g times-synthesis u v times)^2) =
      fun times => (synthesis f g times*synthesis f g times-2*(synthesis f g times*synthesis u v times))+
        synthesis u v times*synthesis u v times := by ext; ring
  have expanded := integral_add' ((product_integrable f g f g).sub ((product_integrable f g u v).const_mul 2)) (product_integrable u v u v)
  rw [integral_sub' (product_integrable f g f g) ((product_integrable f g u v).const_mul 2),integral_const_mul,
    product_integral,product_integral,product_integral] at expanded
  simp only [Pi.add_apply,Pi.sub_apply] at expanded
  rw [same,expanded]
  have squared := real_inner_self_eq_norm_sq (NativeWindowCrossHistoryAction.tensorPair f g-NativeWindowCrossHistoryAction.tensorPair u v)
  simp only [inner_sub_left,inner_sub_right] at squared
  have symmetry := real_inner_comm (NativeWindowCrossHistoryAction.tensorPair f g) (NativeWindowCrossHistoryAction.tensorPair u v)
  linarith only [squared,symmetry]

variable {nu : Viscosity}

def pairField (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (F : Finset IntegerWavevector) (times : ℝ × ℝ) : C(Torus,ℝ) :=
  NativeWindowCrossHistoryAction.pair (NativeWindowCrossHistoryAction.velocity seed F (observation-times.1))
    (NativeWindowCrossHistoryAction.velocity seed F (observation-times.2))

def wedgeField (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (F : Finset IntegerWavevector)
    (direction : Coordinate) (times : ℝ × ℝ) : C(Torus,ℝ) :=
  NativeWindowCrossHistoryAction.wedge (NativeWindowCrossHistoryAction.velocity seed F (observation-times.1))
    (NativeWindowCrossHistoryAction.velocity seed F (observation-times.2))
    (NativeWindowCrossHistoryAction.gradient seed F (observation-times.1))
    (NativeWindowCrossHistoryAction.gradient seed F (observation-times.2)) direction

theorem value_read (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (F : Finset IntegerWavevector) (x : PhysicalSpace) :
    ∀ᵐ shift ∂averageMeasure, ∀ i : Coordinate, value seed observation F x i shift =
      NativeWindowCrossHistoryAction.velocity seed F (observation-shift) i (NativeFullOrderSynthesis.circlePoint x) := by
  apply eventually_countable_forall.mpr
  intro i
  filter_upwards [lift_ae seed observation (fieldRead F x i)] with shift same
  rw [NativeWindowCrossHistoryAction.velocity,NativeWindowStressHeatTime.field_original,NativeWindowFiniteGramFourier.read_physical]
  exact same

theorem gradient_read (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (F : Finset IntegerWavevector)
    (x : PhysicalSpace) (j : Coordinate) : ∀ᵐ shift ∂averageMeasure, ∀ i : Coordinate, gradient seed observation F x j i shift =
      NativeWindowCrossHistoryAction.gradient seed F (observation-shift) j i (NativeFullOrderSynthesis.circlePoint x) := by
  apply eventually_countable_forall.mpr
  intro i
  filter_upwards [lift_ae seed observation (gradientRead F x j i)] with shift same
  rw [NativeWindowCrossHistoryAction.gradient,NativeWindowStressHeatSource.jetRead_first]
  exact same

theorem pair_represented (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (F : Finset IntegerWavevector) (x : PhysicalSpace) :
    (fun times => pairField seed observation F times (NativeFullOrderSynthesis.circlePoint x)) =ᵐ[jointMeasure]
      synthesis (value seed observation F x) (value seed observation F x) := by
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := averageMeasure) (ν := averageMeasure)).ae (value_read seed observation F x),
    (Measure.quasiMeasurePreserving_snd (μ := averageMeasure) (ν := averageMeasure)).ae (value_read seed observation F x)] with times first last
  simp only [pairField,NativeWindowCrossHistoryAction.pair,ContinuousMap.sum_apply,ContinuousMap.mul_apply,synthesis]
  apply Finset.sum_congr rfl
  intro i _
  rw [← first i,← last i]

theorem wedge_represented (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (F : Finset IntegerWavevector)
    (x : PhysicalSpace) (j : Coordinate) :
    (fun times => wedgeField seed observation F j times (NativeFullOrderSynthesis.circlePoint x)) =ᵐ[jointMeasure]
      fun times => synthesis (gradient seed observation F x j) (value seed observation F x) times-
        synthesis (value seed observation F x) (gradient seed observation F x j) times := by
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := averageMeasure) (ν := averageMeasure)).ae (value_read seed observation F x),
    (Measure.quasiMeasurePreserving_snd (μ := averageMeasure) (ν := averageMeasure)).ae (value_read seed observation F x),
    (Measure.quasiMeasurePreserving_fst (μ := averageMeasure) (ν := averageMeasure)).ae (gradient_read seed observation F x j),
    (Measure.quasiMeasurePreserving_snd (μ := averageMeasure) (ν := averageMeasure)).ae (gradient_read seed observation F x j)] with times first last dfirst dlast
  simp only [wedgeField,NativeWindowCrossHistoryAction.wedge,NativeWindowCrossHistoryAction.pair,
    ContinuousMap.sub_apply,ContinuousMap.sum_apply,ContinuousMap.mul_apply,synthesis]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _
  · rw [← dfirst i,← last i]
  · rw [← first i,← dlast i]

theorem pair_square_integrable (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (F : Finset IntegerWavevector) (point : Torus) :
    Integrable (fun times => pairField seed observation F times point^2) jointMeasure := by
  obtain ⟨x,rfl⟩ := NativeWindowStressHeatSource.circle_surjective point
  have paid : Integrable (fun times => synthesis (value seed observation F x) (value seed observation F x) times^2) jointMeasure := by
    simpa only [pow_two] using product_integrable (value seed observation F x) (value seed observation F x) (value seed observation F x) (value seed observation F x)
  exact paid.congr ((pair_represented seed observation F x).fun_comp (fun r : ℝ => r^2)).symm

theorem pair_square_integral (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (F : Finset IntegerWavevector) (point : Torus) :
    (∫ times, pairField seed observation F times point^2 ∂jointMeasure) =
      ∑ i : Coordinate, ∑ j : Coordinate, NativeWindowFiniteGramFourier.stress seed observation F i j point^2 := by
  obtain ⟨x,rfl⟩ := NativeWindowStressHeatSource.circle_surjective point
  have represented := integral_congr_ae ((pair_represented seed observation F x).fun_comp (fun r : ℝ => r^2))
  simp only [Function.comp_def] at represented
  rw [represented,square_integral,
    NativeWindowCrossHistoryAction.source_tensor_mass]
  simp only [NativeWindowFiniteGramFourier.stress_physical]

theorem wedge_square_integrable (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (F : Finset IntegerWavevector)
    (j : Coordinate) (point : Torus) : Integrable (fun times => wedgeField seed observation F j times point^2) jointMeasure := by
  obtain ⟨x,rfl⟩ := NativeWindowStressHeatSource.circle_surjective point
  exact (difference_square_integrable (gradient seed observation F x j) (value seed observation F x)
    (value seed observation F x) (gradient seed observation F x j)).congr
      ((wedge_represented seed observation F x j).fun_comp (fun r : ℝ => r^2)).symm

theorem wedge_square_bound (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (F : Finset IntegerWavevector) (point : Torus) :
    (∫ times, (∑ j : Coordinate, wedgeField seed observation F j times point^2) ∂jointMeasure) ≤
      4*NativeWindowStressHeatSource.interaction seed observation F point := by
  obtain ⟨x,rfl⟩ := NativeWindowStressHeatSource.circle_surjective point
  rw [integral_finsetSum Finset.univ (fun j _ => wedge_square_integrable seed observation F j _)]
  have same (j : Coordinate) : (∫ times, wedgeField seed observation F j times (NativeFullOrderSynthesis.circlePoint x)^2 ∂jointMeasure) =
      ‖NativeWindowCrossHistoryAction.tensorPair (gradient seed observation F x j) (value seed observation F x)-
        NativeWindowCrossHistoryAction.tensorPair (value seed observation F x) (gradient seed observation F x j)‖^2 := by
    have represented := integral_congr_ae ((wedge_represented seed observation F x j).fun_comp (fun r : ℝ => r^2))
    simp only [Function.comp_def] at represented
    rw [represented,difference_square_integral]
  simp_rw [same]
  rw [← NativeWindowCrossHistoryAction.source_tensor_energy seed observation F x]
  exact Finset.sum_le_sum fun j _ => le_add_of_nonneg_left (sq_nonneg _)

theorem read_memLp (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ)
    (read : NativeCompleteStressAction.FullSpace →L[ℝ] C(Torus,ℝ)) :
    MemLp (fun shift => read (NativeUnifiedCompleteSource.source seed (observation-shift))) ∞ averageMeasure := by
  apply memLp_top_of_bound (read.integrable_comp (original_integrable seed observation)).aestronglyMeasurable
    (‖read‖*NativeUnifiedCompleteSource.budget seed)
  filter_upwards with shift
  exact (read.le_opNorm _).trans (mul_le_mul_of_nonneg_left (NativeUnifiedCompleteSource.source_bound seed _) (norm_nonneg _))

theorem left_memLp (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ)
    (read : NativeCompleteStressAction.FullSpace →L[ℝ] C(Torus,ℝ)) :
    MemLp (fun times : ℝ × ℝ => read (NativeUnifiedCompleteSource.source seed (observation-times.1))) ∞ jointMeasure :=
  (read_memLp seed observation read).comp_measurePreserving measurePreserving_fst

theorem right_memLp (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ)
    (read : NativeCompleteStressAction.FullSpace →L[ℝ] C(Torus,ℝ)) :
    MemLp (fun times : ℝ × ℝ => read (NativeUnifiedCompleteSource.source seed (observation-times.2))) ∞ jointMeasure :=
  (read_memLp seed observation read).comp_measurePreserving measurePreserving_snd

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime in
theorem source_next_ae (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    ∀ᵐ times : ℝ × ℝ ∂jointMeasure,
      NativeUnifiedCompleteSource.source seed (step.2.clockAdvance+time-times.1) = NativeUnifiedCompleteSource.source step.1 (time-times.1) ∧
      NativeUnifiedCompleteSource.source seed (step.2.clockAdvance+time-times.2) = NativeUnifiedCompleteSource.source step.1 (time-times.2) := by
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := averageMeasure) (ν := averageMeasure)).ae NativeWindowHistoryGNS.average_support,
    (Measure.quasiMeasurePreserving_snd (μ := averageMeasure) (ν := averageMeasure)).ae NativeWindowHistoryGNS.average_support] with times first last
  constructor <;> rw [add_sub_assoc]
  · exact NativeUnifiedCompleteSource.source_generated_next seed step generated (time-times.1) (by linarith)
  · exact NativeUnifiedCompleteSource.source_generated_next seed step generated (time-times.2) (by linarith)

end
end SaturationMonoid.NavierStokes.NativeWindowLowAdvectorHistory
