import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Correction
import H0mework.Versions.X.NavierStokes.WindowEnergyAugmented.TimeForm

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowTraceOperator
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWindowStressOseenTest NativeResolventAdjoint
open NativeWindowAugmentedFixedOperator (spectral)
open NativeWindowStressHeatSource (physical)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

def field (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector) (radius : ℕ) : ScalarField :=
  ∑ i : Coordinate,NativeWindowAugmentedSourceForm.matrixField seed time F radius i i

theorem field_original (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector) (radius : ℕ) :
    field seed time F radius= -NativeWindowTraceEnergy.relative seed F radius time := by
  simp only [field,NativeWindowAugmentedSourceForm.matrixField_relative,Finset.sum_neg_distrib,NativeWindowTraceEnergy.relative]

theorem field_split (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector) (radius : ℕ) :
    field seed time F radius=physical (NativeWindowTraceGradient.traceStress seed time F)+NativeWindowTraceEnergy.correction seed F radius time := by
  simp only [field,NativeWindowAugmentedSourceForm.matrixField,Finset.sum_add_distrib,
    NativeWindowTraceGradient.traceStress,NativeWindowTraceEnergy.correction,map_sum]

def read (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector) (radius : ℕ) : C(Torus,ℝ) →L[ℝ] ℝ :=
  (innerSL ℝ (field seed time F radius)).comp physical

def matrixForm (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (M F : Finset IntegerWavevector) (radius : ℕ) :
    physicalSpace M →ₗ[ℝ] physicalSpace M →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => ∑ i : Coordinate,read seed time F radius (evaluate M F i x*evaluate M F i y))
    (fun _ _ _ => by simp only [map_add,add_mul,Finset.sum_add_distrib])
    (fun _ _ _ => by simp only [map_smul,smul_mul_assoc,Finset.smul_sum])
    (fun _ _ _ => by simp only [map_add,mul_add,Finset.sum_add_distrib])
    (fun _ _ _ => by simp only [map_smul,mul_smul_comm,Finset.smul_sum])

def form (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (M L F : Finset IntegerWavevector) (radius : ℕ) :
    physicalSpace M →ₗ[ℝ] physicalSpace M →ₗ[ℝ] ℝ := spectral nu M L+matrixForm seed time M F radius

def test (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (M L F : Finset IntegerWavevector) (radius : ℕ) :
    Module.End ℝ (physicalSpace M) := (duality M).symm.toLinearMap.comp (form seed time M L F radius).flip

theorem test_pairing (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (M L F : Finset IntegerWavevector) (radius : ℕ)
    (x y : physicalSpace M) : pairing M x (test seed time M L F radius y)=form seed time M L F radius x y := by
  have generated := congrArg (fun f : Module.Dual ℝ (physicalSpace M) => f x)
    ((duality M).apply_symm_apply ((form seed time M L F radius).flip y))
  change pairing M (test seed time M L F radius y) x=_ at generated
  rw [pairing_symmetric] at generated
  exact generated

theorem form_symmetric (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (M L F : Finset IntegerWavevector) (radius : ℕ)
    (x y : physicalSpace M) : form seed time M L F radius x y=form seed time M L F radius y x := by
  simp only [form,LinearMap.add_apply,spectral,LinearMap.mk₂_apply,matrixForm]
  congr 1
  · exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => congrArg (fun z : ℝ => _*z) (real_inner_comm _ _)
  · exact Finset.sum_congr rfl fun i _ => congrArg (read seed time F radius) (mul_comm _ _)

def positiveForm (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (M F : Finset IntegerWavevector) (v : physicalSpace M) : ℝ :=
  ∑ i : Coordinate,inner ℝ (physical (NativeWindowTraceGradient.traceStress seed time F))
    (physical (evaluate M F i v*evaluate M F i v))

theorem positiveForm_nonnegative (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (M F : Finset IntegerWavevector) (v : physicalSpace M) :
    0≤positiveForm seed time M F v := by
  have tracePositive (point : Torus) : 0≤NativeWindowTraceGradient.traceStress seed time F point := by
    obtain ⟨x,rfl⟩ := NativeWindowStressHeatSource.circle_surjective point
    simp only [NativeWindowTraceGradient.traceStress,ContinuousMap.sum_apply,NativeWindowFiniteGramFourier.stress_physical]
    exact Finset.sum_nonneg fun i _ => by
      simpa only [NativeWindowFiniteGramSource.stress,NativeWindowStressHeatGram.gram,Matrix.gram_apply] using
        (real_inner_self_nonneg (x := NativeWindowFiniteGramSource.value seed time F x i))
  apply Finset.sum_nonneg
  intro i _
  rw [NativeWindowStressHeatSource.physical_inner]
  apply integral_nonneg
  intro point
  exact mul_nonneg (tracePositive point) (mul_self_nonneg _)

theorem actual_diagonal (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (M F : Finset IntegerWavevector) (radius : ℕ)
    (v : physicalSpace M) (zero : 0∉M) :
    pairing M v (test seed time M M F radius v)=pairing M v v+nu.coeff*curlPair M v.1 v.1+
      positiveForm seed time M F v+NativeWindowTraceCorrection.testForm seed time M F radius v := by
  rw [test_pairing,form,LinearMap.add_apply,LinearMap.add_apply,NativeWindowAugmentedCoercivity.spectral_diagonal M v zero]
  simp only [matrixForm,LinearMap.mk₂_apply,read,ContinuousLinearMap.comp_apply,innerSL_apply_apply,field_split,
    inner_add_left,Finset.sum_add_distrib,positiveForm,NativeWindowTraceCorrection.testForm]
  ring

theorem source_coercivity (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∀ radius≥low,∀ M F : Finset IntegerWavevector,0∉M →FiniteModeNegClosed M →FiniteModeNegClosed F →
      ∀ time∈Icc 0 horizon,∀ v : physicalSpace M,
        pairing M v v+(nu.coeff/2)*curlPair M v.1 v.1≤pairing M v (test seed time M M F radius v) := by
  obtain ⟨low,paid⟩ := NativeWindowTraceCorrection.source_test_bound seed horizon nonnegative
  refine ⟨low,fun radius above M F zero closedM closedF time inside v => ?_⟩
  have bound := (neg_abs_le _).trans' (neg_le_neg (paid radius above M F zero closedM closedF time inside v))
  have positive := positiveForm_nonnegative seed time M F v
  rw [actual_diagonal seed time M F radius v zero]
  linarith only [bound,positive]

def jointTest (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (M F : Finset IntegerWavevector) (radius : ℕ) :
    Module.End ℝ (physicalSpace M) := LinearMap.id-test seed time M M F radius

theorem jointTest_pairing (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (M F : Finset IntegerWavevector) (radius : ℕ)
    (x y : physicalSpace M) : pairing M x (jointTest seed time M F radius y)=pairing M x y-spectral nu M M x y+
      ∑ i : Coordinate,inner ℝ (NativeWindowTraceEnergy.relative seed F radius time)
        (physical (evaluate M F i x*evaluate M F i y)) := by
  simp only [jointTest,LinearMap.sub_apply,LinearMap.id_apply,map_sub,test_pairing,form,
    LinearMap.add_apply,matrixForm,LinearMap.mk₂_apply,read,ContinuousLinearMap.comp_apply,innerSL_apply_apply,
    field_original,inner_neg_left,Finset.sum_neg_distrib]
  ring

end
end SaturationMonoid.NavierStokes.NativeWindowTraceOperator
