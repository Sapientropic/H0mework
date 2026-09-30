import H0mework.Versions.X.NavierStokes.WindowStressHeat.OseenApprox
import H0mework.Versions.X.NavierStokes.WindowSource.OperatorGreenSource
import Mathlib.LinearAlgebra.Dual.Lemmas

set_option autoImplicit false
open scoped BigOperators ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowStressOseenTest
open MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open NativePhysicalFourier NativeFiniteActionResolvent NativeResolventAdjoint NativeWindowOperatorGreen
noncomputable section
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
variable {nu : Viscosity}

def evaluate (modes F : Finset IntegerWavevector) (coordinate : Coordinate) : physicalSpace modes →ₗ[ℝ] C(Torus,ℝ) :=
  ∑ wave ∈ F, (NativeWindowStressHeatBalance.basis wave).toLinearMap.comp
    (((ContinuousLinearMap.proj coordinate).comp (lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave)).toLinearMap.comp
      (physicalSpace modes).subtype)

theorem evaluate_apply (modes F : Finset IntegerWavevector) (coordinate : Coordinate) (value : physicalSpace modes) :
    evaluate modes F coordinate value = ∑ wave ∈ F, NativeWindowStressHeatBalance.basis wave (value.1 wave coordinate) := by
  rw [evaluate,LinearMap.sum_apply]
  rfl

def mean : C(Torus,ℝ) →ₗ[ℝ] ℝ :=
  ((innerSL ℝ (NativeWindowStressHeatSource.physical 1)).comp NativeWindowStressHeatSource.physical).toLinearMap

theorem mean_apply (field : C(Torus,ℝ)) : mean field = ∫ point, field point := by
  change inner ℝ (NativeWindowStressHeatSource.physical 1) (NativeWindowStressHeatSource.physical field) = _
  rw [NativeWindowStressHeatSource.physical_inner]
  simp only [ContinuousMap.one_apply,one_mul]

def form (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (modes F : Finset IntegerWavevector) :
    physicalSpace modes →ₗ[ℝ] physicalSpace modes →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => ∑ output : Coordinate, ∑ input : Coordinate,
    mean (NativeWindowFiniteGramFourier.stress seed time F output input*evaluate modes F output x*evaluate modes F input y))
    (fun _ _ _ => by simp only [map_add,mul_add,add_mul,Finset.sum_add_distrib])
    (fun _ _ _ => by simp only [map_smul,mul_smul_comm,smul_mul_assoc,Finset.smul_sum])
    (fun _ _ _ => by simp only [map_add,mul_add,Finset.sum_add_distrib])
    (fun _ _ _ => by simp only [map_smul,mul_smul_comm,Finset.smul_sum])

theorem form_apply (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (modes F : Finset IntegerWavevector)
    (x y : physicalSpace modes) : form seed time modes F x y = ∑ output : Coordinate, ∑ input : Coordinate,
      mean (NativeWindowFiniteGramFourier.stress seed time F output input*evaluate modes F output x*evaluate modes F input y) := rfl

theorem stress_symmetric (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (output input : Coordinate) : NativeWindowFiniteGramFourier.stress seed time F output input =
      NativeWindowFiniteGramFourier.stress seed time F input output := by
  ext point
  simp only [NativeWindowFiniteGramFourier.stress_apply]
  apply integral_congr_ae
  filter_upwards with shift
  exact mul_comm _ _

theorem form_symmetric (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (modes F : Finset IntegerWavevector)
    (x y : physicalSpace modes) : form seed time modes F x y = form seed time modes F y x := by
  rw [form_apply,form_apply,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro output _
  apply Finset.sum_congr rfl
  intro input _
  rw [stress_symmetric seed time F input output]
  apply congrArg mean
  ring

theorem form_integral (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (modes F : Finset IntegerWavevector)
    (x y : physicalSpace modes) : form seed time modes F x y =
      ∫ point : Torus, ∑ output : Coordinate, ∑ input : Coordinate,
        NativeWindowFiniteGramFourier.stress seed time F output input point*
          evaluate modes F output x point*evaluate modes F input y point := by
  rw [form_apply]
  calc
    _ = mean (∑ output : Coordinate, ∑ input : Coordinate,
        NativeWindowFiniteGramFourier.stress seed time F output input*evaluate modes F output x*evaluate modes F input y) := by
      simp only [map_sum]
    _ = _ := by
      rw [mean_apply]
      simp only [ContinuousMap.sum_apply,ContinuousMap.mul_apply]

theorem gram_square {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (value : Coordinate → H) (weight : Coordinate → ℝ) :
    (∑ output : Coordinate, ∑ input : Coordinate,
      NativeWindowStressHeatGram.gram value output input*weight output*weight input) =
      ‖∑ coordinate : Coordinate, weight coordinate • value coordinate‖^2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,NativeWindowStressHeatGram.gram,Matrix.gram_apply]
  apply Finset.sum_congr rfl
  intro output _
  apply Finset.sum_congr rfl
  intro input _
  rw [real_inner_comm (value input) (value output)]
  ring

theorem form_positive (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (modes F : Finset IntegerWavevector)
    (value : physicalSpace modes) : 0 ≤ form seed time modes F value value := by
  rw [form_integral]
  apply integral_nonneg
  intro point
  obtain ⟨x,rfl⟩ := NativeWindowStressHeatSource.circle_surjective point
  simp only [NativeWindowFiniteGramFourier.stress_physical,NativeWindowFiniteGramSource.stress]
  rw [gram_square]
  positivity

theorem pairing_injective (modes : Finset IntegerWavevector) : Function.Injective (pairing modes) := by
  intro x y same
  apply sub_eq_zero.mp
  apply pairing_faithful modes
  have zero : pairing modes (x-y) = 0 := by rw [map_sub,same,sub_self]
  rw [zero,LinearMap.zero_apply]

def duality (modes : Finset IntegerWavevector) : physicalSpace modes ≃ₗ[ℝ] Module.Dual ℝ (physicalSpace modes) :=
  LinearMap.linearEquivOfInjective (pairing modes) (pairing_injective modes)
    (Subspace.dual_finrank_eq (K := ℝ) (V := physicalSpace modes)).symm

def operator (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (modes F : Finset IntegerWavevector) :
    Module.End ℝ (physicalSpace modes) :=
  (duality modes).symm.toLinearMap.comp (form seed time modes F).flip

theorem operator_pairing (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (modes F : Finset IntegerWavevector)
    (x y : physicalSpace modes) : pairing modes x (operator seed time modes F y) = form seed time modes F x y := by
  have generated := congrArg (fun functional : Module.Dual ℝ (physicalSpace modes) => functional x)
    ((duality modes).apply_symm_apply ((form seed time modes F).flip y))
  change pairing modes (operator seed time modes F y) x = _ at generated
  rw [pairing_symmetric] at generated
  exact generated

theorem operator_selfadjoint (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (modes F : Finset IntegerWavevector)
    (x y : physicalSpace modes) : pairing modes (operator seed time modes F x) y = pairing modes x (operator seed time modes F y) := by
  rw [pairing_symmetric,operator_pairing,form_symmetric,operator_pairing]

def massOperator (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (modes F : Finset IntegerWavevector) :
    Module.End ℝ (physicalSpace modes) := LinearMap.id+operator seed time modes F

theorem mass_floor (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (modes F : Finset IntegerWavevector)
    (value : physicalSpace modes) : pairing modes value value ≤ pairing modes value (massOperator seed time modes F value) := by
  simp only [massOperator,LinearMap.add_apply,LinearMap.id_apply,map_add,operator_pairing]
  exact le_add_of_nonneg_right (form_positive seed time modes F value)

theorem convection_work (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (modes F : Finset IntegerWavevector)
    (zero : 0 ∉ modes) (closed : FiniteModeNegClosed modes) (advector : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality advector) (value : physicalSpace modes) :
    let K := convection modes zero closed nu advector reality
    let T := operator seed time modes F
    2*pairing modes (K value) (T value) = pairing modes value (T (K value)-K (T value)) := by
  dsimp only
  rw [map_sub]
  have skew := convection_skew modes zero closed nu advector reality value (operator seed time modes F value)
  have same : pairing modes value (operator seed time modes F (convection modes zero closed nu advector reality value)) =
      pairing modes (convection modes zero closed nu advector reality value) (operator seed time modes F value) := by
    rw [operator_pairing,operator_pairing,form_symmetric]
  rw [same]
  linarith

theorem mass_commutator (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (modes F : Finset IntegerWavevector)
    (action : Module.End ℝ (physicalSpace modes)) (value : physicalSpace modes) :
    massOperator seed time modes F (action value)-action (massOperator seed time modes F value) =
      operator seed time modes F (action value)-action (operator seed time modes F value) := by
  simp only [massOperator,LinearMap.add_apply,LinearMap.id_apply,map_add]
  abel

theorem full_green (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (modes F : Finset IntegerWavevector)
    (zero : 0 ∉ modes) (closed : FiniteModeNegClosed modes) (advector : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality advector) (value : physicalSpace modes) :
    2*pairing modes (physicalOperator modes zero closed nu advector reality value) (operator seed time modes F value) =
      pairing modes value (lyapunov modes zero closed nu advector reality (operator seed time modes F) value) := by
  have generated := whole_green modes zero closed nu advector reality (operator seed time modes F) value
  have same : pairing modes value (operator seed time modes F (physicalOperator modes zero closed nu advector reality value)) =
      pairing modes (physicalOperator modes zero closed nu advector reality value) (operator seed time modes F value) := by
    rw [operator_pairing,operator_pairing,form_symmetric]
  rw [same] at generated
  linarith

open SourceGeneratedNativeResponseDisposition ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem operator_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step) (time : ℝ) (nonnegative : 0 ≤ time)
    (modes F : Finset IntegerWavevector) : operator seed (step.2.clockAdvance+time) modes F = operator step.1 time modes F := by
  have same : form seed (step.2.clockAdvance+time) modes F = form step.1 time modes F := by
    ext x y
    simp only [form_apply,NativeWindowFiniteGramFourier.stress_next seed step generated time nonnegative]
  unfold operator
  rw [same]

end
end SaturationMonoid.NavierStokes.NativeWindowStressOseenTest
