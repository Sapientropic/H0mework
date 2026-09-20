import H0mework.Physics.LowEnergySpacetime.ScalarEuler
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Source-coordinate spatial modes of the original radial scalar operator. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Spacetime
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineEnrichedProofFreeSource StageNineDynamicBreakingVacuum Stage9C.Material.SpinPair
open StageNineDiracDualFormNativeScalarVariation Stage9C.Dynamics.Homogeneous Response.Radial
open scoped ContDiff
noncomputable section

def spatialPhase (momentum : Fin 3 → ℝ) : BasePoint →L[ℝ] ℝ :=
  ∑ axis : Fin 3, momentum axis • (EuclideanSpace.proj axis.succ : BasePoint →L[ℝ] ℝ)

def radialWave (rate : ℝ) (momentum : Fin 3 → ℝ) (point : BasePoint) : ℝ :=
  Real.sinh (rate*point 0)*Real.cos (spatialPhase momentum point)

theorem spatialPhase_time (momentum : Fin 3 → ℝ) :
    spatialPhase momentum (coordinateDirection 0) = 0 := by
  simp [spatialPhase, Fin.sum_univ_three, coordinateDirection]

theorem spatialPhase_space (momentum : Fin 3 → ℝ) (axis : Fin 3) :
    spatialPhase momentum (coordinateDirection axis.succ) = momentum axis := by
  fin_cases axis <;> simp [spatialPhase, Fin.sum_univ_three, coordinateDirection]

theorem radialWave_smooth (rate : ℝ) (momentum : Fin 3 → ℝ) :
    ContDiff ℝ ∞ (radialWave rate momentum) := by
  unfold radialWave
  fun_prop

theorem radialWave_time (rate : ℝ) (momentum : Fin 3 → ℝ) (point : BasePoint) :
    coordinateDerivative (radialWave rate momentum) 0 point =
      rate*Real.cosh (rate*point 0)*Real.cos (spatialPhase momentum point) := by
  have derivative := ((((EuclideanSpace.proj (0 : LorentzianIndex) : BasePoint →L[ℝ] ℝ).hasFDerivAt (x := point)).const_mul rate).sinh).mul
    (((spatialPhase momentum).hasFDerivAt (x := point)).cos)
  change HasFDerivAt (radialWave rate momentum) _ point at derivative
  unfold coordinateDerivative fieldDirectionalDerivative
  rw [derivative.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, spatialPhase_time]
  simp [coordinateDirection]
  ring

theorem radialWave_space (rate : ℝ) (momentum : Fin 3 → ℝ) (point : BasePoint) (axis : Fin 3) :
    coordinateDerivative (radialWave rate momentum) axis.succ point =
      -momentum axis*Real.sinh (rate*point 0)*Real.sin (spatialPhase momentum point) := by
  have derivative := ((((EuclideanSpace.proj (0 : LorentzianIndex) : BasePoint →L[ℝ] ℝ).hasFDerivAt (x := point)).const_mul rate).sinh).mul
    (((spatialPhase momentum).hasFDerivAt (x := point)).cos)
  change HasFDerivAt (radialWave rate momentum) _ point at derivative
  unfold coordinateDerivative fieldDirectionalDerivative
  rw [derivative.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, spatialPhase_space]
  simp [coordinateDirection]
  ring

theorem radialWave_time_time (rate : ℝ) (momentum : Fin 3 → ℝ) (point : BasePoint) :
    coordinateDerivative (coordinateDerivative (radialWave rate momentum) 0) 0 point =
      rate^2*radialWave rate momentum point := by
  have equal := funext (radialWave_time rate momentum)
  rw [equal]
  have derivative := (((((EuclideanSpace.proj (0 : LorentzianIndex) : BasePoint →L[ℝ] ℝ).hasFDerivAt (x := point)).const_mul rate).cosh).const_mul rate).mul
    (((spatialPhase momentum).hasFDerivAt (x := point)).cos)
  change HasFDerivAt (fun p : BasePoint => rate*Real.cosh (rate*p 0)*Real.cos (spatialPhase momentum p)) _ point at derivative
  unfold coordinateDerivative fieldDirectionalDerivative
  rw [derivative.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, spatialPhase_time]
  simp [coordinateDirection, radialWave]
  ring

theorem radialWave_space_space (rate : ℝ) (momentum : Fin 3 → ℝ) (point : BasePoint) (axis : Fin 3) :
    coordinateDerivative (coordinateDerivative (radialWave rate momentum) axis.succ) axis.succ point =
      -(momentum axis)^2*radialWave rate momentum point := by
  have equal := funext (fun p => radialWave_space rate momentum p axis)
  rw [equal]
  have derivative := (((((EuclideanSpace.proj (0 : LorentzianIndex) : BasePoint →L[ℝ] ℝ).hasFDerivAt (x := point)).const_mul rate).sinh).const_mul (-momentum axis)).mul
    (((spatialPhase momentum).hasFDerivAt (x := point)).sin)
  change HasFDerivAt (fun p : BasePoint => -momentum axis*Real.sinh (rate*p 0)*Real.sin (spatialPhase momentum p)) _ point at derivative
  unfold coordinateDerivative fieldDirectionalDerivative
  rw [derivative.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, spatialPhase_space]
  simp [coordinateDirection, radialWave]
  ring

theorem radialWave_twice (rate : ℝ) (momentum : Fin 3 → ℝ) (mu : LorentzianIndex) :
    Differentiable ℝ (coordinateDerivative (radialWave rate momentum) mu) := by
  refine Fin.cases ?_ (fun axis => ?_) mu
  · rw [funext (radialWave_time rate momentum)]
    fun_prop
  · rw [funext (fun p => radialWave_space rate momentum p axis)]
    fun_prop

theorem radialWave_operator (rate : ℝ) (momentum : Fin 3 → ℝ) (point : BasePoint) :
    radialOperator (radialWave rate momentum) point =
      (rate^2/lapse^2+(∑ axis, (momentum axis)^2)-2)*radialWave rate momentum point := by
  unfold radialOperator
  rw [radialWave_time_time]
  simp_rw [radialWave_space_space]
  rw [← Finset.sum_mul]
  simp only [Finset.sum_neg_distrib]
  ring

end
end SaturationMonoid.PhysicsCore.LowEnergy.Spacetime
