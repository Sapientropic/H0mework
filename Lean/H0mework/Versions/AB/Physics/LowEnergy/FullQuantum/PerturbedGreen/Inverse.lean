import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.PerturbedGreen.Native
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.RealDeriv

/-! A convergent operator correction generates genuine full-source perturbed Dirac solutions. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PerturbedGreen
open FullSpace SpatialGreen ProofFreeRicherAnholonomicSource Filter Topology
noncomputable section

abbrev SpatialOperators := FullMatterL2 →L[ℂ] FullMatterL2

def correction (G V : SpatialOperators) (parameter : ℂ) : SpatialOperators :=
  1+parameter • (G*V)

def response (G V : SpatialOperators) (parameter : ℂ) : SpatialOperators :=
  Ring.inverse (correction G V parameter)*G

theorem correction_isUnit (G V : SpatialOperators) (parameter : ℂ)
    (small : ‖parameter • (G*V)‖<1) : IsUnit (correction G V parameter) := by
  have generated := (Units.oneSub (-(parameter • (G*V))) (by simpa only [norm_neg] using small)).isUnit
  simpa only [Units.val_oneSub,sub_neg_eq_add,correction] using generated

def Equation (point : BasePoint) (energy damping : ℝ) (V : SpatialOperators) (parameter : ℂ)
    (field source : FullMatterL2) : Prop :=
  SpatialGreen.Equation point energy damping field (source-parameter • V field)

theorem equation_iff_correction (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (V : SpatialOperators) (parameter : ℂ) (field source : FullMatterL2) :
    Equation point energy damping V parameter field source ↔
      correction (green point energy damping positive) V parameter field=green point energy damping positive source := by
  rw [Equation,SpatialGreen.equation_iff point energy damping positive]
  rw [map_sub,map_smul]
  change field=green point energy damping positive source-
    parameter • green point energy damping positive (V field) ↔
    field+parameter • green point energy damping positive (V field)=green point energy damping positive source
  exact eq_sub_iff_add_eq

theorem response_solves (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (V : SpatialOperators) (parameter : ℂ)
    (small : ‖parameter • (green point energy damping positive*V)‖<1) (source : FullMatterL2) :
    Equation point energy damping V parameter
      (response (green point energy damping positive) V parameter source) source := by
  apply (equation_iff_correction point energy damping positive V parameter _ source).mpr
  have generated := Ring.mul_inverse_cancel _ (correction_isUnit (green point energy damping positive) V parameter small)
  have applySource := congrArg (fun A : SpatialOperators => A (green point energy damping positive source)) generated
  exact applySource

theorem response_unique (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (V : SpatialOperators) (parameter : ℂ)
    (small : ‖parameter • (green point energy damping positive*V)‖<1)
    (field source : FullMatterL2) (solves : Equation point energy damping V parameter field source) :
    field=response (green point energy damping positive) V parameter source := by
  have generated := (equation_iff_correction point energy damping positive V parameter field source).mp solves
  have inverse := Ring.inverse_mul_cancel _ (correction_isUnit (green point energy damping positive) V parameter small)
  have read := congrArg (fun v : FullMatterL2 =>
    (Ring.inverse (correction (green point energy damping positive) V parameter) : SpatialOperators) v) generated
  have left := congrArg (fun A : SpatialOperators => A field) inverse
  exact left.symm.trans read

theorem response_zero (G V : SpatialOperators) : response G V 0=G := by
  simp [response,correction]

theorem correction_derivative (G V : SpatialOperators) (parameter : ℂ) :
    HasDerivAt (correction G V) (G*V) parameter := by
  convert! (hasDerivAt_const parameter (1 : SpatialOperators)).add
    ((hasDerivAt_id parameter).smul_const (G*V)) using 1
  simp

theorem response_derivative (G V : SpatialOperators) :
    HasDerivAt (response G V) (-(G*V*G)) (0 : ℂ) := by
  have outside : HasFDerivAt (Ring.inverse : SpatialOperators → SpatialOperators)
      (-ContinuousLinearMap.mulLeftRight ℂ SpatialOperators 1 1) (correction G V 0) := by
    simpa only [correction,zero_smul,add_zero,inv_one,Units.val_one] using
      (hasFDerivAt_ringInverse (𝕜 := ℂ) (1 : SpatialOperatorsˣ))
  have derivative := (outside.comp_hasDerivAt 0 (correction_derivative G V 0)).mul_const G
  convert! derivative using 1

theorem response_real_derivative (G V : SpatialOperators) :
    HasDerivAt (fun epsilon : ℝ => response G V (epsilon : ℂ)) (-(G*V*G)) 0 := by
  have complex : HasDerivAt (response G V) (-(G*V*G)) ((0 : ℝ) : ℂ) := by
    convert! response_derivative G V using 1
  have composed := (complex.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt 0
    (Complex.ofRealCLM.hasDerivAt)
  simpa using! composed

theorem small_near_zero (G V : SpatialOperators) :
    ∀ᶠ epsilon : ℝ in 𝓝 0, ‖(epsilon : ℂ) • (G*V)‖<1 := by
  have continuous : Continuous (fun epsilon : ℝ => ‖(epsilon : ℂ) • (G*V)‖) := by fun_prop
  exact continuous.continuousAt.eventually_lt_const (by simp)

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PerturbedGreen
