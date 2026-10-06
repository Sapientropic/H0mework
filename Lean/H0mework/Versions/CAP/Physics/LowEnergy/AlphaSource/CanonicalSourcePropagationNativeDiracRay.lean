import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationNativeGaugeRay

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.SourcePropagationNativeActionHessian
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineHolonomicField StageNineGlobalIntegratedAction StageNineDynamicBreakingVacuum
open Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous
open DiracExteriorMatterAction DiracCliffordRepresentation PointwiseDiracSpinConnectionLift
open StageNineDiracMatterCoordinateCalculus StageNineMatterVariation
open SU7MotherGaugeTheory SU7MotherLieAlgebra StageNineP286GaugeConnectionVariationDensity
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open PreparationVacuumMixedFieldReturn
open scoped BigOperators ContDiff Topology Matrix.Norms.Elementwise
attribute [local irreducible] Stage9C.Material.SpinPair.actual
local instance h0meworkNativeDiracRayNormedAddCommGroup : NormedAddCommGroup LorentzianCoframe := Matrix.normedAddCommGroup
local instance h0meworkNativeDiracRaySeminormedAddCommGroup : SeminormedAddCommGroup LorentzianCoframe := Matrix.seminormedAddCommGroup
local instance h0meworkNativeDiracRayNormedSpace : NormedSpace ℝ LorentzianCoframe := Matrix.normedSpace
local instance h0meworkNativeDiracRayModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance h0meworkNativeDiracRayP286Fintype : Fintype P286CoordinateIndex := Fintype.ofFinite _
local instance h0meworkNativeDiracRayMatterFintype : Fintype MatterCoordinateIndex := Fintype.ofFinite _
local instance h0meworkNativeDiracRayTopologicalAddGroup : IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

def diracSpinAction := spinCoordinateBilinear.toContinuousBilinearMap
def diracGaugeAction := matterP286ActionCoordinateBilinear.toContinuousBilinearMap
def diracPrimalBase : MatterCoordinateCarrier := matterCoordinateEquiv (actual.matter 0)
def diracSpinBase (mu : Fin 4) := diracSpinConnectionLift (actual.gravityConnection 0) mu
def diracSpinVariation (jet : NativeFirstJet) (mu : Fin 4) :=
  diracSpinConnectionLift (lorentzInsertionCLM jet.1) mu
def diracGaugeBase (mu : Fin 4) := p286CoordinateEquiv (actual.gaugeConnection 0 mu)
def diracGaugeVariation (jet : NativeFirstJet) (mu : Fin 4) := gaugeCoordinateCLM mu jet.1

def diracCovariantBase (mu : Fin 4) : MatterCoordinateCarrier :=
  fieldDirectionalDerivative (fun x => matterCoordinateEquiv (actual.matter x)) 0 mu +
    diracSpinAction (diracSpinBase mu) diracPrimalBase +
    diracGaugeAction (diracGaugeBase mu) diracPrimalBase

def diracCovariantFirst (jet : NativeFirstJet) (mu : Fin 4) : MatterCoordinateCarrier :=
  rotatedPrimalDerivative jet mu + diracSpinAction (diracSpinBase mu) (primalInsertionCLM jet.1) +
    diracSpinAction (diracSpinVariation jet mu) diracPrimalBase +
    diracGaugeAction (diracGaugeBase mu) (primalInsertionCLM jet.1) +
    diracGaugeAction (diracGaugeVariation jet mu) diracPrimalBase

def diracCovariantSecond (jet : NativeFirstJet) (mu : Fin 4) : MatterCoordinateCarrier :=
  diracSpinAction (diracSpinVariation jet mu) (primalInsertionCLM jet.1) +
    diracGaugeAction (diracGaugeVariation jet mu) (primalInsertionCLM jet.1)

private theorem diracSpinAction_source (M : DiracMatrix) (v : MatterCoordinateCarrier) :
    diracSpinAction M v = matterCoordinateEquiv (diracMatrixMatterAction M (matterCoordinateEquiv.symm v)) := rfl
private theorem diracGaugeAction_source (A : P286CoordinateCarrier) (v : MatterCoordinateCarrier) :
    diracGaugeAction A v = matterCoordinateEquiv (diracExteriorMotherLieAction
      (p286LieBlockEmbed (p286CoordinateEquiv.symm A)) (matterCoordinateEquiv.symm v)) := rfl

theorem diracCovariant_coordinates (jet : NativeFirstJet) (mu : Fin 4) :
    matterCoordinateEquiv (nativeMatterCovariant jet mu) =
      fieldDirectionalDerivative (fun x => matterCoordinateEquiv (actual.matter x)) 0 mu +
      rotatedPrimalDerivative jet mu +
      diracSpinAction (diracSpinBase mu+diracSpinVariation jet mu)
        (diracPrimalBase+primalInsertionCLM jet.1) +
      diracGaugeAction (diracGaugeBase mu+diracGaugeVariation jet mu)
        (diracPrimalBase+primalInsertionCLM jet.1) := by
  have primal : matterCoordinateEquiv (nativeMatterValue jet)=diracPrimalBase+primalInsertionCLM jet.1 := by
    exact matterCoordinateEquiv.map_add _ _
  have spin : diracSpinConnectionLift (actual.gravityConnection 0+lorentzInsertionCLM jet.1) mu =
      diracSpinBase mu+diracSpinVariation jet mu := (diracSpinConnectionLiftLinear mu).map_add _ _
  have gauge : p286CoordinateEquiv.symm (diracGaugeBase mu+diracGaugeVariation jet mu) =
      actual.gaugeConnection 0 mu+p286CoordinateEquiv.symm (fieldGauge jet.1 mu) := by
    simp only [diracGaugeBase, diracGaugeVariation, map_add, LinearEquiv.symm_apply_apply]
    rfl
  rw [diracSpinAction_source, diracGaugeAction_source, ←primal, gauge]
  simp only [LinearEquiv.symm_apply_apply]
  unfold nativeMatterCovariant
  rw [map_add, map_add, LinearEquiv.apply_symm_apply, spin]

private theorem diracBilinear_ray {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (B : V →L[ℝ] W →L[ℝ] W)
    (a da : V) (v dv : W) (r : ℝ) :
    B (a+r • da) (v+r • dv) = B a v+r • (B a dv+B da v)+r^2 • B da dv := by
  simp only [map_add, map_smul, add_apply, smul_apply, smul_smul, smul_add, pow_two]
  module

theorem rotatedPrimalDerivative_scale (jet : NativeFirstJet) (r : ℝ) (mu : Fin 4) :
    rotatedPrimalDerivative (r • jet) mu = r • rotatedPrimalDerivative jet mu := by
  unfold rotatedPrimalDerivative
  simp only [Prod.smul_fst, Prod.smul_snd, Finset.smul_sum]
  apply Finset.sum_congr rfl; intro spin _
  apply Finset.sum_congr rfl; intro color _
  have coefficient (f : Field289) : fieldPrimalComplex (r • f) spin color =
      (r:ℂ)*fieldPrimalComplex f spin color := by
    simp only [fieldPrimalComplex, fieldPrimal, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
    ring
  rw [coefficient]
  change (((if mu=0 then phaseComponentVelocity spin else 0)*((r:ℂ)*fieldPrimalComplex jet.1 spin color)+
    fieldPrimalComplex (r • jet.2 mu) spin color) • matterCoordinateEquiv (PreparationVacuumNativeSourceRestriction.sourceTripletLeg spin color)) =
    r • (((if mu=0 then phaseComponentVelocity spin else 0)*fieldPrimalComplex jet.1 spin color+
      fieldPrimalComplex (jet.2 mu) spin color) • matterCoordinateEquiv (PreparationVacuumNativeSourceRestriction.sourceTripletLeg spin color))
  rw [coefficient]
  have scalar : (if mu=0 then phaseComponentVelocity spin else 0)*((r:ℂ)*fieldPrimalComplex jet.1 spin color)+
      (r:ℂ)*fieldPrimalComplex (jet.2 mu) spin color =
      (r:ℂ)*((if mu=0 then phaseComponentVelocity spin else 0)*fieldPrimalComplex jet.1 spin color+
        fieldPrimalComplex (jet.2 mu) spin color) := by ring
  rw [scalar, mul_smul]
  rfl

theorem diracCovariant_ray (jet : NativeFirstJet) (r : ℝ) (mu : Fin 4) :
    matterCoordinateEquiv (nativeMatterCovariant (r • jet) mu) = diracCovariantBase mu +
      r • diracCovariantFirst jet mu + r^2 • diracCovariantSecond jet mu := by
  rw [diracCovariant_coordinates, rotatedPrimalDerivative_scale]
  simp only [diracSpinVariation, diracGaugeVariation, Prod.smul_fst, map_smul]
  have scale : diracSpinConnectionLift (r • lorentzInsertionCLM jet.1) mu =
      r • diracSpinVariation jet mu := (diracSpinConnectionLiftLinear mu).map_smul r _
  rw [scale, diracBilinear_ray, diracBilinear_ray]
  unfold diracCovariantBase diracCovariantFirst diracCovariantSecond diracSpinVariation diracGaugeVariation
  module

def diracAdjugateCoefficient (h : LorentzianCoframe) (degree : Fin 4) (i j : Fin 4) : ℝ :=
  match degree.val, i.val, j.val with
  | 0, 0, 0 => 1
  | 0, 1, 1 => lapse
  | 0, 2, 2 => lapse
  | 0, 3, 3 => lapse
  | 1, 0, 0 => h 1 1 + h 2 2 + h 3 3
  | 1, 0, 1 => -h 0 1
  | 1, 0, 2 => -h 0 2
  | 1, 0, 3 => -h 0 3
  | 1, 1, 0 => -h 1 0
  | 1, 1, 1 => h 0 0 + lapse * h 2 2 + lapse * h 3 3
  | 1, 1, 2 => -lapse * h 1 2
  | 1, 1, 3 => -lapse * h 1 3
  | 1, 2, 0 => -h 2 0
  | 1, 2, 1 => -lapse * h 2 1
  | 1, 2, 2 => h 0 0 + lapse * h 1 1 + lapse * h 3 3
  | 1, 2, 3 => -lapse * h 2 3
  | 1, 3, 0 => -h 3 0
  | 1, 3, 1 => -lapse * h 3 1
  | 1, 3, 2 => -lapse * h 3 2
  | 1, 3, 3 => h 0 0 + lapse * h 1 1 + lapse * h 2 2
  | 2, 0, 0 => h 1 1 * h 2 2 + h 1 1 * h 3 3 - h 1 2 * h 2 1 - h 1 3 * h 3 1 + h 2 2 * h 3 3 - h 2 3 * h 3 2
  | 2, 0, 1 => -h 0 1 * h 2 2 - h 0 1 * h 3 3 + h 0 2 * h 2 1 + h 0 3 * h 3 1
  | 2, 0, 2 => h 0 1 * h 1 2 - h 0 2 * h 1 1 - h 0 2 * h 3 3 + h 0 3 * h 3 2
  | 2, 0, 3 => h 0 1 * h 1 3 + h 0 2 * h 2 3 - h 0 3 * h 1 1 - h 0 3 * h 2 2
  | 2, 1, 0 => -h 1 0 * h 2 2 - h 1 0 * h 3 3 + h 1 2 * h 2 0 + h 1 3 * h 3 0
  | 2, 1, 1 => h 0 0 * h 2 2 + h 0 0 * h 3 3 - h 0 2 * h 2 0 - h 0 3 * h 3 0 + lapse * h 2 2 * h 3 3 - lapse * h 2 3 * h 3 2
  | 2, 1, 2 => -h 0 0 * h 1 2 + h 0 2 * h 1 0 - lapse * h 1 2 * h 3 3 + lapse * h 1 3 * h 3 2
  | 2, 1, 3 => -h 0 0 * h 1 3 + h 0 3 * h 1 0 + lapse * h 1 2 * h 2 3 - lapse * h 1 3 * h 2 2
  | 2, 2, 0 => h 1 0 * h 2 1 - h 1 1 * h 2 0 - h 2 0 * h 3 3 + h 2 3 * h 3 0
  | 2, 2, 1 => -h 0 0 * h 2 1 + h 0 1 * h 2 0 - lapse * h 2 1 * h 3 3 + lapse * h 2 3 * h 3 1
  | 2, 2, 2 => h 0 0 * h 1 1 + h 0 0 * h 3 3 - h 0 1 * h 1 0 - h 0 3 * h 3 0 + lapse * h 1 1 * h 3 3 - lapse * h 1 3 * h 3 1
  | 2, 2, 3 => -h 0 0 * h 2 3 + h 0 3 * h 2 0 - lapse * h 1 1 * h 2 3 + lapse * h 1 3 * h 2 1
  | 2, 3, 0 => h 1 0 * h 3 1 - h 1 1 * h 3 0 + h 2 0 * h 3 2 - h 2 2 * h 3 0
  | 2, 3, 1 => -h 0 0 * h 3 1 + h 0 1 * h 3 0 + lapse * h 2 1 * h 3 2 - lapse * h 2 2 * h 3 1
  | 2, 3, 2 => -h 0 0 * h 3 2 + h 0 2 * h 3 0 - lapse * h 1 1 * h 3 2 + lapse * h 1 2 * h 3 1
  | 2, 3, 3 => h 0 0 * h 1 1 + h 0 0 * h 2 2 - h 0 1 * h 1 0 - h 0 2 * h 2 0 + lapse * h 1 1 * h 2 2 - lapse * h 1 2 * h 2 1
  | 3, 0, 0 => h 1 1 * h 2 2 * h 3 3 - h 1 1 * h 2 3 * h 3 2 - h 1 2 * h 2 1 * h 3 3 + h 1 2 * h 2 3 * h 3 1 + h 1 3 * h 2 1 * h 3 2 - h 1 3 * h 2 2 * h 3 1
  | 3, 0, 1 => -h 0 1 * h 2 2 * h 3 3 + h 0 1 * h 2 3 * h 3 2 + h 0 2 * h 2 1 * h 3 3 - h 0 2 * h 2 3 * h 3 1 - h 0 3 * h 2 1 * h 3 2 + h 0 3 * h 2 2 * h 3 1
  | 3, 0, 2 => h 0 1 * h 1 2 * h 3 3 - h 0 1 * h 1 3 * h 3 2 - h 0 2 * h 1 1 * h 3 3 + h 0 2 * h 1 3 * h 3 1 + h 0 3 * h 1 1 * h 3 2 - h 0 3 * h 1 2 * h 3 1
  | 3, 0, 3 => -h 0 1 * h 1 2 * h 2 3 + h 0 1 * h 1 3 * h 2 2 + h 0 2 * h 1 1 * h 2 3 - h 0 2 * h 1 3 * h 2 1 - h 0 3 * h 1 1 * h 2 2 + h 0 3 * h 1 2 * h 2 1
  | 3, 1, 0 => -h 1 0 * h 2 2 * h 3 3 + h 1 0 * h 2 3 * h 3 2 + h 1 2 * h 2 0 * h 3 3 - h 1 2 * h 2 3 * h 3 0 - h 1 3 * h 2 0 * h 3 2 + h 1 3 * h 2 2 * h 3 0
  | 3, 1, 1 => h 0 0 * h 2 2 * h 3 3 - h 0 0 * h 2 3 * h 3 2 - h 0 2 * h 2 0 * h 3 3 + h 0 2 * h 2 3 * h 3 0 + h 0 3 * h 2 0 * h 3 2 - h 0 3 * h 2 2 * h 3 0
  | 3, 1, 2 => -h 0 0 * h 1 2 * h 3 3 + h 0 0 * h 1 3 * h 3 2 + h 0 2 * h 1 0 * h 3 3 - h 0 2 * h 1 3 * h 3 0 - h 0 3 * h 1 0 * h 3 2 + h 0 3 * h 1 2 * h 3 0
  | 3, 1, 3 => h 0 0 * h 1 2 * h 2 3 - h 0 0 * h 1 3 * h 2 2 - h 0 2 * h 1 0 * h 2 3 + h 0 2 * h 1 3 * h 2 0 + h 0 3 * h 1 0 * h 2 2 - h 0 3 * h 1 2 * h 2 0
  | 3, 2, 0 => h 1 0 * h 2 1 * h 3 3 - h 1 0 * h 2 3 * h 3 1 - h 1 1 * h 2 0 * h 3 3 + h 1 1 * h 2 3 * h 3 0 + h 1 3 * h 2 0 * h 3 1 - h 1 3 * h 2 1 * h 3 0
  | 3, 2, 1 => -h 0 0 * h 2 1 * h 3 3 + h 0 0 * h 2 3 * h 3 1 + h 0 1 * h 2 0 * h 3 3 - h 0 1 * h 2 3 * h 3 0 - h 0 3 * h 2 0 * h 3 1 + h 0 3 * h 2 1 * h 3 0
  | 3, 2, 2 => h 0 0 * h 1 1 * h 3 3 - h 0 0 * h 1 3 * h 3 1 - h 0 1 * h 1 0 * h 3 3 + h 0 1 * h 1 3 * h 3 0 + h 0 3 * h 1 0 * h 3 1 - h 0 3 * h 1 1 * h 3 0
  | 3, 2, 3 => -h 0 0 * h 1 1 * h 2 3 + h 0 0 * h 1 3 * h 2 1 + h 0 1 * h 1 0 * h 2 3 - h 0 1 * h 1 3 * h 2 0 - h 0 3 * h 1 0 * h 2 1 + h 0 3 * h 1 1 * h 2 0
  | 3, 3, 0 => -h 1 0 * h 2 1 * h 3 2 + h 1 0 * h 2 2 * h 3 1 + h 1 1 * h 2 0 * h 3 2 - h 1 1 * h 2 2 * h 3 0 - h 1 2 * h 2 0 * h 3 1 + h 1 2 * h 2 1 * h 3 0
  | 3, 3, 1 => h 0 0 * h 2 1 * h 3 2 - h 0 0 * h 2 2 * h 3 1 - h 0 1 * h 2 0 * h 3 2 + h 0 1 * h 2 2 * h 3 0 + h 0 2 * h 2 0 * h 3 1 - h 0 2 * h 2 1 * h 3 0
  | 3, 3, 2 => -h 0 0 * h 1 1 * h 3 2 + h 0 0 * h 1 2 * h 3 1 + h 0 1 * h 1 0 * h 3 2 - h 0 1 * h 1 2 * h 3 0 - h 0 2 * h 1 0 * h 3 1 + h 0 2 * h 1 1 * h 3 0
  | 3, 3, 3 => h 0 0 * h 1 1 * h 2 2 - h 0 0 * h 1 2 * h 2 1 - h 0 1 * h 1 0 * h 2 2 + h 0 1 * h 1 2 * h 2 0 + h 0 2 * h 1 0 * h 2 1 - h 0 2 * h 1 1 * h 2 0
  | _, _, _ => 0

theorem diracAdjugate_ray (h : LorentzianCoframe) (r : ℝ) (i j : Fin 4) :
    Matrix.adjugate (homogeneousCoframe lapse+r • h) i j =
      diracAdjugateCoefficient h 0 i j+r*diracAdjugateCoefficient h 1 i j+
        r^2*diracAdjugateCoefficient h 2 i j+r^3*diracAdjugateCoefficient h 3 i j := by
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_three, Matrix.submatrix_apply,
      homogeneousCoframe, Matrix.diagonal_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, diracAdjugateCoefficient, Fin.succAbove]
  all_goals ring

def diracInternalLinear (a : Fin 4) : MatterCoordinateCarrier →ₗ[ℝ] MatterCoordinateCarrier :=
  Complex.I • spinCoordinateBilinear (diracGamma a)

def diracDualVariationLinear (f : Field289) : MatterCoordinateCarrier →ₗ[ℝ] ℂ :=
  ∑ spin : Fin 4, ∑ color : Fin 3,
    dualCoefficientCLM spin color f • (matterReadCLM spin color).toLinearMap

def diracDualPairLinear (jet : NativeFirstJet) : MatterCoordinateCarrier →ₗ[ℝ] ℂ :=
  originalDualCLM.toLinearMap+diracDualVariationLinear jet.1

theorem diracDualVariation_value (f : Field289) (v : MatterCoordinateCarrier) :
    diracDualVariationLinear f v = ∑ spin : Fin 4, ∑ color : Fin 3,
      dualCoefficientCLM spin color f*matterReadCLM spin color v := by
  simp only [diracDualVariationLinear, LinearMap.sum_apply, LinearMap.smul_apply,
    ContinuousLinearMap.coe_coe, smul_eq_mul]

theorem diracDualVariation_scale (f : Field289) (r : ℝ) :
    diracDualVariationLinear (r • f) = r • diracDualVariationLinear f := by
  apply LinearMap.ext; intro v
  simp only [diracDualVariation_value, map_smul, LinearMap.smul_apply,
    RCLike.real_smul_eq_coe_mul, Finset.mul_sum, mul_assoc]

private theorem diracGamma_weighted (c : ℝ) (M : DiracMatrix) (v : MatterCoordinateCarrier) :
    Complex.I • spinCoordinateBilinear ((c:ℂ) • M) v =
      c • (Complex.I • spinCoordinateBilinear M v) := by
  have scalar : (c:ℂ) • M = c • M := (RCLike.real_smul_eq_coe_smul (K:=ℂ) c M).symm
  rw [scalar, map_smul, LinearMap.smul_apply]
  exact smul_comm _ _ _

def diracKineticEntry (jet : NativeFirstJet) (mu a : Fin 4) : ℝ :=
  (diracDualPairLinear jet (diracInternalLinear a
    (matterCoordinateEquiv (nativeMatterCovariant jet mu)))).re

theorem diracKineticPair_entries (jet : NativeFirstJet) :
    (nativeKineticPair jet).re = ∑ mu : Fin 4, ∑ a : Fin 4,
      (nativeJetPoint jet).coframe⁻¹ mu a * diracKineticEntry jet mu a := by
  have pair : nativeKineticPair jet = diracDualPairLinear jet (nativeKineticCoordinates jet) := by
    simp only [nativeKineticPair, diracDualPairLinear, LinearMap.add_apply, diracDualVariation_value,
      ContinuousLinearMap.coe_coe]
  have vector : nativeKineticCoordinates jet = ∑ mu : Fin 4, ∑ a : Fin 4,
      (nativeJetPoint jet).coframe⁻¹ mu a •
        diracInternalLinear a (matterCoordinateEquiv (nativeMatterCovariant jet mu)) := by
    unfold nativeKineticCoordinates inverseCoframeDiracGamma diracInternalLinear
    simp only [map_sum, LinearMap.sum_apply, LinearMap.smul_apply,
      ContinuousLinearMap.coe_coe, Finset.smul_sum]
    apply Finset.sum_congr rfl; intro mu _
    apply Finset.sum_congr rfl; intro a _
    exact diracGamma_weighted _ _ _
  rw [pair, vector]
  simp only [map_sum, map_smul, Complex.re_sum, Complex.smul_re, smul_eq_mul,
    diracKineticEntry]

def nativeDiracDensity (jet : NativeFirstJet) : ℝ :=
  StageNineDiracKineticLocalSpinDensity.generatedDensitizedContinuumMatterKineticDensity
    positiveSmoothUnifiedSource 0 0 (nativeJetPoint jet)

theorem nativeDiracDensity_original (jet : NativeFirstJet) :
    nativeDiracDensity jet = generatedVolumeDensity (nativeJetPoint jet)*(nativeKineticPair jet).re := by
  unfold nativeDiracDensity StageNineDiracKineticLocalSpinDensity.generatedDensitizedContinuumMatterKineticDensity
  rw [matterDualFrameRelative_zeroChart, nativeKineticPair_original]

private theorem determinant_inverse_adjugate (e : LorentzianCoframe) (hne : e.det ≠ 0) (mu a : Fin 4) :
    e.det*e⁻¹ mu a = Matrix.adjugate e mu a := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv]
  simp only [Matrix.smul_apply, smul_eq_mul]
  field_simp


theorem nativeDiracDensity_adjugate (jet : NativeFirstJet) (positive : 0 < (nativeJetPoint jet).coframe.det) :
    nativeDiracDensity jet = ∑ mu : Fin 4, ∑ a : Fin 4,
      Matrix.adjugate (nativeJetPoint jet).coframe mu a*diracKineticEntry jet mu a := by
  rw [nativeDiracDensity_original, diracKineticPair_entries]
  unfold generatedVolumeDensity
  rw [abs_of_pos positive, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro mu _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _
  rw [←mul_assoc, determinant_inverse_adjugate _ (ne_of_gt positive)]


def diracPairCoefficient (jet : NativeFirstJet) (mu a : Fin 4) (degree : Fin 4) : ℂ :=
  let D0 := originalDualCLM.toLinearMap.comp (diracInternalLinear a)
  let D1 := (diracDualVariationLinear jet.1).comp (diracInternalLinear a)
  match degree.val with
  | 0 => D0 (diracCovariantBase mu)
  | 1 => D0 (diracCovariantFirst jet mu)+D1 (diracCovariantBase mu)
  | 2 => D0 (diracCovariantSecond jet mu)+D1 (diracCovariantFirst jet mu)
  | _ => D1 (diracCovariantSecond jet mu)

theorem diracKineticEntry_ray (jet : NativeFirstJet) (r : ℝ) (mu a : Fin 4) :
    diracKineticEntry (r • jet) mu a = (diracPairCoefficient jet mu a 0).re+
      r*(diracPairCoefficient jet mu a 1).re+r^2*(diracPairCoefficient jet mu a 2).re+
        r^3*(diracPairCoefficient jet mu a 3).re := by
  unfold diracKineticEntry diracDualPairLinear
  rw [diracCovariant_ray]
  simp only [Prod.smul_fst, diracDualVariation_scale, LinearMap.add_apply, LinearMap.smul_apply,
    map_add, map_smul, Complex.add_re, Complex.smul_re, smul_eq_mul]
  simp only [diracPairCoefficient, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, LinearMap.comp_apply,
    Complex.add_re, smul_eq_mul]
  norm_num only [Fin.coe_ofNat_eq_mod]
  simp only [Complex.add_re]
  ring

def diracRayCoefficient (jet : NativeFirstJet) : Fin 7 → ℝ := fun degree =>
  ∑ mu : Fin 4, ∑ a : Fin 4, ∑ d : Fin 4, ∑ q : Fin 4,
    if d.val+q.val=degree.val then
      diracAdjugateCoefficient (fieldCoframe jet.1) d mu a*(diracPairCoefficient jet mu a q).re else 0

def nativeDiracQuadratic (jet : NativeFirstJet) : ℝ :=
  ∑ mu : Fin 4, ∑ a : Fin 4, (
    diracAdjugateCoefficient (fieldCoframe jet.1) 0 mu a*(diracPairCoefficient jet mu a 2).re+
    diracAdjugateCoefficient (fieldCoframe jet.1) 1 mu a*(diracPairCoefficient jet mu a 1).re+
    diracAdjugateCoefficient (fieldCoframe jet.1) 2 mu a*(diracPairCoefficient jet mu a 0).re)

theorem diracRayCoefficient_second (jet : NativeFirstJet) : diracRayCoefficient jet 2=nativeDiracQuadratic jet := by
  unfold diracRayCoefficient nativeDiracQuadratic
  apply Finset.sum_congr rfl; intro mu _
  apply Finset.sum_congr rfl; intro a _
  simp [Fin.sum_univ_four]

def diracRayPolynomial (jet : NativeFirstJet) (r : ℝ) : ℝ :=
  ∑ k : Fin 7, r^k.val*diracRayCoefficient jet k

theorem diracRayPolynomial_product (jet : NativeFirstJet) (r : ℝ) :
    diracRayPolynomial jet r = ∑ mu : Fin 4, ∑ a : Fin 4,
      (∑ d : Fin 4, r^d.val*diracAdjugateCoefficient (fieldCoframe jet.1) d mu a)*
      (∑ q : Fin 4, r^q.val*(diracPairCoefficient jet mu a q).re) := by
  have convolution (A B : Fin 4 → ℝ) :
      (∑ k : Fin 7, r^k.val*(∑ d : Fin 4, ∑ q : Fin 4,
        if d.val+q.val=k.val then A d*B q else 0)) =
      (∑ d : Fin 4, r^d.val*A d)*(∑ q : Fin 4, r^q.val*B q) := by
    rw [Finset.sum_mul]; simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro d _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro q _
    have lt : d.val+q.val<7 := by omega
    rw [Finset.sum_eq_single (⟨d.val+q.val,lt⟩ : Fin 7)]
    · simp only [Fin.val_mk, if_true, pow_add]; ring
    · intro k _ hk
      have ne : d.val+q.val≠k.val := by intro h; apply hk; exact Fin.ext h.symm
      simp [ne]
    · simp
  unfold diracRayPolynomial diracRayCoefficient
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro mu _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  simpa only [Finset.mul_sum] using
    convolution (diracAdjugateCoefficient (fieldCoframe jet.1) · mu a)
      (fun q => (diracPairCoefficient jet mu a q).re)

open Filter in
 theorem nativeDiracDensity_ray_polynomial (jet : NativeFirstJet) :
    (fun r : ℝ => nativeDiracDensity (r • jet)) =ᶠ[𝓝 0] diracRayPolynomial jet := by
  let h := fieldCoframe jet.1
  have atZero : 0 < Matrix.det (actual.coframe 0) := by
    rw [actual_coframe, homogeneousCoframe_det]; exact lapse_pos
  have positive : ∀ᶠ r in 𝓝 (0:ℝ), 0 < Matrix.det (actual.coframe 0+r • h) :=
    ((StageNineCoframeVariation.coframe_det_contDiff.continuous.continuousAt).comp
      (coframeRay_derivative (actual.coframe 0) h 0).continuousAt).eventually_const_lt
        (by simpa using atZero)
  filter_upwards [positive] with r hr
  have coframe : (nativeJetPoint (r • jet)).coframe=actual.coframe 0+r • h := by
    simp only [nativeJetPoint, Prod.smul_fst, fieldCoframe_scale]; rfl
  rw [nativeDiracDensity_adjugate _ (by simpa only [coframe] using hr), diracRayPolynomial_product]
  apply Finset.sum_congr rfl; intro mu _
  apply Finset.sum_congr rfl; intro a _
  rw [coframe, actual_coframe, diracAdjugate_ray, diracKineticEntry_ray]
  simp only [Fin.sum_univ_four, Fin.isValue, pow_zero, pow_one]
  norm_num only [Fin.coe_ofNat_eq_mod]
  ring


private theorem diracMonomial_second (n : ℕ) (c : ℝ) :
    HasDerivAt (deriv (fun r : ℝ => r^n*c))
      ((n:ℝ)*(n-1:ℕ)*(0:ℝ)^(n-1-1)*c) 0 := by
  have first : deriv (fun r : ℝ => r^n*c) = fun r : ℝ => (n:ℝ)*r^(n-1)*c := by
    funext r
    simpa only [id_eq, Pi.pow_apply, mul_one] using (((hasDerivAt_id r).pow n).mul_const c).deriv
  rw [first]
  simpa only [id_eq, Pi.pow_apply, mul_one, mul_assoc] using
    (((hasDerivAt_id (0:ℝ)).pow (n-1)).const_mul (n:ℝ)).mul_const c

open Filter in
 theorem diracRayPolynomial_second (jet : NativeFirstJet) :
    HasDerivAt (deriv (diracRayPolynomial jet)) (2*nativeDiracQuadratic jet) 0 := by
  have second (k : Fin 7) :
      HasDerivAt (deriv (fun r : ℝ => r^k.val*diracRayCoefficient jet k))
        (if k=2 then 2*diracRayCoefficient jet 2 else 0) 0 := by
    convert! diracMonomial_second k.val (diracRayCoefficient jet k) using 1
    fin_cases k <;> simp only [Fin.reduceEq, Fin.reduceFinMk, if_true, if_false] <;> norm_num
  have near (k : Fin 7) : ∀ᶠ r in 𝓝 (0:ℝ),
      DifferentiableAt ℝ (fun t : ℝ => t^k.val*diracRayCoefficient jet k) r :=
    Filter.Eventually.of_forall fun r =>
      (((hasDerivAt_id r).pow k.val).mul_const (diracRayCoefficient jet k)).differentiableAt
  have h := finiteSum_second (fun k : Fin 7 => fun r : ℝ => r^k.val*diracRayCoefficient jet k)
    (fun k => if k=2 then 2*diracRayCoefficient jet 2 else 0) second near
  change HasDerivAt (deriv (fun r : ℝ => ∑ k : Fin 7, r^k.val*diracRayCoefficient jet k))
    (2*nativeDiracQuadratic jet) 0
  simpa only [Finset.sum_ite_eq', Finset.mem_univ, if_true,
    diracRayCoefficient_second] using h

open Filter in
 theorem nativeDiracDensity_ray_second (jet : NativeFirstJet) :
    HasDerivAt (deriv (fun r : ℝ => nativeDiracDensity (r • jet)))
      (2*nativeDiracQuadratic jet) 0 :=
  (diracRayPolynomial_second jet).congr_of_eventuallyEq
    (nativeDiracDensity_ray_polynomial jet).deriv

def nativeDiracHessian : NativeFirstJet →L[ℝ] NativeFirstJet →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ nativeDiracDensity) 0

theorem nativeDiracHessian_quadratic (jet : NativeFirstJet) :
    nativeDiracHessian jet jet = 2*nativeDiracQuadratic jet :=
  sourceRay_second_hessian nativeDiracDensity nativeDiracKinetic_smooth jet
    (2*nativeDiracQuadratic jet) (nativeDiracDensity_ray_second jet)

theorem nativeDiracHessian_symmetric (u v : NativeFirstJet) :
    nativeDiracHessian u v = nativeDiracHessian v u := by
  have order : (2 : ℕ∞ω) ≤ ∞ := by
    change ((2:ℕ∞):ℕ∞ω) ≤ ((⊤:ℕ∞):ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top
  exact (nativeDiracKinetic_smooth.isSymmSndFDerivAt (by simpa using order)).eq u v

theorem nativeDiracHessian_polarization (u v : NativeFirstJet) :
    nativeDiracHessian u v = nativeDiracQuadratic (u+v)-nativeDiracQuadratic u-nativeDiracQuadratic v := by
  have all := nativeDiracHessian_quadratic (u+v)
  simp only [map_add, add_apply] at all
  rw [nativeDiracHessian_quadratic u, nativeDiracHessian_quadratic v,
    nativeDiracHessian_symmetric v u] at all
  linarith

end LowEnergy.SourcePropagationNativeActionHessian
