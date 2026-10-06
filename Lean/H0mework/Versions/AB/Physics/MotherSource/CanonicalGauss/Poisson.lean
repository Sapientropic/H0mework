import H0mework.Versions.AB.Physics.MotherSource.CanonicalGauss.Euler

/-! The central hypercharge projection generates the Poisson operator with its original coupling and lapse. -/

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000
namespace SaturationMonoid.PhysicsCore.Stage10.CanonicalGauss
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineGlobalIntegratedAction
open SU7MotherLieAlgebra SU7MotherGaugeTheory
open StageNineP286GaugeConnectionVariation StageNineP286GaugeAuxiliaryVariation
open StageNineCoframeLocalDifferentiability StageNineCanonicalCauchyState
open Stage9C.Material.SpinPair DiracExteriorMatterAction
open TemporalGauge
noncomputable section

local instance : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance : Fintype P286CoordinateIndex := Fintype.ofFinite _
local instance : IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

def abelianPotential (potential : BasePoint → ℝ) : Potential :=
  fun point => potential point • HyperchargeResponse.chargeDirection

def spatialLaplacian (potential : BasePoint → ℝ) (point : BasePoint) : ℝ :=
  ∑ axis : Fin 3, fieldDirectionalDerivative
    (fun p => fieldDirectionalDerivative potential p axis.succ) point axis.succ

def ScalarRegular (potential : BasePoint → ℝ) : Prop :=
  Differentiable ℝ potential ∧ ∀ axis : Fin 3,
    Differentiable ℝ (fun p => fieldDirectionalDerivative potential p axis.succ)

theorem abelian_differentiable (potential : BasePoint → ℝ) (regular : Differentiable ℝ potential) :
    PotentialDifferentiable (abelianPotential potential) := by
  unfold PotentialDifferentiable abelianPotential
  simp only [map_smul]
  exact regular.smul_const _

theorem derivative_abelian (potential : BasePoint → ℝ) (point : BasePoint)
    (regular : DifferentiableAt ℝ potential point) (direction : LorentzianIndex) :
    derivative (abelianPotential potential) point direction =
      fieldDirectionalDerivative potential point direction • HyperchargeResponse.chargeDirection := by
  unfold derivative abelianPotential
  simp only [map_smul]
  unfold fieldDirectionalDerivative
  rw [fderiv_smul_const regular]
  simp

theorem central_left (amount : ℝ) (data : P286LieBlockData) :
    p286LieBracket (amount • HyperchargeResponse.chargeDirection) data = 0 := by
  simp [HyperchargeResponse.chargeDirection, p286LieBracket, suLieBracket]

theorem central_right (amount : ℝ) (data : P286LieBlockData) :
    p286LieBracket data (amount • HyperchargeResponse.chargeDirection) = 0 := by
  simp [HyperchargeResponse.chargeDirection, p286LieBracket, suLieBracket]

theorem electric_abelian (potential : BasePoint → ℝ) (point : BasePoint)
    (regular : DifferentiableAt ℝ potential point) (axis : Fin 3) :
    electric (abelianPotential potential) point axis =
      -fieldDirectionalDerivative potential point axis.succ • HyperchargeResponse.chargeDirection := by
  rw [electric, derivative_abelian potential point regular]
  simp only [abelianPotential, central_left, add_zero]
  module

theorem abelian_electric_regular (potential : BasePoint → ℝ) (regular : ScalarRegular potential)
    (point : BasePoint) : ElectricDifferentiableAt (abelianPotential potential) point := by
  intro axis
  simp only [electric_abelian potential _ (regular.1 _), map_smul]
  exact ((regular.2 axis point).neg).smul_const _

theorem abelian_divergence (potential : BasePoint → ℝ) (regular : ScalarRegular potential)
    (point : BasePoint) :
    divergence (abelianPotential potential) point =
      -spatialLaplacian potential point • HyperchargeResponse.chargeDirection := by
  unfold divergence
  have fieldEq (axis : Fin 3) : (fun p => electric (abelianPotential potential) p axis) =
      abelianPotential (fun p => -fieldDirectionalDerivative potential p axis.succ) := by
    funext p
    exact electric_abelian potential p (regular.1 p) axis
  have term (axis : Fin 3) :
      derivative (fun p => electric (abelianPotential potential) p axis) point axis.succ +
        p286LieBracket (gaugeScale • sourceColorP286Generator axis)
          (electric (abelianPotential potential) point axis) =
      (-fieldDirectionalDerivative (fun p => fieldDirectionalDerivative potential p axis.succ)
        point axis.succ) • HyperchargeResponse.chargeDirection := by
    rw [fieldEq, derivative_abelian (fun p => -fieldDirectionalDerivative potential p axis.succ)
      point ((regular.2 axis point).neg),
      electric_abelian potential point (regular.1 point), central_right, add_zero]
    unfold fieldDirectionalDerivative
    rw [fderiv_fun_neg]
    rfl
  simp only [term]
  unfold spatialLaplacian
  rw [← Finset.sum_smul, ← Finset.sum_neg_distrib]

theorem charge_pairing :
    p286LiePairing HyperchargeResponse.chargeDirection HyperchargeResponse.chargeDirection = 1 := by
  norm_num [HyperchargeResponse.chargeDirection, p286LiePairing,
    specialUnitaryLiePairing, hyperchargeLiePairing, hyperchargeGenerator]

theorem poisson_gauss (potential : BasePoint → ℝ) (regular : ScalarRegular potential)
    (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (space : StageNineSpatialPoint) :
    p286CoordinateLiePairing (p286CoordinateEquiv HyperchargeResponse.chargeDirection)
      (StageNineFormNativeP286GaugeGeometricFirstVariation.holonomicFormNativeP286GaugeEulerThreeForm
        Stage10.Runtime.source 0 (withMatter (abelianPotential potential) matter dual)
        (canonicalCauchySlicePoint 0 space) 3) =
      -(2*lapse)*spatialLaplacian potential (canonicalCauchySlicePoint 0 space) +
        (dual (canonicalCauchySlicePoint 0 space)
          (Stage9DEF.Compatibility.currentAction 0 HyperchargeResponse.chargeDirection
            (matter (canonicalCauchySlicePoint 0 space)))).re := by
  rw [gauss_projection _ (abelian_differentiable potential regular.1) _ _ _
    (abelian_electric_regular potential regular _) _, abelian_divergence potential regular]
  rw [p286LiePairing_smul_right, charge_pairing]
  ring

end
end SaturationMonoid.PhysicsCore.Stage10.CanonicalGauss
