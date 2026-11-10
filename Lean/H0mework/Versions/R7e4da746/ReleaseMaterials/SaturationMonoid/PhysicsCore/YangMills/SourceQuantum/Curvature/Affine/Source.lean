import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.PhysicsCore.YangMills.SourceQuantum.Curvature.Action
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ContDiff
noncomputable section
namespace SaturationMonoid.PhysicsCore.YangMills.NativeCurvature.Affine
open Variation StageNineCompactSupportIntegrationByParts StageNineP286GaugeConnectionVariation
open StageNineHolonomicField Stage9C.Material.SpinPair SU7MotherLieAlgebra
open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
local instance : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance : Fintype P286CoordinateIndex := Fintype.ofFinite P286CoordinateIndex
variable {n : ℕ} (η : Fin n → Variation.Input)

def combine (q : Fin n → ℝ) : Variation.Input where
  toFun x := ∑ i, q i • η i x
  smooth := ContDiff.sum (fun i _ => (η i).smooth.const_smul (q i))
  compactSupport := by
    rw [hasCompactSupport_iff_eventuallyEq]
    have all : ∀ᶠ x in Filter.coclosedCompact BasePoint, ∀ i, η i x = 0 :=
      Filter.eventually_all.mpr (fun i =>
        hasCompactSupport_iff_eventuallyEq.mp (η i).compactSupport)
    filter_upwards [all] with x hx
    simp only [hx, smul_zero, Finset.sum_const_zero, Pi.zero_apply]

def configuration (q : Fin n → ℝ) : StageNineHolonomicConfiguration :=
  varyP286GaugeConnectionCoordinate Stage10.Runtime.configuration (combine η q) 1

theorem connection_readback (q : Fin n → ℝ) (x : BasePoint) :
    holonomicP286GaugeConnectionCoordinate (configuration η q) x =
      holonomicP286GaugeConnectionCoordinate Stage10.Runtime.configuration x +
        ∑ i, q i • η i x := by
  simp only [configuration, holonomicP286GaugeConnectionCoordinate_vary, one_smul]
  rfl

theorem original : configuration η 0 = Stage10.Runtime.configuration := by
  have zero : (combine η (0 : Fin n → ℝ) : BasePoint → P286GaugeOneForm) = 0 := by
    funext x
    simp [combine]
  simp only [configuration, zero]
  change varyP286GaugeConnectionCoordinate Stage10.Runtime.configuration (fun _ => 0) 1 = _
  unfold varyP286GaugeConnectionCoordinate holonomicP286GaugeConnectionCoordinate
  simp only [Pi.zero_apply, smul_zero, add_zero, LinearEquiv.symm_apply_apply]

theorem combine_derivative (q : Fin n → ℝ) (x : BasePoint) (u : LorentzianIndex)
    (v : LorentzianIndex) :
    p286GaugeVariationCoordinateDerivative (combine η q) x u v =
      ∑ i, q i • p286GaugeVariationCoordinateDerivative (η i) x u v := by
  have smooth (i : Fin n) : DifferentiableAt ℝ (fun y => η i y v) x :=
    ((contDiff_pi.mp (η i).smooth v).differentiable (by simp)).differentiableAt
  have generated := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => (smooth i).hasFDerivAt.const_smul (q i))
  unfold p286GaugeVariationCoordinateDerivative fieldDirectionalDerivative
  simp only [combine, Finset.sum_apply, Pi.smul_apply]
  simpa using congrArg
    (fun L : BasePoint →L[ℝ] P286CoordinateCarrier => L (coordinateDirection u)) generated.fderiv
end SaturationMonoid.PhysicsCore.YangMills.NativeCurvature.Affine
