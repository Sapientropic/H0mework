import H0mework.Versions.R2.Physics.RootRuntime.RecoveryConsumer
import H0mework.Versions.R2.Physics.QuantumCompatibility.Stress
import Mathlib.Analysis.Calculus.FDeriv.Mul

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedAction
open SaturationMonoid.PhysicsCore
open ProofFreeRicherAnholonomicSource StageNineHolonomicField DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open scoped ContDiff
noncomputable section

/-- Test sections retain every original U field and change the matter section by the named weight. -/
def weighted (weight : BasePoint → ℂ) : StageNineHolonomicConfiguration :=
  { Stage10.Runtime.configuration with
    matter := fun p => weight p • Stage10.Runtime.configuration.matter p }

theorem original_matter_smooth :
    ContDiff ℝ ∞ (fun p => matterCoordinateEquiv (Stage10.Runtime.configuration.matter p)) :=
  Stage10.Recovery.stageOneThroughTenClosure.final.classical.smooth.2.2.2.2.2.2.2.1

/-- The full original connection is preserved; differentiating a test weight exposes its actual extra term. -/
theorem weighted_covariant_derivative (weight : BasePoint → ℂ) (p : BasePoint)
    (differentiable : DifferentiableAt ℝ weight p) (direction : LorentzianIndex) :
    holonomicMatterCovariantDerivative (weighted weight) p direction =
      weight p • holonomicMatterCovariantDerivative Stage10.Runtime.configuration p direction +
        fieldDirectionalDerivative weight p direction • Stage10.Runtime.configuration.matter p := by
  have dm : DifferentiableAt ℝ
      (fun x => matterCoordinateEquiv (Stage10.Runtime.configuration.matter x)) p :=
    original_matter_smooth.differentiable (by simp) p
  simp only [holonomicMatterCovariantDerivative, fieldDirectionalDerivative,
    fderiv_fun_smul differentiable dm, _root_.add_apply,
    ContinuousLinearMap.smulRight_apply, _root_.smul_apply,
    map_add, map_smul, weighted]
  rw [LinearEquiv.symm_apply_apply]
  module

end
end LAlanine40K2025.UnifiedAction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
