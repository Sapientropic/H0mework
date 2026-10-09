import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationCoframeInverseJets

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.SourcePropagationNativeActionHessian
open SaturationMonoid.PhysicsCore
open ProofFreeRicherAnholonomicSource StageNineGlobalIntegratedAction
open Stage9C.Dynamics.Homogeneous Stage9C.Material.SpinPair
open scoped BigOperators Matrix.Norms.Elementwise

def nativeHodgeFirstFlat (h : LorentzianCoframe) (i j : Fin 6) : ℝ :=
  match i.val, j.val with
  | 0, 1 => -lapse⁻¹ * h 3 0 + h 0 3
  | 0, 2 => lapse⁻¹ * h 2 0 - h 0 2
  | 0, 3 => -(lapse⁻¹)^2 * h 0 0 - lapse⁻¹ * h 1 1 + lapse⁻¹ * h 2 2 + lapse⁻¹ * h 3 3
  | 0, 4 => -lapse⁻¹ * h 1 2 - lapse⁻¹ * h 2 1
  | 0, 5 => -lapse⁻¹ * h 1 3 - lapse⁻¹ * h 3 1
  | 1, 0 => lapse⁻¹ * h 3 0 - h 0 3
  | 1, 2 => -lapse⁻¹ * h 1 0 + h 0 1
  | 1, 3 => -lapse⁻¹ * h 1 2 - lapse⁻¹ * h 2 1
  | 1, 4 => -(lapse⁻¹)^2 * h 0 0 + lapse⁻¹ * h 1 1 - lapse⁻¹ * h 2 2 + lapse⁻¹ * h 3 3
  | 1, 5 => -lapse⁻¹ * h 2 3 - lapse⁻¹ * h 3 2
  | 2, 0 => -lapse⁻¹ * h 2 0 + h 0 2
  | 2, 1 => lapse⁻¹ * h 1 0 - h 0 1
  | 2, 3 => -lapse⁻¹ * h 1 3 - lapse⁻¹ * h 3 1
  | 2, 4 => -lapse⁻¹ * h 2 3 - lapse⁻¹ * h 3 2
  | 2, 5 => -(lapse⁻¹)^2 * h 0 0 + lapse⁻¹ * h 1 1 + lapse⁻¹ * h 2 2 - lapse⁻¹ * h 3 3
  | 3, 0 => -h 0 0 - lapse * h 1 1 + lapse * h 2 2 + lapse * h 3 3
  | 3, 1 => -lapse * h 1 2 - lapse * h 2 1
  | 3, 2 => -lapse * h 1 3 - lapse * h 3 1
  | 3, 4 => lapse⁻¹ * h 3 0 - h 0 3
  | 3, 5 => -lapse⁻¹ * h 2 0 + h 0 2
  | 4, 0 => -lapse * h 1 2 - lapse * h 2 1
  | 4, 1 => -h 0 0 + lapse * h 1 1 - lapse * h 2 2 + lapse * h 3 3
  | 4, 2 => -lapse * h 2 3 - lapse * h 3 2
  | 4, 3 => -lapse⁻¹ * h 3 0 + h 0 3
  | 4, 5 => lapse⁻¹ * h 1 0 - h 0 1
  | 5, 0 => -lapse * h 1 3 - lapse * h 3 1
  | 5, 1 => -lapse * h 2 3 - lapse * h 3 2
  | 5, 2 => -h 0 0 + lapse * h 1 1 + lapse * h 2 2 - lapse * h 3 3
  | 5, 3 => lapse⁻¹ * h 2 0 - h 0 2
  | 5, 4 => -lapse⁻¹ * h 1 0 + h 0 1
  | _, _ => 0

def nativeHodgeSecondFlat (h : LorentzianCoframe) (i j : Fin 6) : ℝ :=
  match i.val, j.val with
  | 0, 0 => -lapse⁻¹ * h 1 2 * h 3 0 + lapse⁻¹ * h 1 3 * h 2 0 + lapse⁻¹ * h 2 0 * h 3 1 - lapse⁻¹ * h 2 1 * h 3 0 - h 0 2 * h 1 3 - h 0 2 * h 3 1 + h 0 3 * h 1 2 + h 0 3 * h 2 1
  | 0, 1 => (lapse⁻¹)^2 * h 0 0 * h 3 0 - lapse⁻¹ * h 1 0 * h 1 3 + lapse⁻¹ * h 1 1 * h 3 0 + lapse⁻¹ * h 2 0 * h 3 2 - lapse⁻¹ * h 2 2 * h 3 0 - h 0 2 * h 2 3 - h 0 2 * h 3 2 - h 0 3 * h 1 1 + h 0 3 * h 2 2 - h 0 3 * h 3 3
  | 0, 2 => -(lapse⁻¹)^2 * h 0 0 * h 2 0 + lapse⁻¹ * h 1 0 * h 1 2 - lapse⁻¹ * h 1 1 * h 2 0 + lapse⁻¹ * h 2 0 * h 3 3 - lapse⁻¹ * h 2 3 * h 3 0 + h 0 2 * h 1 1 + h 0 2 * h 2 2 - h 0 2 * h 3 3 + h 0 3 * h 2 3 + h 0 3 * h 3 2
  | 0, 3 => (lapse⁻¹)^3 * h 0 0 * h 0 0 + (lapse⁻¹)^2 * h 0 0 * h 1 1 - (lapse⁻¹)^2 * h 0 0 * h 2 2 - (lapse⁻¹)^2 * h 0 0 * h 3 3 + (lapse⁻¹)^2 * h 0 1 * h 1 0 + (lapse⁻¹)^2 * h 0 2 * h 2 0 + (lapse⁻¹)^2 * h 0 3 * h 3 0 - lapse⁻¹ * h 0 2 * h 0 2 - lapse⁻¹ * h 0 3 * h 0 3 + lapse⁻¹ * h 1 1 * h 1 1 - lapse⁻¹ * h 1 1 * h 2 2 - lapse⁻¹ * h 1 1 * h 3 3 + lapse⁻¹ * h 1 2 * h 1 2 + lapse⁻¹ * h 1 2 * h 2 1 + lapse⁻¹ * h 1 3 * h 1 3 + lapse⁻¹ * h 1 3 * h 3 1 + lapse⁻¹ * h 2 2 * h 3 3 - lapse⁻¹ * h 2 3 * h 3 2
  | 0, 4 => (lapse⁻¹)^2 * h 0 0 * h 1 2 + (lapse⁻¹)^2 * h 0 0 * h 2 1 + lapse⁻¹ * h 0 1 * h 0 2 + lapse⁻¹ * h 1 1 * h 2 1 + lapse⁻¹ * h 1 2 * h 2 2 - lapse⁻¹ * h 1 2 * h 3 3 + lapse⁻¹ * h 1 3 * h 2 3 + lapse⁻¹ * h 1 3 * h 3 2 - lapse⁻¹ * h 2 1 * h 3 3 + lapse⁻¹ * h 2 3 * h 3 1
  | 0, 5 => (lapse⁻¹)^2 * h 0 0 * h 1 3 + (lapse⁻¹)^2 * h 0 0 * h 3 1 + lapse⁻¹ * h 0 1 * h 0 3 + lapse⁻¹ * h 1 1 * h 3 1 + lapse⁻¹ * h 1 2 * h 2 3 + lapse⁻¹ * h 1 2 * h 3 2 - lapse⁻¹ * h 1 3 * h 2 2 + lapse⁻¹ * h 1 3 * h 3 3 + lapse⁻¹ * h 2 1 * h 3 2 - lapse⁻¹ * h 2 2 * h 3 1
  | 1, 0 => -(lapse⁻¹)^2 * h 0 0 * h 3 0 - lapse⁻¹ * h 1 0 * h 3 1 + lapse⁻¹ * h 1 1 * h 3 0 + lapse⁻¹ * h 2 0 * h 2 3 - lapse⁻¹ * h 2 2 * h 3 0 + h 0 1 * h 1 3 + h 0 1 * h 3 1 - h 0 3 * h 1 1 + h 0 3 * h 2 2 + h 0 3 * h 3 3
  | 1, 1 => -lapse⁻¹ * h 1 0 * h 2 3 - lapse⁻¹ * h 1 0 * h 3 2 + lapse⁻¹ * h 1 2 * h 3 0 + lapse⁻¹ * h 2 1 * h 3 0 + h 0 1 * h 2 3 + h 0 1 * h 3 2 - h 0 3 * h 1 2 - h 0 3 * h 2 1
  | 1, 2 => (lapse⁻¹)^2 * h 0 0 * h 1 0 + lapse⁻¹ * h 1 0 * h 2 2 - lapse⁻¹ * h 1 0 * h 3 3 + lapse⁻¹ * h 1 3 * h 3 0 - lapse⁻¹ * h 2 0 * h 2 1 - h 0 1 * h 1 1 - h 0 1 * h 2 2 + h 0 1 * h 3 3 - h 0 3 * h 1 3 - h 0 3 * h 3 1
  | 1, 3 => (lapse⁻¹)^2 * h 0 0 * h 1 2 + (lapse⁻¹)^2 * h 0 0 * h 2 1 + lapse⁻¹ * h 0 1 * h 0 2 + lapse⁻¹ * h 1 1 * h 2 1 + lapse⁻¹ * h 1 2 * h 2 2 - lapse⁻¹ * h 1 2 * h 3 3 + lapse⁻¹ * h 1 3 * h 2 3 + lapse⁻¹ * h 1 3 * h 3 2 - lapse⁻¹ * h 2 1 * h 3 3 + lapse⁻¹ * h 2 3 * h 3 1
  | 1, 4 => (lapse⁻¹)^3 * h 0 0 * h 0 0 - (lapse⁻¹)^2 * h 0 0 * h 1 1 + (lapse⁻¹)^2 * h 0 0 * h 2 2 - (lapse⁻¹)^2 * h 0 0 * h 3 3 + (lapse⁻¹)^2 * h 0 1 * h 1 0 + (lapse⁻¹)^2 * h 0 2 * h 2 0 + (lapse⁻¹)^2 * h 0 3 * h 3 0 - lapse⁻¹ * h 0 1 * h 0 1 - lapse⁻¹ * h 0 3 * h 0 3 - lapse⁻¹ * h 1 1 * h 2 2 + lapse⁻¹ * h 1 1 * h 3 3 + lapse⁻¹ * h 1 2 * h 2 1 - lapse⁻¹ * h 1 3 * h 3 1 + lapse⁻¹ * h 2 1 * h 2 1 + lapse⁻¹ * h 2 2 * h 2 2 - lapse⁻¹ * h 2 2 * h 3 3 + lapse⁻¹ * h 2 3 * h 2 3 + lapse⁻¹ * h 2 3 * h 3 2
  | 1, 5 => (lapse⁻¹)^2 * h 0 0 * h 2 3 + (lapse⁻¹)^2 * h 0 0 * h 3 2 + lapse⁻¹ * h 0 2 * h 0 3 - lapse⁻¹ * h 1 1 * h 2 3 - lapse⁻¹ * h 1 1 * h 3 2 + lapse⁻¹ * h 1 2 * h 3 1 + lapse⁻¹ * h 1 3 * h 2 1 + lapse⁻¹ * h 2 1 * h 3 1 + lapse⁻¹ * h 2 2 * h 3 2 + lapse⁻¹ * h 2 3 * h 3 3
  | 2, 0 => (lapse⁻¹)^2 * h 0 0 * h 2 0 + lapse⁻¹ * h 1 0 * h 2 1 - lapse⁻¹ * h 1 1 * h 2 0 + lapse⁻¹ * h 2 0 * h 3 3 - lapse⁻¹ * h 3 0 * h 3 2 - h 0 1 * h 1 2 - h 0 1 * h 2 1 + h 0 2 * h 1 1 - h 0 2 * h 2 2 - h 0 2 * h 3 3
  | 2, 1 => -(lapse⁻¹)^2 * h 0 0 * h 1 0 + lapse⁻¹ * h 1 0 * h 2 2 - lapse⁻¹ * h 1 0 * h 3 3 - lapse⁻¹ * h 1 2 * h 2 0 + lapse⁻¹ * h 3 0 * h 3 1 + h 0 1 * h 1 1 - h 0 1 * h 2 2 + h 0 1 * h 3 3 + h 0 2 * h 1 2 + h 0 2 * h 2 1
  | 2, 2 => lapse⁻¹ * h 1 0 * h 2 3 + lapse⁻¹ * h 1 0 * h 3 2 - lapse⁻¹ * h 1 3 * h 2 0 - lapse⁻¹ * h 2 0 * h 3 1 - h 0 1 * h 2 3 - h 0 1 * h 3 2 + h 0 2 * h 1 3 + h 0 2 * h 3 1
  | 2, 3 => (lapse⁻¹)^2 * h 0 0 * h 1 3 + (lapse⁻¹)^2 * h 0 0 * h 3 1 + lapse⁻¹ * h 0 1 * h 0 3 + lapse⁻¹ * h 1 1 * h 3 1 + lapse⁻¹ * h 1 2 * h 2 3 + lapse⁻¹ * h 1 2 * h 3 2 - lapse⁻¹ * h 1 3 * h 2 2 + lapse⁻¹ * h 1 3 * h 3 3 + lapse⁻¹ * h 2 1 * h 3 2 - lapse⁻¹ * h 2 2 * h 3 1
  | 2, 4 => (lapse⁻¹)^2 * h 0 0 * h 2 3 + (lapse⁻¹)^2 * h 0 0 * h 3 2 + lapse⁻¹ * h 0 2 * h 0 3 - lapse⁻¹ * h 1 1 * h 2 3 - lapse⁻¹ * h 1 1 * h 3 2 + lapse⁻¹ * h 1 2 * h 3 1 + lapse⁻¹ * h 1 3 * h 2 1 + lapse⁻¹ * h 2 1 * h 3 1 + lapse⁻¹ * h 2 2 * h 3 2 + lapse⁻¹ * h 2 3 * h 3 3
  | 2, 5 => (lapse⁻¹)^3 * h 0 0 * h 0 0 - (lapse⁻¹)^2 * h 0 0 * h 1 1 - (lapse⁻¹)^2 * h 0 0 * h 2 2 + (lapse⁻¹)^2 * h 0 0 * h 3 3 + (lapse⁻¹)^2 * h 0 1 * h 1 0 + (lapse⁻¹)^2 * h 0 2 * h 2 0 + (lapse⁻¹)^2 * h 0 3 * h 3 0 - lapse⁻¹ * h 0 1 * h 0 1 - lapse⁻¹ * h 0 2 * h 0 2 + lapse⁻¹ * h 1 1 * h 2 2 - lapse⁻¹ * h 1 1 * h 3 3 - lapse⁻¹ * h 1 2 * h 2 1 + lapse⁻¹ * h 1 3 * h 3 1 - lapse⁻¹ * h 2 2 * h 3 3 + lapse⁻¹ * h 2 3 * h 3 2 + lapse⁻¹ * h 3 1 * h 3 1 + lapse⁻¹ * h 3 2 * h 3 2 + lapse⁻¹ * h 3 3 * h 3 3
  | 3, 0 => lapse⁻¹ * h 2 0 * h 2 0 + lapse⁻¹ * h 3 0 * h 3 0 - h 0 0 * h 1 1 + h 0 0 * h 2 2 + h 0 0 * h 3 3 + h 0 1 * h 1 0 - h 0 2 * h 2 0 - h 0 3 * h 3 0 + lapse * h 1 1 * h 2 2 + lapse * h 1 1 * h 3 3 - lapse * h 1 2 * h 2 1 - lapse * h 1 3 * h 3 1 - lapse * h 2 1 * h 2 1 - lapse * h 2 2 * h 2 2 - lapse * h 2 2 * h 3 3 - lapse * h 2 3 * h 3 2 - lapse * h 3 1 * h 3 1 - lapse * h 3 3 * h 3 3
  | 3, 1 => -lapse⁻¹ * h 1 0 * h 2 0 - h 0 0 * h 1 2 - h 0 0 * h 2 1 + h 0 1 * h 2 0 + h 0 2 * h 1 0 + lapse * h 1 1 * h 2 1 + lapse * h 1 2 * h 2 2 + lapse * h 1 2 * h 3 3 + lapse * h 2 1 * h 3 3 - lapse * h 3 1 * h 3 2
  | 3, 2 => -lapse⁻¹ * h 1 0 * h 3 0 - h 0 0 * h 1 3 - h 0 0 * h 3 1 + h 0 1 * h 3 0 + h 0 3 * h 1 0 + lapse * h 1 1 * h 3 1 + lapse * h 1 3 * h 2 2 + lapse * h 1 3 * h 3 3 - lapse * h 2 1 * h 2 3 + lapse * h 2 2 * h 3 1
  | 3, 3 => -lapse⁻¹ * h 1 2 * h 3 0 + lapse⁻¹ * h 1 3 * h 2 0 + lapse⁻¹ * h 2 0 * h 3 1 - lapse⁻¹ * h 2 1 * h 3 0 - h 0 2 * h 1 3 - h 0 2 * h 3 1 + h 0 3 * h 1 2 + h 0 3 * h 2 1
  | 3, 4 => -(lapse⁻¹)^2 * h 0 0 * h 3 0 - lapse⁻¹ * h 1 0 * h 3 1 + lapse⁻¹ * h 1 1 * h 3 0 + lapse⁻¹ * h 2 0 * h 2 3 - lapse⁻¹ * h 2 2 * h 3 0 + h 0 1 * h 1 3 + h 0 1 * h 3 1 - h 0 3 * h 1 1 + h 0 3 * h 2 2 + h 0 3 * h 3 3
  | 3, 5 => (lapse⁻¹)^2 * h 0 0 * h 2 0 + lapse⁻¹ * h 1 0 * h 2 1 - lapse⁻¹ * h 1 1 * h 2 0 + lapse⁻¹ * h 2 0 * h 3 3 - lapse⁻¹ * h 3 0 * h 3 2 - h 0 1 * h 1 2 - h 0 1 * h 2 1 + h 0 2 * h 1 1 - h 0 2 * h 2 2 - h 0 2 * h 3 3
  | 4, 0 => -lapse⁻¹ * h 1 0 * h 2 0 - h 0 0 * h 1 2 - h 0 0 * h 2 1 + h 0 1 * h 2 0 + h 0 2 * h 1 0 + lapse * h 1 1 * h 2 1 + lapse * h 1 2 * h 2 2 + lapse * h 1 2 * h 3 3 + lapse * h 2 1 * h 3 3 - lapse * h 3 1 * h 3 2
  | 4, 1 => lapse⁻¹ * h 1 0 * h 1 0 + lapse⁻¹ * h 3 0 * h 3 0 + h 0 0 * h 1 1 - h 0 0 * h 2 2 + h 0 0 * h 3 3 - h 0 1 * h 1 0 + h 0 2 * h 2 0 - h 0 3 * h 3 0 - lapse * h 1 1 * h 1 1 + lapse * h 1 1 * h 2 2 - lapse * h 1 1 * h 3 3 - lapse * h 1 2 * h 1 2 - lapse * h 1 2 * h 2 1 - lapse * h 1 3 * h 3 1 + lapse * h 2 2 * h 3 3 - lapse * h 2 3 * h 3 2 - lapse * h 3 2 * h 3 2 - lapse * h 3 3 * h 3 3
  | 4, 2 => -lapse⁻¹ * h 2 0 * h 3 0 - h 0 0 * h 2 3 - h 0 0 * h 3 2 + h 0 2 * h 3 0 + h 0 3 * h 2 0 + lapse * h 1 1 * h 2 3 + lapse * h 1 1 * h 3 2 - lapse * h 1 2 * h 1 3 + lapse * h 2 2 * h 3 2 + lapse * h 2 3 * h 3 3
  | 4, 3 => (lapse⁻¹)^2 * h 0 0 * h 3 0 - lapse⁻¹ * h 1 0 * h 1 3 + lapse⁻¹ * h 1 1 * h 3 0 + lapse⁻¹ * h 2 0 * h 3 2 - lapse⁻¹ * h 2 2 * h 3 0 - h 0 2 * h 2 3 - h 0 2 * h 3 2 - h 0 3 * h 1 1 + h 0 3 * h 2 2 - h 0 3 * h 3 3
  | 4, 4 => -lapse⁻¹ * h 1 0 * h 2 3 - lapse⁻¹ * h 1 0 * h 3 2 + lapse⁻¹ * h 1 2 * h 3 0 + lapse⁻¹ * h 2 1 * h 3 0 + h 0 1 * h 2 3 + h 0 1 * h 3 2 - h 0 3 * h 1 2 - h 0 3 * h 2 1
  | 4, 5 => -(lapse⁻¹)^2 * h 0 0 * h 1 0 + lapse⁻¹ * h 1 0 * h 2 2 - lapse⁻¹ * h 1 0 * h 3 3 - lapse⁻¹ * h 1 2 * h 2 0 + lapse⁻¹ * h 3 0 * h 3 1 + h 0 1 * h 1 1 - h 0 1 * h 2 2 + h 0 1 * h 3 3 + h 0 2 * h 1 2 + h 0 2 * h 2 1
  | 5, 0 => -lapse⁻¹ * h 1 0 * h 3 0 - h 0 0 * h 1 3 - h 0 0 * h 3 1 + h 0 1 * h 3 0 + h 0 3 * h 1 0 + lapse * h 1 1 * h 3 1 + lapse * h 1 3 * h 2 2 + lapse * h 1 3 * h 3 3 - lapse * h 2 1 * h 2 3 + lapse * h 2 2 * h 3 1
  | 5, 1 => -lapse⁻¹ * h 2 0 * h 3 0 - h 0 0 * h 2 3 - h 0 0 * h 3 2 + h 0 2 * h 3 0 + h 0 3 * h 2 0 + lapse * h 1 1 * h 2 3 + lapse * h 1 1 * h 3 2 - lapse * h 1 2 * h 1 3 + lapse * h 2 2 * h 3 2 + lapse * h 2 3 * h 3 3
  | 5, 2 => lapse⁻¹ * h 1 0 * h 1 0 + lapse⁻¹ * h 2 0 * h 2 0 + h 0 0 * h 1 1 + h 0 0 * h 2 2 - h 0 0 * h 3 3 - h 0 1 * h 1 0 - h 0 2 * h 2 0 + h 0 3 * h 3 0 - lapse * h 1 1 * h 1 1 - lapse * h 1 1 * h 2 2 + lapse * h 1 1 * h 3 3 - lapse * h 1 2 * h 2 1 - lapse * h 1 3 * h 1 3 - lapse * h 1 3 * h 3 1 - lapse * h 2 2 * h 2 2 + lapse * h 2 2 * h 3 3 - lapse * h 2 3 * h 2 3 - lapse * h 2 3 * h 3 2
  | 5, 3 => -(lapse⁻¹)^2 * h 0 0 * h 2 0 + lapse⁻¹ * h 1 0 * h 1 2 - lapse⁻¹ * h 1 1 * h 2 0 + lapse⁻¹ * h 2 0 * h 3 3 - lapse⁻¹ * h 2 3 * h 3 0 + h 0 2 * h 1 1 + h 0 2 * h 2 2 - h 0 2 * h 3 3 + h 0 3 * h 2 3 + h 0 3 * h 3 2
  | 5, 4 => (lapse⁻¹)^2 * h 0 0 * h 1 0 + lapse⁻¹ * h 1 0 * h 2 2 - lapse⁻¹ * h 1 0 * h 3 3 + lapse⁻¹ * h 1 3 * h 3 0 - lapse⁻¹ * h 2 0 * h 2 1 - h 0 1 * h 1 1 - h 0 1 * h 2 2 + h 0 1 * h 3 3 - h 0 3 * h 1 3 - h 0 3 * h 3 1
  | 5, 5 => lapse⁻¹ * h 1 0 * h 2 3 + lapse⁻¹ * h 1 0 * h 3 2 - lapse⁻¹ * h 1 3 * h 2 0 - lapse⁻¹ * h 2 0 * h 3 1 - h 0 1 * h 2 3 - h 0 1 * h 3 2 + h 0 2 * h 1 3 + h 0 2 * h 3 1
  | _, _ => 0

theorem nativeHodgeFirst_flat (h : LorentzianCoframe) (i j : Fin 6) :
    nativeHodgeFirst (homogeneousCoframe lapse) h i j = nativeHodgeFirstFlat h i j := by
  unfold nativeHodgeFirst
  rw [homogeneousCoframe_inv lapse (ne_of_gt lapse_pos)]
  fin_cases i <;> fin_cases j <;>
    simp [nativeHodgeFirstFlat, exteriorTangent, exteriorMatrix, coframeHodgeMatrixConst,
      gaugeOperatorCoefficient, EmpiricalReferenceScaleCouplingBoundary.lorentzianCoframeHodgeEquiv,
      lorentzianCoframeHodge, StageNineCartanTangentSimplicityResponse.coframeWedgeTangent,
      coframeWedge, homogeneousCoframe, Matrix.diagonal_apply, Matrix.mul_apply,
      Matrix.add_apply, Matrix.neg_apply, pairFirst, pairSecond, Fin.sum_univ_six, Fin.sum_univ_four]
  all_goals field_simp [ne_of_gt lapse_pos]
  all_goals ring

theorem nativeHodgeSecond_flat (h : LorentzianCoframe) (i j : Fin 6) :
    nativeHodgeSecond (homogeneousCoframe lapse) h i j = nativeHodgeSecondFlat h i j := by
  unfold nativeHodgeSecond
  rw [homogeneousCoframe_inv lapse (ne_of_gt lapse_pos)]
  fin_cases i <;> fin_cases j <;>
    simp [nativeHodgeSecondFlat, exteriorTangent, exteriorMatrix, coframeHodgeMatrixConst,
      gaugeOperatorCoefficient, EmpiricalReferenceScaleCouplingBoundary.lorentzianCoframeHodgeEquiv,
      lorentzianCoframeHodge, StageNineCartanTangentSimplicityResponse.coframeWedgeTangent,
      coframeWedge, homogeneousCoframe, Matrix.diagonal_apply, Matrix.mul_apply,
      Matrix.add_apply, Matrix.neg_apply, pairFirst, pairSecond, Fin.sum_univ_six, Fin.sum_univ_four]
  all_goals field_simp [ne_of_gt lapse_pos]
  all_goals ring

end LowEnergy.SourcePropagationNativeActionHessian
