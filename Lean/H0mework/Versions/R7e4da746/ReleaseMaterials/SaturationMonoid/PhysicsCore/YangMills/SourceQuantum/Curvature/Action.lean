import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.PhysicsCore.YangMills.SourceQuantum.GaugeWords.Field
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.PhysicsCore.YangMills.Flat.Quantum.History.Variation

/-! The original compactly supported connection variation acts on all ordered quantum curvature words. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.YangMills.NativeCurvature.Variation
noncomputable section
open ProofFreeRicherAnholonomicSource StageNineHolonomicField Stage9C.Material.SpinPair
open StageNineCompactSupportIntegrationByParts StageNineP286GaugeConnectionVariation
open FullPairing Flat.Quantum SU7MotherLieAlgebra

local instance : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance : Fintype P286CoordinateIndex := Fintype.ofFinite P286CoordinateIndex

abbrev Input := CompactlySupportedSmoothVariation P286GaugeOneForm
abbrev Operator := Hilbert →L[ℂ] Hilbert

def representation : Mother →ₐ[ℂ] Operator where
  toFun := operator
  map_zero' := by ext v; simp [operator]
  map_one' := by ext v; simp [operator]
  map_add' A B := by ext v; simp [operator]
  map_mul' A B := by ext v; simp [operator]
  commutes' c := by ext v; simp [operator, Algebra.algebraMap_eq_smul_one]

def value (η : Input) (t : ℝ) : History.Polynomial →ₐ[ℂ] Operator :=
  representation.comp (quantumEvaluate (varyP286GaugeConnectionCoordinate actual η t))

def first (η : Input) (label : History.Label) : Operator :=
  operator (dualAction (History.coordinateAction
    (p286GaugeConnectionLinearCurvatureVariation actual η label.1 label.2)))

def second (η : Input) (label : History.Label) : Operator :=
  operator (dualAction (History.coordinateAction
    (p286GaugeConnectionQuadraticCurvatureVariation η label.1 label.2)))

private theorem dual_add (A B : Mother) : dualAction (A+B) = dualAction A + dualAction B := by
  apply LinearMap.ext
  intro v
  simp only [dualAction, LinearMap.comp_apply, LinearMap.add_apply, map_add]

private theorem dual_smul (c : ℂ) (A : Mother) : dualAction (c • A) = c • dualAction A := by
  apply LinearMap.ext
  intro v
  simp only [dualAction, LinearMap.comp_apply, LinearMap.smul_apply, map_smul]

theorem value_original (η : Input) (P : History.Polynomial) :
    value η 0 P = NativeSource.GaugeWords.seed P := by
  simp only [value, AlgHom.comp_apply, varyP286GaugeConnectionCoordinate_zero]
  rfl

theorem generator_expansion (η : Input) (t : ℝ) (label : History.Label) :
    value η t (FreeAlgebra.ι ℂ label) =
      NativeSource.GaugeWords.seed (FreeAlgebra.ι ℂ label) +
        t • first η label + t^2 • second η label := by
  rw [value, AlgHom.comp_apply, quantumEvaluate_generator,
    History.field_expansion actual actual_smooth η t label]
  simp only [History.expandedField, dual_add, dual_smul]
  change representation (_ + (t : ℂ) • _ + ((t^2 : ℝ) : ℂ) • _) = _
  rw [map_add, map_add, map_smul, map_smul]
  change operator (dualAction (History.field actual label)) + (t : ℂ) • first η label +
    ((t^2 : ℝ) : ℂ) • second η label = _
  rw [NativeSource.GaugeWords.seed, quantumEvaluate_generator,
    RCLike.real_smul_eq_coe_smul (K := ℂ) t (first η label),
    RCLike.real_smul_eq_coe_smul (K := ℂ) (t^2) (second η label)]
  rfl

theorem generator_hasDerivAt (η : Input) (t : ℝ) (label : History.Label) :
    HasDerivAt (fun e => value η e (FreeAlgebra.ι ℂ label))
      (first η label + (2*t) • second η label) t := by
  have generated := ((hasDerivAt_id t).smul_const (first η label)).const_add
    (NativeSource.GaugeWords.seed (FreeAlgebra.ι ℂ label)) |>.add
      (((hasDerivAt_id t).pow 2).smul_const (second η label))
  simp only [one_smul, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, id_eq, Pi.pow_apply] at generated
  convert! generated using 1
  funext e
  exact generator_expansion η e label

end
end SaturationMonoid.PhysicsCore.YangMills.NativeCurvature.Variation
