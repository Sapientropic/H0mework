import H0mework.Physics.SpinPair.GaugeField
import H0mework.Physics.SpinPair.ColorInvariant
import H0mework.Physics.QuantumCompatibility.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! The original non-Abelian curvature acts on the original occupied matter.
The second operator retains the independent dual's Dirac exchange. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum

open Matrix DiracCliffordRepresentation DiracExteriorMatterAction
open StageNineHolonomicField ProofFreeRicherAnholonomicSource
open StageNineP286GaugeConnectionVariation StageNineHolonomicGaugeCurvatureTransport
open SU7MotherLieAlgebra SU7MotherGaugeTheory
open Stage9C.Material.SpinPair Stage9DEF Stage9DEF.Compatibility
open scoped Kronecker

noncomputable section

def magneticPair (axis : Fin 3) : Fin 6 := ![3, 4, 5] axis

def curvatureScale : ℝ := gaugeScale ^ 2 / 2

theorem curvatureScale_pos : 0 < curvatureScale := by
  exact div_pos (sq_pos_of_pos gaugeScale_pos) (by norm_num)

def pauli (axis : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  (-2 * Complex.I) • sourceColorPauli axis

theorem pauli_explicit : pauli =
    ![!![0, 1; 1, 0], !![0, -Complex.I; Complex.I, 0], !![1, 0; 0, -1]] := by
  ext axis row column
  fin_cases axis <;> fin_cases row <;> fin_cases column <;>
    norm_num [pauli, sourceColorPauli] <;> ring_nf <;> simp [Complex.I_sq]

def exchange : Matrix DiracSpinorIndex DiracSpinorIndex ℂ :=
  fun row column => if spinFlip row = column then 1 else 0

def curvatureAction (point : BasePoint) (axis : Fin 3) :
    Module.End ℂ DiracExteriorMatterCarrier :=
  Complex.I • diracExteriorMotherLieAction
    (p286LieBlockEmbed (holonomicGaugeCurvature actual point (magneticPair axis)))

def curvature (point : BasePoint) (axis : Fin 3) : State.Observable :=
  compression (curvatureAction point axis)

def dualCurvature (point : BasePoint) (axis : Fin 3) : State.Observable :=
  responseMatrix (curvatureAction point axis)

theorem actual_magnetic_component (point : BasePoint) (axis : Fin 3) :
    holonomicGaugeCurvature actual point (magneticPair axis) =
      -(gaugeScale ^ 2) • sourceColorP286Generator axis := by
  rw [actual_gaugeCurvature]
  fin_cases axis <;> rfl

theorem compression_generator (axis : Fin 3) :
    compression (diracExteriorMotherLieAction
      (p286LieBlockEmbed (sourceColorP286Generator axis))) =
      (1 : Matrix DiracSpinorIndex DiracSpinorIndex ℂ) ⊗ₖ sourceColorPauli axis := by
  apply Matrix.ext
  intro row column
  rcases row with ⟨spin, color⟩
  rcases column with ⟨other, input⟩
  rw [compression, LinearMap.toMatrix'_apply]
  simp only [LinearMap.comp_apply, coordinates, embed, diracExteriorMotherLieAction,
    internalMatterLinearAction, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [sourceColorDiracMatter, map_sum, map_smul,
    sourceColorDoublet_generatorAction]
  simp only [sourceColorDoubletDual_basis, smul_eq_mul]
  fin_cases input <;> by_cases same : spin = other <;>
    simp [Pi.single_apply, Prod.mk.injEq, same]

theorem compression_smul (scalar : ℂ) (action : Module.End ℂ DiracExteriorMatterCarrier) :
    compression (scalar • action) = scalar • compression action := by
  ext row column
  simp [compression, LinearMap.toMatrix'_apply]

theorem curvature_normalForm (point : BasePoint) (axis : Fin 3) :
    curvature point axis =
      (curvatureScale : ℂ) • ((1 : Matrix DiracSpinorIndex DiracSpinorIndex ℂ) ⊗ₖ pauli axis) := by
  unfold curvature curvatureAction
  rw [actual_magnetic_component, p286LieBlockEmbed_real_smul,
    diracExteriorMotherLieAction_real_smul, compression_smul, compression_smul,
    compression_generator]
  ext row column
  simp [pauli, curvatureScale, Matrix.smul_apply, Matrix.kroneckerMap_apply]
  ring

theorem dualCurvature_normalForm (point : BasePoint) (axis : Fin 3) :
    dualCurvature point axis = (curvatureScale : ℂ) • (exchange ⊗ₖ pauli axis) := by
  ext row column
  change curvature point axis (Compatibility.flip row) column = _
  rw [curvature_normalForm]
  simp [exchange, Compatibility.flip, Matrix.one_apply, Matrix.kroneckerMap_apply]

theorem dualCurvature_actual_response (point : BasePoint) (axis : Fin 3) :
    actual.conjugateMatter point (curvatureAction point axis (actual.matter point)) =
      4 * (spinScale : ℂ) * State.evaluation point (dualCurvature point axis) :=
  actual_action_quantumResponse point (curvatureAction point axis)

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum
