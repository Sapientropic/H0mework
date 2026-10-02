import H0mework.Versions.R2.Physics.GaugeSpectrum.GroundAcceptance

/-! The incoming primitive field generates the full ordered cubic action.
Its connection to the quantum cubic is proved through occupied invariance
of the actual exterior action, not assumed multiplicativity of responseMatrix. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum

open Matrix DiracCliffordRepresentation DiracExteriorMatterAction
open StageNineHolonomicField ProofFreeRicherAnholonomicSource
open StageNineP286GaugeConnectionVariation SU7MotherLieAlgebra SU7MotherGaugeTheory
open Stage9C.Material.SpinPair Stage9DEF Stage9DEF.Compatibility
open scoped Kronecker

noncomputable section

def incomingCurvatureAction (point : BasePoint) (axis : Fin 3) :
    Module.End ℂ DiracExteriorMatterCarrier :=
  Complex.I • diracExteriorMotherLieAction
    (p286LieBlockEmbed (holonomicGaugeCurvature Runtime.configuration point (magneticPair axis)))

def alternatingProduct {A : Type*} [Ring A] [Algebra ℂ A] (fields : Fin 3 → A) : A :=
  (-Complex.I / 6) •
    (fields 0 * fields 1 * fields 2 + fields 1 * fields 2 * fields 0 + fields 2 * fields 0 * fields 1 -
      fields 0 * fields 2 * fields 1 - fields 2 * fields 1 * fields 0 - fields 1 * fields 0 * fields 2)

def compositeAction (point : BasePoint) : Module.End ℂ DiracExteriorMatterCarrier :=
  alternatingProduct (incomingCurvatureAction point)

theorem incomingCurvatureAction_eq (point : BasePoint) (axis : Fin 3) :
    incomingCurvatureAction point axis = curvatureAction point axis := by
  rw [incomingCurvatureAction, Runtime.configuration_eq]
  rfl

theorem generatorAction_embed (axis : Fin 3) (values : Source.Index → ℂ) :
    diracExteriorMotherLieAction (p286LieBlockEmbed (sourceColorP286Generator axis)) (embed values) =
      embed (((1 : Matrix DiracSpinorIndex DiracSpinorIndex ℂ) ⊗ₖ sourceColorPauli axis) *ᵥ values) := by
  funext spin
  simp only [embed, diracExteriorMotherLieAction, internalMatterLinearAction,
    LinearMap.coe_mk, AddHom.coe_mk, sourceColorDiracMatter,
    map_sum, map_smul, sourceColorDoublet_generatorAction]
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply,
    smul_add, smul_smul]
  module

theorem incomingCurvatureAction_embed (point : BasePoint) (axis : Fin 3) (values : Source.Index → ℂ) :
    incomingCurvatureAction point axis (embed values) = embed (curvature point axis *ᵥ values) := by
  rw [incomingCurvatureAction_eq, curvatureAction, actual_magnetic_component,
    p286LieBlockEmbed_real_smul, diracExteriorMotherLieAction_real_smul]
  simp only [LinearMap.smul_apply, generatorAction_embed, curvature_normalForm, pauli,
    Matrix.kronecker_smul, Matrix.smul_mulVec, map_smul, smul_smul]
  congr 1
  simp [curvatureScale]
  ring

theorem compositeAction_embed (point : BasePoint) (values : Source.Index → ℂ) :
    compositeAction point (embed values) = embed (orientedCubic (curvature point) *ᵥ values) := by
  simp only [compositeAction, alternatingProduct, orientedCubic,
    Module.End.mul_apply, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply,
    incomingCurvatureAction_embed, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.sub_mulVec,
    ← Matrix.mulVec_mulVec, map_smul, map_add, map_sub]

theorem compositeAction_compression (point : BasePoint) :
    compression (compositeAction point) = orientedCubic (curvature point) := by
  have action_eq : coordinates.comp ((compositeAction point).comp embed) =
      Matrix.toLin' (orientedCubic (curvature point)) := by
    apply LinearMap.ext
    intro values
    simp only [LinearMap.comp_apply, compositeAction_embed, coordinates_embed, Matrix.toLin'_apply]
  rw [compression, action_eq, LinearMap.toMatrix'_toLin']

theorem curvature_triple (point : BasePoint) (first second third : Fin 3) :
    curvature point first * curvature point second * curvature point third =
      ((curvatureScale : ℂ) ^ 3) •
        ((1 : Matrix DiracSpinorIndex DiracSpinorIndex ℂ) ⊗ₖ (pauli first * pauli second * pauli third)) := by
  simp only [curvature_normalForm, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  congr 1
  ring

theorem rawCubic_normalForm (point : BasePoint) :
    orientedCubic (curvature point) = ((curvatureScale : ℂ) ^ 3) • 1 := by
  unfold orientedCubic
  simp_rw [curvature_triple]
  ext ⟨spin, color⟩ ⟨other, input⟩
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
    Matrix.kroneckerMap_apply, smul_eq_mul]
  rw [pauli_explicit]
  by_cases same : spin = other
  · subst other
    fin_cases color <;> fin_cases input <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
        ring_nf <;> simp [Complex.I_sq]
    all_goals ring_nf; simp [Complex.I_sq]; ring
  · simp [Prod.mk.injEq, same]

theorem compositeAction_responseMatrix (point : BasePoint) :
    responseMatrix (compositeAction point) = cubic point := by
  apply Matrix.ext
  intro row column
  rcases row with ⟨spin, color⟩
  rcases column with ⟨other, input⟩
  simp only [responseMatrix, compositeAction_compression, rawCubic_normalForm, cubic_normalForm]
  simp [Compatibility.flip, exchange, Matrix.one_apply, Prod.mk.injEq,
    Matrix.kroneckerMap_apply]
  split_ifs <;> simp_all

theorem compositeAction_quantum_response (point : BasePoint) :
    Runtime.configuration.conjugateMatter point
      (compositeAction point (Runtime.configuration.matter point)) =
      4 * (spinScale : ℂ) * State.vectorEvaluation (Runtime.tick.answer point) (cubic point) := by
  rw [Runtime.configuration_eq, Runtime.tick_vector]
  have response := actual_action_quantumResponse point (compositeAction point)
  rw [compositeAction_responseMatrix] at response
  exact response

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum
