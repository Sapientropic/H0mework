import H0mework.Physics.QuantumState.SourceCoefficients
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! The accepted linear dual is retained. Its source phase relation inserts
an upper/lower Dirac exchange into quantum response, rather than replacing
the independent dual by the adjoint of the prepared vector. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9DEF.Compatibility

open DiracCliffordRepresentation DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open Stage9C.Material.SpinPair
open scoped Matrix

noncomputable section

abbrev Matrix8 := Matrix Source.Index Source.Index ℂ

def embed : (Source.Index → ℂ) →ₗ[ℂ] DiracExteriorMatterCarrier where
  toFun values := sourceColorDiracMatter (fun spin color => values (spin, color))
  map_add' := by
    intro first second
    funext spin
    simp [sourceColorDiracMatter, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro coefficient values
    funext spin
    simp [sourceColorDiracMatter, smul_smul]

def coordinates : DiracExteriorMatterCarrier →ₗ[ℂ] (Source.Index → ℂ) where
  toFun matter index := sourceColorDoubletDual index.2 (matter index.1)
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp

theorem coordinates_embed (values : Source.Index → ℂ) : coordinates (embed values) = values := by
  ext index
  exact sourceColorDoubletDual_diracMatter _ _ _

def compression (action : Module.End ℂ DiracExteriorMatterCarrier) : Matrix8 :=
  LinearMap.toMatrix' (coordinates.comp (action.comp embed))

theorem compression_mulVec (action : Module.End ℂ DiracExteriorMatterCarrier)
    (values : Source.Index → ℂ) :
    compression action *ᵥ values = coordinates (action (embed values)) :=
  LinearMap.toMatrix'_mulVec _ _

def spinFlip (spin : DiracSpinorIndex) : DiracSpinorIndex := ![2, 3, 0, 1] spin

def flip (index : Source.Index) : Source.Index := (spinFlip index.1, index.2)

theorem spinFlip_involutive (spin : DiracSpinorIndex) : spinFlip (spinFlip spin) = spin := by
  fin_cases spin <;> rfl

theorem flip_involutive : Function.Involutive flip := by
  intro index
  simp [flip, spinFlip_involutive]

def dualCoefficient (point : BasePoint) (index : Source.Index) : ℂ :=
  spinPairCoefficients (upperDualPhase point) (lowerDualPhase point) index.1 index.2

theorem dualCoefficient_source_star (point : BasePoint) (index : Source.Index) :
    dualCoefficient point index = 2 * (spinScale : ℂ) * star (Source.vector point (flip index)) := by
  rcases index with ⟨spin, color⟩
  fin_cases spin <;> fin_cases color <;>
    simp [dualCoefficient, Source.vector, Source.amplitude, flip, spinFlip,
      spinPairCoefficients, upperDualPhase, lowerDualPhase, upperPhase, lowerPhase,
      Source.phase_star] <;> ring

def vectorRead (point : BasePoint) (observable : Matrix8) : ℂ :=
  ∑ index, star (Source.vector point index) * (observable *ᵥ Source.vector point) index

def responseMatrix (action : Module.End ℂ DiracExteriorMatterCarrier) : Matrix8 :=
  fun row column => compression action (flip row) column

theorem responseMatrix_mulVec (action : Module.End ℂ DiracExteriorMatterCarrier)
    (values : Source.Index → ℂ) (index : Source.Index) :
    (responseMatrix action *ᵥ values) index =
      coordinates (action (embed values)) (flip index) := by
  exact congrFun (compression_mulVec action values) (flip index)

theorem actual_dual_evaluation (point : BasePoint) (matter : DiracExteriorMatterCarrier) :
    actual.conjugateMatter point matter =
      ∑ index : Source.Index, dualCoefficient point index * coordinates matter index := by
  rw [actual_conjugateMatter]
  simp only [spinPairDual, sourceColorDiracDual, Fintype.sum_prod_type,
    dualCoefficient, coordinates, LinearMap.coe_mk, AddHom.coe_mk]

theorem actual_action_quantumResponse (point : BasePoint)
    (action : Module.End ℂ DiracExteriorMatterCarrier) :
    actual.conjugateMatter point (action (actual.matter point)) =
      4 * (spinScale : ℂ) * vectorRead point (responseMatrix action) := by
  have reconstructed : actual.matter point = (2 : ℂ) • embed (Source.vector point) := by
    rw [← Source.amplitude_reconstruction point, ← map_smul]
    congr 1
    ext spin color
    exact Source.amplitude_eq_twice_vector point (spin, color)
  rw [reconstructed, map_smul, actual_dual_evaluation]
  simp only [map_smul, dualCoefficient_source_star, Pi.smul_apply, smul_eq_mul]
  rw [show (∑ index : Source.Index,
      2 * (spinScale : ℂ) * star (Source.vector point (flip index)) *
        (2 * coordinates (action (embed (Source.vector point))) index)) =
      ∑ index : Source.Index,
      2 * (spinScale : ℂ) * star (Source.vector point index) *
        (2 * coordinates (action (embed (Source.vector point))) (flip index)) by
    simp [Fintype.sum_prod_type, Fin.sum_univ_four, Fin.sum_univ_two, flip, spinFlip]
    ring]
  unfold vectorRead
  simp_rw [responseMatrix_mulVec]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  ring

end
end SaturationMonoid.PhysicsCore.Stage9DEF.Compatibility
