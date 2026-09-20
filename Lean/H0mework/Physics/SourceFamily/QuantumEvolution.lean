import H0mework.Physics.SourceFamily.Acceptance
import H0mework.Physics.QuantumState.SourceRestriction
import H0mework.Physics.QuantumCompatibility.DualResponse
import H0mework.Physics.QuantumState.StateVector

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.SourceFamilyEvolution.Quantum

open DiracCliffordRepresentation DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineCClassicalWorldAcceptance
open Stage9C.Material.SpinPair SourceFamily
open scoped Matrix

noncomputable section

def occupied (step : ℕ) : Stage9DEF.Source.OccupiedField :=
  Stage9DEF.Source.restrict (fieldAt step)

theorem occupied_formula (step : ℕ) (point : BasePoint) (index : Stage9DEF.Source.Index) :
    occupied step point index = spinPairCoefficients
      (phase (phaseRate step) point) (phase (-phaseRate step) point) index.1 index.2 / 2 := by
  unfold occupied Stage9DEF.Source.restrict
  rw [Gauge.field_matter]
  change sourceColorDoubletDual index.2
    (sourceColorDiracMatter (spinPairCoefficients _ _) index.1) / 2 = _
  rw [sourceColorDoubletDual_diracMatter]
  rfl

/-- Reconstruction is for this family's actual occupied matter. The
ambient action below may send it outside the occupied subspace. -/
theorem matter_reconstruction (step : ℕ) (point : BasePoint) :
    (fieldAt step).matter point =
      (2 : ℂ) • Stage9DEF.Compatibility.embed (occupied step point) := by
  calc
    (fieldAt step).matter point = Stage9DEF.Compatibility.embed
        (fun index => spinPairCoefficients
          (phase (phaseRate step) point) (phase (-phaseRate step) point) index.1 index.2) := rfl
    _ = Stage9DEF.Compatibility.embed ((2 : ℂ) • occupied step point) := by
      congr 1
      funext index
      simp only [Pi.smul_apply, smul_eq_mul, occupied_formula]
      ring
    _ = (2 : ℂ) • Stage9DEF.Compatibility.embed (occupied step point) := map_smul _ _ _

def dualCoefficient (step : ℕ) (point : BasePoint) (index : Stage9DEF.Source.Index) : ℂ :=
  spinPairCoefficients (Gauge.upperDual step point) (Gauge.lowerDual step point) index.1 index.2

theorem dual_source_star (step : ℕ) (point : BasePoint) (index : Stage9DEF.Source.Index) :
    dualCoefficient step point index =
      2 * (spinScale : ℂ) * star (occupied step point (Stage9DEF.Compatibility.flip index)) := by
  rcases index with ⟨spin, color⟩
  fin_cases spin <;> fin_cases color <;>
    simp [dualCoefficient, occupied_formula, Stage9DEF.Compatibility.flip,
      Stage9DEF.Compatibility.spinFlip, spinPairCoefficients,
      Gauge.upperDual, Gauge.lowerDual, Gauge.upper, Gauge.lower, Stage9DEF.Source.phase_star] <;> ring

theorem dual_evaluation (step : ℕ) (point : BasePoint) (matter : DiracExteriorMatterCarrier) :
    (fieldAt step).conjugateMatter point matter =
      ∑ index : Stage9DEF.Source.Index,
        dualCoefficient step point index * Stage9DEF.Compatibility.coordinates matter index := by
  rw [Gauge.field_dual]
  simp only [spinPairDual, sourceColorDiracDual, Fintype.sum_prod_type,
    dualCoefficient, Stage9DEF.Compatibility.coordinates, LinearMap.coe_mk, AddHom.coe_mk]

theorem occupied_inner_self (step : ℕ) (point : BasePoint) :
    (∑ index : Stage9DEF.Source.Index,
      star (occupied step point index) * occupied step point index) = 1 := by
  simp only [Fintype.sum_prod_type, occupied_formula]
  simp [spinPairCoefficients, Fin.sum_univ_four, Fin.sum_univ_two, star_div₀]
  have upper := Stage9DEF.Source.phase_star_mul (phaseRate step) point
  have lower := Stage9DEF.Source.phase_star_mul (-phaseRate step) point
  change (starRingEnd ℂ) (phase (phaseRate step) point) * phase (phaseRate step) point = 1 at upper
  change (starRingEnd ℂ) (phase (-phaseRate step) point) * phase (-phaseRate step) point = 1 at lower
  linear_combination upper / 2 + lower / 2

theorem evaluation_normalized (step : ℕ) (point : BasePoint) :
    Stage9DEF.State.vectorEvaluation (occupied step point) 1 = 1 :=
  Stage9DEF.State.vectorEvaluation_one _ (occupied_inner_self step point)

theorem evaluation_density (step : ℕ) (point : BasePoint)
    (observable : Stage9DEF.Compatibility.Matrix8) :
    Stage9DEF.State.vectorEvaluation (occupied step point) observable =
      (Stage9DEF.State.pureMatrix (occupied step point) * observable).trace :=
  Stage9DEF.State.vectorEvaluation_eq_trace _ _

theorem action_response (step : ℕ) (point : BasePoint)
    (action : Module.End ℂ DiracExteriorMatterCarrier) :
    (fieldAt step).conjugateMatter point (action ((fieldAt step).matter point)) =
      4 * (spinScale : ℂ) * Stage9DEF.State.vectorEvaluation
        (occupied step point) (Stage9DEF.Compatibility.responseMatrix action) := by
  rw [matter_reconstruction, map_smul, dual_evaluation]
  simp only [map_smul, dual_source_star, Pi.smul_apply, smul_eq_mul]
  rw [show (∑ index : Stage9DEF.Source.Index,
      2 * (spinScale : ℂ) * star (occupied step point (Stage9DEF.Compatibility.flip index)) *
        (2 * Stage9DEF.Compatibility.coordinates
          (action (Stage9DEF.Compatibility.embed (occupied step point))) index)) =
      ∑ index : Stage9DEF.Source.Index,
      2 * (spinScale : ℂ) * star (occupied step point index) *
        (2 * Stage9DEF.Compatibility.coordinates
          (action (Stage9DEF.Compatibility.embed (occupied step point)))
          (Stage9DEF.Compatibility.flip index)) by
    simp [Fintype.sum_prod_type, Fin.sum_univ_four, Fin.sum_univ_two,
      Stage9DEF.Compatibility.flip, Stage9DEF.Compatibility.spinFlip]
    ring]
  change _ = 4 * (spinScale : ℂ) * ∑ index,
    star (occupied step point index) *
      (Stage9DEF.Compatibility.responseMatrix action *ᵥ occupied step point) index
  simp_rw [Stage9DEF.Compatibility.responseMatrix_mulVec]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  ring

theorem accepted_action (step : ℕ) (point : BasePoint)
    (action : Module.End ℂ DiracExteriorMatterCarrier) :
    ClassicalWorldAcceptance (sourceAt step) (fieldAt step) ∧
      (fieldAt step).conjugateMatter point (action ((fieldAt step).matter point)) =
        4 * (spinScale : ℂ) * Stage9DEF.State.vectorEvaluation
          (occupied step point) (Stage9DEF.Compatibility.responseMatrix action) :=
  ⟨accepted step, action_response step point action⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.SourceFamilyEvolution.Quantum
