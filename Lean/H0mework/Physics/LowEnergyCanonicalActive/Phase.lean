import H0mework.Physics.LowEnergyActiveGauge.Phase
import H0mework.Physics.LowEnergyQuantum.Preparation

/-! The original same-sided rotation preserves the existing canonical preparation relation. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.CanonicalActive
open ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair
open DiracCliffordRepresentation DiracExteriorMatterAction
open SU7ExteriorMatterRepresentation StageNineFullDiracAdjointMaterial
noncomputable section
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

private theorem internal_smul_left (coefficient : ℂ)
    (left right : SU7ExteriorSpinorMatterCarrier) :
    fullInternalPair (coefficient • left) right =
      star coefficient*fullInternalPair left right := by
  simp only [fullInternalPair,exteriorCoordinatePair,Prod.smul_fst,Prod.smul_snd,
    map_smul,Finsupp.smul_apply,smul_eq_mul,map_mul,starRingEnd_apply]
  simp only [mul_add,Finset.mul_sum,mul_assoc]

private theorem internal_smul_right (coefficient : ℂ)
    (left right : SU7ExteriorSpinorMatterCarrier) :
    fullInternalPair left (coefficient • right) =
      coefficient*fullInternalPair left right := by
  simp only [fullInternalPair,exteriorCoordinatePair,Prod.smul_fst,Prod.smul_snd,
    map_smul,Finsupp.smul_apply,smul_eq_mul]
  simp only [mul_add,Finset.mul_sum]
  apply congrArg₂ (·+·)
  · apply congrArg₂ (·+·)
    · apply Finset.sum_congr rfl
      intro index _
      ring
    · apply Finset.sum_congr rfl
      intro index _
      ring
  · apply Finset.sum_congr rfl
    intro index _
    ring

theorem original_phase_star (rate : ℝ) (point : BasePoint) :
    star (Stage9C.Material.SpinPair.phase rate point) =
      Stage9C.Material.SpinPair.phase (-rate) point := by
  change starRingEnd ℂ (Complex.exp _) = _
  rw [← Complex.exp_conj]
  simp [Stage9C.Material.SpinPair.phase]

/-- In the original phase convention both independent fields rotate on the same side. -/
theorem canonical_rotation (point : BasePoint) (matter : DiracExteriorMatterCarrier) :
    fullCanonicalDiracAdjoint (diracMatrixMatterAction (ActiveGauge.rotation point) matter) =
      (fullCanonicalDiracAdjoint matter).comp
        (diracMatrixMatterAction (ActiveGauge.rotation point)) := by
  apply LinearMap.ext
  intro test
  rw [LinearMap.comp_apply,fullCanonicalDiracAdjoint_evaluate,fullCanonicalDiracAdjoint_evaluate]
  simp [diracMatrixMatterAction,ActiveGauge.rotation,Matrix.diagonal_apply,
    internal_smul_left,internal_smul_right,
    upperPhase,lowerPhase,original_phase_star]

theorem scaled_canonical_rotation (point : BasePoint) (matter : DiracExteriorMatterCarrier) :
    ((spinScale : ℂ) • fullCanonicalDiracAdjoint matter).comp
        (diracMatrixMatterAction (ActiveGauge.rotation point)) =
      (spinScale : ℂ) • fullCanonicalDiracAdjoint
        (diracMatrixMatterAction (ActiveGauge.rotation point) matter) := by
  rw [canonical_rotation]
  rfl

end
end SaturationMonoid.PhysicsCore.LowEnergy.CanonicalActive
