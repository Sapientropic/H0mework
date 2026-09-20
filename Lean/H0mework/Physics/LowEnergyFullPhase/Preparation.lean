import H0mework.Physics.LowEnergyFullPhase.Operator

/-! The complete graded co-rotation preserves the same original canonical preparation. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullPhase
open ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair
open DiracCliffordRepresentation DiracExteriorMatterAction SU7ExteriorMatterRepresentation
open StageNineFullDiracAdjointMaterial
noncomputable section

private theorem internal_phase_transfer (six other : ℂ)
    (left right : SU7ExteriorSpinorMatterCarrier) :
    fullInternalPair (six • left.1,other • left.2.1,other • left.2.2) right =
      fullInternalPair left (star six • right.1,star other • right.2.1,star other • right.2.2) := by
  simp only [fullInternalPair,exteriorCoordinatePair,map_smul,Finsupp.smul_apply,
    smul_eq_mul,map_mul,starRingEnd_apply]
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

theorem canonical_preserved (point : BasePoint) (matter : DiracExteriorMatterCarrier) :
    fullCanonicalDiracAdjoint (primal point matter) =
      (fullCanonicalDiracAdjoint matter).comp (dual point) := by
  apply LinearMap.ext
  intro test
  rw [LinearMap.comp_apply,fullCanonicalDiracAdjoint_evaluate,fullCanonicalDiracAdjoint_evaluate]
  simp [primal,dual,phaseOperator,sixPrimalRate,sixDualRate,otherRate,
    internal_phase_transfer,CanonicalActive.original_phase_star]

theorem prepared_pair_preserved (point : BasePoint) (matter : DiracExteriorMatterCarrier) :
    ((spinScale : ℂ) • fullCanonicalDiracAdjoint matter).comp (dual point) =
      (spinScale : ℂ) • fullCanonicalDiracAdjoint (primal point matter) := by
  rw [canonical_preserved]
  rfl

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullPhase
