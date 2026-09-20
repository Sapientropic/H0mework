import H0mework.Physics.LowEnergyResponse.Yukawa
import H0mework.Physics.QuantumCompatibility.DualResponse

/-! Exact source quantum compression of the repaired Yukawa family.
This diagnoses the existing eight-dimensional reader, not the full quantum
content of the theory and not a replacement state or action. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Contact.Quantum
open DiracExteriorMatterAction SU7ExteriorBreakingYukawa
open StageNineDiracDualYukawaSpinJurisdiction Stage9DEF.Compatibility
open Stage9C.Material.SpinPair StageNineHolonomicField
open ProofFreeRicherAnholonomicSource
noncomputable section

theorem coordinates_yukawa (scalar : ExteriorBreakingScalarCarrier)
    (matter : DiracExteriorMatterCarrier) :
    coordinates (diracDualRightChiralYukawaAction scalar matter) = 0 := by
  funext index
  change (SU7ExteriorMatterRestriction.su7ExteriorBasis 2).repr
    ((diracDualRightChiralYukawaAction scalar matter index.1).2.1)
    (sourceColorDoubletIndex index.2) = 0
  rw [Response.Yukawa.output_degree_two_zero]
  simp

theorem compressed_yukawa (scalar : ExteriorBreakingScalarCarrier) :
    compression (diracDualRightChiralYukawaAction scalar) = 0 := by
  have zeroMap : coordinates.comp ((diracDualRightChiralYukawaAction scalar).comp embed) = 0 := by
    apply LinearMap.ext
    intro values
    exact coordinates_yukawa scalar (embed values)
  simp only [compression, zeroMap, map_zero]

theorem response_yukawa (scalar : ExteriorBreakingScalarCarrier) :
    responseMatrix (diracDualRightChiralYukawaAction scalar) = 0 := by
  ext row column
  change compression (diracDualRightChiralYukawaAction scalar) (flip row) column = 0
  rw [compressed_yukawa]
  rfl

theorem read_yukawa (point : BasePoint) (scalar : ExteriorBreakingScalarCarrier) :
    vectorRead point (responseMatrix (diracDualRightChiralYukawaAction scalar)) = 0 := by
  rw [response_yukawa]
  simp [vectorRead]

/-- A nonzero source operator is invisible to this particular compression. -/
theorem reader_not_faithful_on_yukawa :
    diracDualRightChiralYukawaAction exteriorBreakingScalar ≠ 0 ∧
    responseMatrix (diracDualRightChiralYukawaAction exteriorBreakingScalar) = 0 :=
  ⟨diracDualRightChiralYukawaAction_nonzero, response_yukawa _⟩

/-- Finite amplitude, arbitrary spacetime profile; no smallness premise. -/
theorem arbitrary_profile_invisible (profile : BasePoint → ExteriorBreakingScalarCarrier)
    (point : BasePoint) :
    actual.conjugateMatter point
      (diracDualRightChiralYukawaAction (profile point) (actual.matter point)) = 0 := by
  rw [actual_action_quantumResponse, read_yukawa, mul_zero]

end
end SaturationMonoid.PhysicsCore.LowEnergy.Contact.Quantum
