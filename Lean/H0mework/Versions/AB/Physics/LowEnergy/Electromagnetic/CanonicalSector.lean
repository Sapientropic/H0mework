import H0mework.Versions.AB.Physics.MotherSource.ChargedPreparation.CanonicalParticle.Pair
import H0mework.Versions.AB.Physics.LowEnergyMixed.Degree

/-! The existing canonical external preparation kills the original Yukawa
for every scalar field. This is a source preparation identity, not a change
to the scalar configuration or to the independent dual. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace SaturationMonoid.PhysicsCore.LowEnergy.Electromagnetic.CanonicalSector
open ProofFreeRicherAnholonomicSource StageNineHolonomicField DiracExteriorMatterAction
open DiracCliffordRepresentation Stage9C.Material.SpinPair Stage9DEF Stage9DEF.Compatibility
open Stage10.ChargedPreparation.CanonicalParticle SU7ExteriorBreakingYukawa
open StageNineDiracDualYukawaSpinJurisdiction
noncomputable section

theorem upper_right_zero (values : Fin 4 → ℂ) :
    diracMatrixMatterAction rightChiralityProjector (embed (upperValues values)) = 0 := by
  funext spin
  fin_cases spin <;>
    simp [diracMatrixMatterAction, rightChiralityProjector, diracGammaFive,
      embed, sourceColorDiracMatter, upperValues, Fin.sum_univ_four, Fin.sum_univ_two]

theorem upper_yukawa_zero (scalar : ExteriorBreakingScalarCarrier) (values : Fin 4 → ℂ) :
    diracDualRightChiralYukawaAction scalar (embed (upperValues values)) = 0 := by
  rw [diracDualRightChiralYukawaAction, LinearMap.comp_apply, upper_right_zero, map_zero]

theorem canonical_preparation_yukawa_zero (scalar : ExteriorBreakingScalarCarrier)
    (point : BasePoint) (momentum : Fin 3 → ℝ) :
    diracDualRightChiralYukawaAction scalar
      (normalizedPreparation momentum (embed (Source.vector point))) = 0 := by
  rw [normalized_source]
  simp only [normalizedValues, values, map_smul, upperValues_smul]
  rw [upper_yukawa_zero, smul_zero, smul_zero]

theorem degreeTwo_degreeSix : MixedSymbol.degreeTwo.comp MixedSymbol.degreeSix = 0 := by
  apply LinearMap.ext
  intro field
  funext spin
  rfl

/-- Every temporal inverse or spin prefactor retains the original degree-six
output. This pays the other side of the canonical degree-two restriction. -/
theorem degreeTwo_spin_yukawa_zero (spin : DiracMatrix)
    (scalar : ExteriorBreakingScalarCarrier) :
    MixedSymbol.degreeTwo.comp ((diracMatrixMatterAction spin).comp
      (diracDualRightChiralYukawaAction scalar)) = 0 := by
  rw [← LinearMap.comp_assoc, MixedSymbol.degreeTwo_spin, LinearMap.comp_assoc]
  have output := congrArg (fun action => MixedSymbol.degreeTwo.comp action)
    (MixedSymbol.yukawa_output scalar)
  rw [← LinearMap.comp_assoc, degreeTwo_degreeSix, LinearMap.zero_comp] at output
  rw [← output, LinearMap.comp_zero]

end
end SaturationMonoid.PhysicsCore.LowEnergy.Electromagnetic.CanonicalSector
