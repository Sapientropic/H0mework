import H0mework.Versions.AB.Physics.LowEnergyResponse.Yukawa
import H0mework.Physics.SpinPair.ColorAction

/-! The full P286 color triplet containing the original occupied doublet. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.ActiveSector
open DiracCliffordRepresentation DiracExteriorMatterAction
open SU7MotherLieAlgebra SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction
open SU7ExteriorBreakingYukawa SU7ExteriorYukawaMassSpectrum
open StageNineDiracDualYukawaSpinJurisdiction Stage9C.Material.SpinPair
open StageNineEnrichedProofFreeSource StageNineDynamicBreakingVacuum
open ProofFreeRicherAnholonomicSource GaugeProjection.ConcreteBlockDiagonal
noncomputable section
local instance : LinearOrder SU7MotherIndex :=
  LinearOrder.lift' smBlockIndexEquivFin7 smBlockIndexEquivFin7.injective

def colorTripletIndex (color : Fin 3) : ExteriorBasisIndex 2 :=
  ⟨{Sum.inl color, hyperPlusIndex}, by
    change ({Sum.inl color, hyperPlusIndex} : Finset SU7MotherIndex).card = 2
    simp [hyperPlusIndex]⟩

def colorTripletMatter (color : Fin 3) : SU7ExteriorSpinorMatterCarrier :=
  (0, su7ExteriorBasis 2 (colorTripletIndex color), 0)

def tripletMatter (coefficient : DiracSpinorIndex → Fin 3 → ℂ) : DiracExteriorMatterCarrier :=
  fun spin => ∑ color, coefficient spin color • colorTripletMatter color

theorem colorTriplet_original (state : Fin 2) :
    colorTripletMatter (state.castLE (by decide)) = sourceColorDoubletMatter state := rfl

theorem colorTriplet_yukawa_zero (color : Fin 3) :
    exteriorYukawaMassMap (sourceGeneratedVacuumBase positiveSmoothUnifiedSource)
      (su7ExteriorBasis 2 (colorTripletIndex color)) = 0 := by
  rw [positive_sourceGeneratedVacuumBase]
  have overlap (output input : Fin 2) :
      ¬ Disjoint (colorTripletIndex color).1 (finiteGenerationScalarIndex output input).1 := by
    fin_cases color <;> fin_cases output <;> fin_cases input <;> decide
  simp [finiteGenerationJointBreakingScalar, Fin.sum_univ_two,
    exteriorYukawaMassMap_add_breaking, finiteGenerationBreakingTensor,
    exteriorYukawaMassMap_basisPair_of_not_disjoint, overlap]

theorem colorTriplet_internal_yukawa_zero (color : Fin 3) :
    exteriorYukawaInternalAction (sourceGeneratedVacuumBase positiveSmoothUnifiedSource)
      (colorTripletMatter color) = 0 := by
  change (exteriorYukawaMassMap (sourceGeneratedVacuumBase positiveSmoothUnifiedSource)
    (su7ExteriorBasis 2 (colorTripletIndex color)), (0, 0)) = 0
  rw [colorTriplet_yukawa_zero]
  rfl

/-- The source Y vanishes on every spin/color coefficient in the whole triplet. -/
theorem triplet_yukawa_zero (coefficient : DiracSpinorIndex → Fin 3 → ℂ) :
    diracDualRightChiralYukawaAction (sourceGeneratedVacuumBase positiveSmoothUnifiedSource)
      (tripletMatter coefficient) = 0 := by
  unfold diracDualRightChiralYukawaAction
  rw [LinearMap.comp_apply]
  funext spin
  change exteriorYukawaInternalAction (sourceGeneratedVacuumBase positiveSmoothUnifiedSource)
    (∑ other, rightChiralityProjector spin other •
      (∑ color, coefficient other color • colorTripletMatter color)) = 0
  simp only [map_sum, map_smul, colorTriplet_internal_yukawa_zero, smul_zero,
    Finset.sum_const_zero]

theorem triplet_spin_action (matrix : DiracMatrix)
    (coefficient : DiracSpinorIndex → Fin 3 → ℂ) :
    diracMatrixMatterAction matrix (tripletMatter coefficient) =
      tripletMatter (fun spin color => ∑ other, matrix spin other * coefficient other color) := by
  funext spin
  change (∑ other, matrix spin other • ∑ color, coefficient other color • colorTripletMatter color) =
    ∑ color, (∑ other, matrix spin other * coefficient other color) • colorTripletMatter color
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]

def originalTripletCoefficients (upper lower : ℂ) : DiracSpinorIndex → Fin 3 → ℂ :=
  !![0,upper,0; -upper,0,0; 0,lower,0; -lower,0,0]

theorem original_matter_triplet (upper lower : ℂ) :
    spinPairMatter upper lower = tripletMatter (originalTripletCoefficients upper lower) := by
  funext spin
  fin_cases spin <;>
    simp [spinPairMatter, sourceColorDiracMatter, spinPairCoefficients,
      tripletMatter, originalTripletCoefficients, Fin.sum_univ_two, Fin.sum_univ_three,
      sourceColorDoubletMatter, sourceColorDoubletIndex, colorTripletMatter, colorTripletIndex]

end
end SaturationMonoid.PhysicsCore.LowEnergy.ActiveSector
