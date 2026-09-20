import H0mework.Physics.SpinPair.ColorAction

/-! The two occupied color states are closed under the source SU2 generators.
The second state is the original source mixing action on the first. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair

open DiracExteriorMatterAction ProofFreeRicherAnholonomicSource
open StageNineGlobalIntegratedAction StageNineHolonomicField
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionVariationDensity
open StageNineResidualLimitScalarBalanceClosure StageNineExteriorMotherLieRepresentation
open StageNineP286LinkedActiveLieRepresentation
open SU7ExteriorBreakingYukawa SU7ExteriorMatterGaugeCovariantJet SU7ExteriorMatterRestriction
open SU7ExteriorMatterRepresentation SU7MotherLieAlgebra SU7MotherGaugeTheory

noncomputable section

private theorem doubletBasis_lieSlots (matrix : SU7MotherLieMatrix) (state : Fin 2) :
    exteriorMotherLieAction 2 matrix (su7ExteriorBasis 2 (sourceColorDoubletIndex state)) =
      (exteriorPower.ιMulti ℂ 2)
        ![fundamentalMotherLieAction matrix
            (su7FundamentalBasis (Sum.inl (state.castLE (by decide)))), su7FundamentalBasis hyperPlusIndex] +
      (exteriorPower.ιMulti ℂ 2)
        ![su7FundamentalBasis (Sum.inl (state.castLE (by decide))),
          fundamentalMotherLieAction matrix (su7FundamentalBasis hyperPlusIndex)] := by
  rw [sourceColorDoublet_basis_wedge, exteriorMotherLieAction_eq_slotDerivedAction,
    exteriorSlotDerivedAction_apply_ιMulti, Fin.sum_univ_two]
  congr 1

private theorem wedge_second_zero (vector : SU7FundamentalCarrier) :
    (exteriorPower.ιMulti ℂ 2) ![vector, 0] = 0 :=
  (exteriorPower.ιMulti ℂ 2).map_coord_zero (1 : Fin 2) rfl

private theorem wedge_first_neg (first second : SU7FundamentalCarrier) :
    (exteriorPower.ιMulti ℂ 2) ![-first, second] =
      -(exteriorPower.ιMulti ℂ 2) ![first, second] := by
  rw [show -first = (-1 : ℂ) • first by simp, AlternatingMap.map_vecCons_smul, neg_one_smul]

private theorem doubletBasis_colorCartan (state : Fin 2) :
    exteriorMotherLieAction 2 colorCartanMotherDirection (su7ExteriorBasis 2 (sourceColorDoubletIndex state)) =
      (if state = 0 then Complex.I else -Complex.I) • su7ExteriorBasis 2 (sourceColorDoubletIndex state) := by
  rw [doubletBasis_lieSlots, sourceColorDoublet_basis_wedge]
  fin_cases state <;>
    simp [fundamentalColorCartan_basis, colorZeroIndex, colorOneIndex, hyperPlusIndex, Fin.castLE,
      AlternatingMap.map_vecCons_smul, wedge_second_zero, wedge_first_neg]
  all_goals module

private theorem doubletBasis_colorMixing (state : Fin 2) :
    exteriorMotherLieAction 2 colorMixingMotherDirection (su7ExteriorBasis 2 (sourceColorDoubletIndex state)) =
      if state = 0 then -su7ExteriorBasis 2 (sourceColorDoubletIndex 1)
      else su7ExteriorBasis 2 (sourceColorDoubletIndex 0) := by
  rw [doubletBasis_lieSlots]
  fin_cases state <;>
    simp [fundamentalColorMixing_basis, colorZeroIndex, colorOneIndex, hyperPlusIndex, Fin.castLE,
      sourceColorDoublet_basis_wedge, wedge_second_zero, wedge_first_neg]

theorem sourceColorDoublet_colorCartan (state : Fin 2) :
    exteriorSpinorMotherLieAction colorCartanMotherDirection (sourceColorDoubletMatter state) =
      (if state = 0 then Complex.I else -Complex.I) • sourceColorDoubletMatter state := by
  change (exteriorMotherLieAction 6 _ 0,
    exteriorMotherLieAction 2 _ (su7ExteriorBasis 2 (sourceColorDoubletIndex state)), exteriorMotherLieAction 4 _ 0) = _
  rw [map_zero, map_zero, doubletBasis_colorCartan]
  fin_cases state <;> simp [sourceColorDoubletMatter]

theorem sourceColorDoublet_colorMixing (state : Fin 2) :
    exteriorSpinorMotherLieAction colorMixingMotherDirection (sourceColorDoubletMatter state) =
      if state = 0 then -sourceColorDoubletMatter 1 else sourceColorDoubletMatter 0 := by
  change (exteriorMotherLieAction 6 _ 0,
    exteriorMotherLieAction 2 _ (su7ExteriorBasis 2 (sourceColorDoubletIndex state)), exteriorMotherLieAction 4 _ 0) = _
  rw [map_zero, map_zero, doubletBasis_colorMixing]
  fin_cases state <;> simp [sourceColorDoubletMatter]

theorem sourceColorDoublet_generatedFromOriginal :
    sourceColorDoubletMatter 1 =
      -exteriorSpinorMotherLieAction colorMixingMotherDirection p286HyperchargeMatterProbe := by
  rw [← sourceColorDoublet_original, sourceColorDoublet_colorMixing]
  simp

theorem sourceColorDoublet_generatorAction (direction : Fin 3) (state : Fin 2) :
    exteriorSpinorMotherLieAction (p286LieBlockEmbed (sourceColorP286Generator direction))
      (sourceColorDoubletMatter state) =
      ∑ output : Fin 2, sourceColorPauli direction output state • sourceColorDoubletMatter output := by
  fin_cases direction <;> simp only [sourceColorP286Generator, p286LieBlockEmbed_real_smul]
  · rw [p286LieBlockEmbed_bracket, exteriorSpinorMotherLieAction_real_smul,
      LinearMap.smul_apply, exteriorSpinorMotherLieAction_bracket,
      LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply]
    change (((1 / 4 : ℝ) : ℂ)) •
      (exteriorSpinorMotherLieAction colorCartanMotherDirection
          (exteriorSpinorMotherLieAction colorMixingMotherDirection (sourceColorDoubletMatter state)) -
        exteriorSpinorMotherLieAction colorMixingMotherDirection
          (exteriorSpinorMotherLieAction colorCartanMotherDirection (sourceColorDoubletMatter state))) = _
    fin_cases state <;>
      simp [sourceColorDoublet_colorCartan, sourceColorDoublet_colorMixing,
        sourceColorPauli, Fin.sum_univ_two, smul_add, smul_sub, smul_smul] <;> module
  · rw [exteriorSpinorMotherLieAction_real_smul, LinearMap.smul_apply]
    change (((1 / 2 : ℝ) : ℂ)) • exteriorSpinorMotherLieAction colorMixingMotherDirection
      (sourceColorDoubletMatter state) = _
    fin_cases state <;>
      simp [sourceColorDoublet_colorMixing, sourceColorPauli, Fin.sum_univ_two]
    all_goals module
  · rw [exteriorSpinorMotherLieAction_real_smul, LinearMap.smul_apply]
    change (((1 / 2 : ℝ) : ℂ)) • exteriorSpinorMotherLieAction colorCartanMotherDirection
      (sourceColorDoubletMatter state) = _
    fin_cases state <;>
      simp [sourceColorDoublet_colorCartan, sourceColorPauli, Fin.sum_univ_two, smul_smul] <;> module

end
end SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair
