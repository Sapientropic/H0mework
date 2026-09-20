import H0mework.Physics.Admission.ResidualLimitScalarBalanceClosure
import H0mework.Physics.GaugeStanding.LieRepresentation
import H0mework.Physics.FixedJoint.FixedJointResidual

/-! The original color/hypercharge source probe and the color-mixed partner
form one doublet. The existing source color generators fix the exact vacuum. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair

open DiracCliffordRepresentation DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource StageNineGlobalIntegratedAction StageNineHolonomicField
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionVariationDensity
open StageNineP286LinkedActiveLieRepresentation StageNineResidualLimitScalarBalanceClosure
open StageNineDiracDualYukawaSpinJurisdiction
open SU7ExteriorBreakingYukawa SU7ExteriorMatterGaugeCovariantJet SU7ExteriorMatterRestriction
open SU7ExteriorMatterRepresentation
open SU7ExteriorYukawaMassSpectrum SU7MotherLieAlgebra SU7MotherGaugeTheory

noncomputable section

def sourceColorDoubletIndex (state : Fin 2) : ExteriorBasisIndex 2 :=
  ⟨{Sum.inl (state.castLE (by decide)), hyperPlusIndex}, by
    change ({Sum.inl (state.castLE (by decide)), hyperPlusIndex} : Finset SU7MotherIndex).card = 2
    simp [hyperPlusIndex]⟩

def sourceColorDoubletMatter (state : Fin 2) : SU7ExteriorSpinorMatterCarrier :=
  (0, su7ExteriorBasis 2 (sourceColorDoubletIndex state), 0)

def sourceColorDoubletDual (state : Fin 2) : Module.Dual ℂ SU7ExteriorSpinorMatterCarrier where
  toFun matter := (su7ExteriorBasis 2).repr matter.2.1 (sourceColorDoubletIndex state)
  map_add' := by intros; simp
  map_smul' := by intros; simp

def sourceColorDiracMatter (coefficients : DiracSpinorIndex → Fin 2 → ℂ) : DiracExteriorMatterCarrier :=
  fun spin => ∑ state, coefficients spin state • sourceColorDoubletMatter state

theorem sourceColorDoublet_original : sourceColorDoubletMatter 0 = p286HyperchargeMatterProbe := rfl

def sourceColorP286Generator : Fin 3 → P286LieBlockData
  | 0 => (1 / 4 : ℝ) • p286LieBracket (colorCartanGenerator, 0, 0) (colorMixingGenerator, 0, 0)
  | 1 => (1 / 2 : ℝ) • (colorMixingGenerator, 0, 0)
  | 2 => (1 / 2 : ℝ) • (colorCartanGenerator, 0, 0)

def sourceColorPauli : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => !![0, Complex.I/2; Complex.I/2, 0]
  | 1 => !![0, 1/2; -1/2, 0]
  | 2 => !![Complex.I/2, 0; 0, -Complex.I/2]

theorem sourceColorP286Generator_topLeft (direction : Fin 3) (row column : Fin 2) :
    (sourceColorP286Generator direction).1.val (row.castLE (by decide)) (column.castLE (by decide)) =
      sourceColorPauli direction row column := by
  fin_cases direction <;> fin_cases row <;> fin_cases column <;>
    norm_num [sourceColorP286Generator, sourceColorPauli, p286LieBracket, suLieBracket,
      colorCartanGenerator, colorCartanRaw, colorMixingGenerator, colorMixingRaw,
      Matrix.mul_apply, Fin.sum_univ_three, Fin.castLE]
  all_goals ring

private theorem sourceColorCartan_vacuum_zero :
    scalarMotherLieAction colorCartanMotherDirection
      (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) = 0 := by
  unfold scalarMotherLieAction sourceGeneratedVacuumCoordinates
  rw [scalarCoordinateEquiv.symm_apply_apply, positive_sourceGeneratedVacuumBase,
    finiteGenerationJointBreakingScalar_colorCartan_action_zero, map_zero]

private theorem sourceColorMixing_vacuum_zero :
    scalarMotherLieAction colorMixingMotherDirection
      (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) = 0 := by
  unfold scalarMotherLieAction sourceGeneratedVacuumCoordinates
  rw [scalarCoordinateEquiv.symm_apply_apply, positive_sourceGeneratedVacuumBase,
    finiteGenerationJointBreakingScalar_colorMixing_action_zero, map_zero]

theorem sourceColorP286Generator_vacuum_zero (direction : Fin 3) :
    scalarMotherLieAction (p286LieBlockEmbed (sourceColorP286Generator direction))
      (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) = 0 := by
  fin_cases direction <;> simp only [sourceColorP286Generator]
  · rw [p286LieBlockEmbed_real_smul, p286LieBlockEmbed_bracket,
      scalarMotherLieAction_real_smul, scalarMotherLieAction_bracket]
    change (1 / 4 : ℝ) •
      (scalarMotherLieAction colorCartanMotherDirection
          (scalarMotherLieAction colorMixingMotherDirection _) -
        scalarMotherLieAction colorMixingMotherDirection
          (scalarMotherLieAction colorCartanMotherDirection _)) = 0
    rw [sourceColorCartan_vacuum_zero, sourceColorMixing_vacuum_zero]
    simp [scalarMotherLieAction]
  · rw [p286LieBlockEmbed_real_smul, scalarMotherLieAction_real_smul]
    change (1 / 2 : ℝ) • scalarMotherLieAction colorMixingMotherDirection _ = 0
    rw [sourceColorMixing_vacuum_zero, smul_zero]
  · rw [p286LieBlockEmbed_real_smul, scalarMotherLieAction_real_smul]
    change (1 / 2 : ℝ) • scalarMotherLieAction colorCartanMotherDirection _ = 0
    rw [sourceColorCartan_vacuum_zero, smul_zero]

theorem sourceColorDoublet_yukawa_zero (state : Fin 2) :
    exteriorYukawaMassMap (sourceGeneratedVacuumBase positiveSmoothUnifiedSource)
      (su7ExteriorBasis 2 (sourceColorDoubletIndex state)) = 0 := by
  rw [positive_sourceGeneratedVacuumBase]
  have overlap (output input : Fin 2) :
      ¬ Disjoint (sourceColorDoubletIndex state).1 (finiteGenerationScalarIndex output input).1 := by
    fin_cases state <;> fin_cases output <;> fin_cases input <;> decide
  simp [finiteGenerationJointBreakingScalar, Fin.sum_univ_two,
    exteriorYukawaMassMap_add_breaking, finiteGenerationBreakingTensor,
    exteriorYukawaMassMap_basisPair_of_not_disjoint, overlap]

theorem sourceColorDoublet_internalYukawa_zero (state : Fin 2) :
    exteriorYukawaInternalAction (sourceGeneratedVacuumBase positiveSmoothUnifiedSource)
      (sourceColorDoubletMatter state) = 0 := by
  change (exteriorYukawaMassMap (sourceGeneratedVacuumBase positiveSmoothUnifiedSource)
    (su7ExteriorBasis 2 (sourceColorDoubletIndex state)), (0, 0)) = 0
  rw [sourceColorDoublet_yukawa_zero]
  rfl

end
end SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair
