import H0mework.Versions.AB.Physics.LowEnergyContact.Quantum
import H0mework.Versions.AB.Physics.LowEnergyResponse.MixedWitness

/-! A source-generated return test detects a mixed Yukawa output whose
original eight-dimensional compression is zero. This is a response operator,
not an added term in the action or a newly installed experimental device. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Contact.ReturnChannel
open DiracExteriorMatterAction SU7ExteriorBreakingYukawa
open StageNineDiracDualYukawaSpinJurisdiction Stage9DEF.Compatibility
open Stage9C.Material.SpinPair StageNineHolonomicField
open ProofFreeRicherAnholonomicSource Response.MixedWitness
noncomputable section

def prepared : DiracExteriorMatterCarrier := actual.matter 0

def returnMap : Module.End ℂ DiracExteriorMatterCarrier where
  toFun matter := outputDual matter • prepared
  map_add' := by intros; simp [map_add, add_smul]
  map_smul' := by intros; simp [map_smul, smul_smul]

def detectedAction : Module.End ℂ DiracExteriorMatterCarrier :=
  returnMap.comp (diracDualRightChiralYukawaAction scalarDirection)

def amplitude : ℂ := outputDual
  (diracDualRightChiralYukawaAction scalarDirection prepared)

theorem amplitude_nonzero : amplitude ≠ 0 := by
  intro zero
  apply mixed_channel_nonzero
  change amplitude.re = 0
  rw [zero]
  rfl

theorem detected_on_prepared : detectedAction prepared = amplitude • prepared := rfl

theorem original_pairing : actual.conjugateMatter 0 prepared = 4 * (spinScale : ℂ) := by
  rw [prepared, actual_matter, actual_conjugateMatter]
  simp only [upperDualPhase, lowerDualPhase, upperPhase, lowerPhase, phase_zero, mul_one]
  change (∑ spin, ∑ state, spinPairCoefficients (spinScale : ℂ) (spinScale : ℂ) spin state *
    sourceColorDoubletDual state (sourceColorDiracMatter (spinPairCoefficients 1 1) spin)) = _
  simp only [sourceColorDoubletDual_diracMatter]
  simp [spinPairCoefficients, Fin.sum_univ_four, Fin.sum_univ_two]
  ring


theorem detected_pairing : actual.conjugateMatter 0 (detectedAction prepared) =
    amplitude * (4 * (spinScale : ℂ)) := by
  rw [detected_on_prepared, map_smul, original_pairing]
  rfl

theorem detected_read_nonzero : vectorRead 0 (responseMatrix detectedAction) ≠ 0 := by
  intro zero
  have response := actual_action_quantumResponse 0 detectedAction
  change actual.conjugateMatter 0 (detectedAction prepared) = _ at response
  rw [detected_pairing, zero, mul_zero] at response
  have factor : (4 * (spinScale : ℂ)) ≠ 0 :=
    mul_ne_zero (by norm_num) (by exact_mod_cast ne_of_gt spinScale_pos)
  exact mul_ne_zero amplitude_nonzero factor response

theorem invisible_factor_visible_composite :
    responseMatrix (diracDualRightChiralYukawaAction scalarDirection) = 0 ∧
    vectorRead 0 (responseMatrix
      (returnMap.comp (diracDualRightChiralYukawaAction scalarDirection))) ≠ 0 :=
  ⟨Quantum.response_yukawa scalarDirection, detected_read_nonzero⟩

end
end SaturationMonoid.PhysicsCore.LowEnergy.Contact.ReturnChannel
