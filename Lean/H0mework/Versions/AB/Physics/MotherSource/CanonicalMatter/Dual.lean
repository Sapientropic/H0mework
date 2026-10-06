import H0mework.Versions.AB.Physics.MotherSource.CanonicalMatter.Time
import H0mework.Versions.AB.Physics.MotherSource.ChargedPreparation.Positive

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
namespace SaturationMonoid.PhysicsCore.Stage10.CanonicalMatter
open ProofFreeRicherAnholonomicSource StageNineHolonomicField DiracExteriorMatterAction
open DiracCliffordRepresentation Stage9C.Material.SpinPair Stage9DEF Stage9DEF.Compatibility
open YangMills.FullPairing SU7MotherLieAlgebra SU7MotherGaugeTheory
open scoped Matrix InnerProductSpace
noncomputable section

def phaseInverse : Mother := -diracMatrixMatterAction diracGammaZero

theorem phase_inverse_source (matter : DiracExteriorMatterCarrier) :
    phaseInverse (diracMatrixMatterAction diracGammaZero matter) = matter := by
  funext spin
  fin_cases spin <;> simp [phaseInverse, diracMatrixMatterAction, diracGammaZero, Fin.sum_univ_four]
  all_goals module

/-- The inverse of the action's normalized temporal principal closes the dual transport. -/
def canonicalDual (preparation : Mother) : Mother :=
  flipMatter.comp ((fromOperator (operator preparation).adjoint).comp phaseInverse)

theorem canonical_paired_time (preparation : Mother) (matter : DiracExteriorMatterCarrier) :
    canonicalDual preparation (diracMatrixMatterAction diracGammaZero (preparation matter)) =
      pairedMother preparation preparation matter := by
  simp only [canonicalDual, LinearMap.comp_apply, phase_inverse_source]
  simp [pairedMother, fromOperator, operator]

theorem canonical_time_gram (point : BasePoint) (preparation : Mother) :
    LowEnergy.FullQuantum.normalizedMomentum actual point
      ((actual.conjugateMatter point).comp (canonicalDual preparation))
      (preparation (actual.matter point)) =
        4*(spinScale : ℂ)*inner ℂ (operator preparation (YangMills.FullPairing.prepared point))
          (operator preparation (YangMills.FullPairing.prepared point)) := by
  rw [native_time_pair, LinearMap.comp_apply, canonical_paired_time, dual_gram]

def canonicalCharge : Mother :=
  phaseInverse.comp (currentAction 0 HyperchargeResponse.chargeDirection)

theorem canonical_charge_source (matter : DiracExteriorMatterCarrier) :
    canonicalCharge matter = Complex.I •
      diracExteriorMotherLieAction (p286LieBlockEmbed HyperchargeResponse.chargeDirection) matter := by
  simp only [canonicalCharge, LinearMap.comp_apply, currentAction, LinearMap.smul_apply, diracGamma,
    Matrix.cons_val_zero, phaseInverse, LinearMap.neg_apply, map_smul]
  change Complex.I • phaseInverse (diracMatrixMatterAction diracGammaZero
    (diracExteriorMotherLieAction (p286LieBlockEmbed HyperchargeResponse.chargeDirection) matter)) = _
  rw [phase_inverse_source]

theorem canonical_charge_coordinates (values : Source.Index → ℂ) (index : Source.Index) :
    coordinates (canonicalCharge (embed values)) index = -values index := by
  rw [canonical_charge_source]
  rcases index with ⟨spin,color⟩
  change sourceColorDoubletDual color
    ((Complex.I • diracExteriorMotherLieAction (p286LieBlockEmbed HyperchargeResponse.chargeDirection)
      (sourceColorDiracMatter (fun s c => values (s,c)))) spin) = _
  simp only [Pi.smul_apply, map_smul, smul_eq_mul, sourceColorDoubletDual_motherAction]
  fin_cases color <;>
    simp [HyperchargeResponse.chargeDirection, hyperchargeGenerator, Fin.castLE]
  all_goals ring_nf; simp [Complex.I_sq]

theorem canonical_current_gram (point : BasePoint) (preparation : Mother) :
    actual.conjugateMatter point
      (canonicalDual preparation (currentAction 0 HyperchargeResponse.chargeDirection
        (preparation (actual.matter point)))) =
      4*(spinScale : ℂ)*inner ℂ (operator preparation (YangMills.FullPairing.prepared point))
        (operator (canonicalCharge.comp preparation) (YangMills.FullPairing.prepared point)) := by
  have paired (matter : DiracExteriorMatterCarrier) :
      canonicalDual preparation (currentAction 0 HyperchargeResponse.chargeDirection (preparation matter)) =
        pairedMother preparation (canonicalCharge.comp preparation) matter := by
    simp [canonicalDual, pairedMother, canonicalCharge, fromOperator, operator]
  rw [paired, dual_gram]

theorem source_upper_time (point : BasePoint) :
    LowEnergy.FullQuantum.normalizedMomentum actual point
      ((actual.conjugateMatter point).comp (canonicalDual ChargedPreparation.Positive.preparation))
      (ChargedPreparation.Positive.preparation (actual.matter point)) = 4*(spinScale : ℂ) := by
  rw [canonical_time_gram, ChargedPreparation.Positive.full_prepared, inner_embed, coordinates_embed,
    ChargedPreparation.Positive.vector_norm, mul_one]

theorem source_upper_current (point : BasePoint) :
    actual.conjugateMatter point
      (canonicalDual ChargedPreparation.Positive.preparation
        (currentAction 0 HyperchargeResponse.chargeDirection
          (ChargedPreparation.Positive.preparation (actual.matter point)))) = -4*(spinScale : ℂ) := by
  rw [canonical_current_gram]
  have composed : operator (canonicalCharge.comp ChargedPreparation.Positive.preparation)
      (YangMills.FullPairing.prepared point) =
        operator canonicalCharge (operator ChargedPreparation.Positive.preparation (YangMills.FullPairing.prepared point)) := by
    simp [YangMills.FullPairing.prepared, operator_coordinates]
  rw [composed, ChargedPreparation.Positive.full_prepared, operator_coordinates, inner_embed]
  simp_rw [canonical_charge_coordinates, mul_neg]
  rw [Finset.sum_neg_distrib, ChargedPreparation.Positive.vector_norm]
  ring

theorem rejects_old_flip_dual : canonicalDual ChargedPreparation.Positive.preparation ≠
    ChargedPreparation.Positive.dualPreparation := by
  intro same
  have observed := source_upper_current 0
  rw [same, ChargedPreparation.Positive.classical_current] at observed
  have real := congrArg Complex.re observed
  norm_num at real
  nlinarith [spinScale_pos]

end
end SaturationMonoid.PhysicsCore.Stage10.CanonicalMatter
