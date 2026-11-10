import H0mework.Versions.R7e4da746.Physics.YangMillsFlatQuantum.HistoryAlgebra
import H0mework.Versions.R7e4da746.Physics.CompositeSpectrum.Complement

/-! Actual curvature words commute with the complete repaired Yukawa action.
Spin commutation holds for every configuration; Yukawa commutation uses the
source's actual curvature and its own breaking scalar. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.YangMills.Ward.Pure

open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open DiracCliffordRepresentation DiracExteriorMatterAction
open SU7MotherLieAlgebra SU7MotherGaugeTheory SU7ExteriorBreakingYukawa
open StageNineExteriorMotherLieYukawaDerivation StageNineDiracDualYukawaSpinJurisdiction
open StageNineDynamicBreakingVacuum StageNineEnrichedProofFreeSource
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionVariationDensity
open Stage9C.Material.SpinPair Stage9DEF Flat.Quantum.History

noncomputable section

private theorem word_commutes (configuration : StageNineHolonomicConfiguration) (action : Mother)
    (generators : ∀ label, Commute action (field configuration label)) (P : Polynomial) :
    Commute action (evaluate configuration P) := by
  induction P using FreeAlgebra.induction ℂ Label with
  | grade0 c =>
    rw [AlgHom.commutes]
    exact Algebra.commute_algebraMap_right c action
  | grade1 label =>
    rw [evaluate_generator]
    exact generators label
  | mul P Q hP hQ =>
    rw [map_mul]
    exact hP.mul_right hQ
  | add P Q hP hQ =>
    rw [map_add]
    exact hP.add_right hQ

theorem source_word_spin (configuration : StageNineHolonomicConfiguration)
    (matrix : DiracMatrix) (P : Polynomial) :
    Commute (diracMatrixMatterAction matrix) (evaluate configuration P) := by
  apply word_commutes configuration _ _ P
  intro label
  have internal : Commute (diracMatrixMatterAction matrix)
      (diracExteriorMotherLieAction
        (p286LieBlockEmbed (holonomicGaugeCurvature configuration label.1 label.2))) :=
    diracMatrixMatterAction_commutes_internal matrix _
  exact internal.smul_right Complex.I

private theorem generator_yukawa (point : BasePoint) (axis : Fin 3) :
    Commute (Compatibility.yukawaAction point)
      (diracExteriorMotherLieAction (p286LieBlockEmbed (sourceColorP286Generator axis))) := by
  have scalar : exteriorMotherLieAction 4 (p286LieBlockEmbed (sourceColorP286Generator axis))
      (Compatibility.actualVacuum point) = 0 := by
    rw [Stage10.Recovery.stageOneThroughTenClosure.final.stageNine.compatibility.vacuum point,
      ← positive_sourceGeneratedVacuumBase]
    exact Stage10.GaugeSpectrum.vacuumMotherAction_zero axis
  apply Commute.symm
  apply LinearMap.ext
  intro v
  change diracExteriorMotherLieAction _ (Compatibility.yukawaAction point v) =
    Compatibility.yukawaAction point (diracExteriorMotherLieAction _ v)
  unfold Compatibility.yukawaAction diracDualRightChiralYukawaAction
  simp only [LinearMap.comp_apply]
  rw [diracExteriorYukawaInternalAction_motherLieAction, scalar]
  have zero (x : DiracExteriorMatterCarrier) : diracExteriorYukawaInternalAction 0 x = 0 := by
    funext spin
    change (exteriorYukawaMassMap 0 (x spin).2.1, (0, 0)) = 0
    simp [exteriorYukawaMassMap]
  rw [zero, zero_add]
  exact congrArg (diracExteriorYukawaInternalAction (Compatibility.actualVacuum point))
    (LinearMap.congr_fun (diracMatrixMatterAction_commutes_internal rightChiralityProjector
      (exteriorSpinorMotherLieAction (p286LieBlockEmbed (sourceColorP286Generator axis)))) v).symm

private theorem field_yukawa (point : BasePoint) (label : Label) :
    Commute (Compatibility.yukawaAction point) (field actual label) := by
  rcases label with ⟨location, pair⟩
  apply Commute.smul_right
  rw [actual_gaugeCurvature]
  have zero : Commute (Compatibility.yukawaAction point)
      (diracExteriorMotherLieAction (p286LieBlockEmbed 0)) := by
    have zeroAction : diracExteriorMotherLieAction 0 = 0 :=
      LinearMap.ext diracExteriorMotherLieAction_zero_matrix
    rw [p286LieBlockEmbed_zero, zeroAction]
    exact Commute.zero_right _
  have magnetic (axis : Fin 3) : Commute (Compatibility.yukawaAction point)
      (diracExteriorMotherLieAction
        (p286LieBlockEmbed (-(gaugeScale ^ 2) • sourceColorP286Generator axis))) := by
    rw [p286LieBlockEmbed_real_smul, diracExteriorMotherLieAction_real_smul]
    exact (generator_yukawa point axis).smul_right _
  fin_cases pair
  · exact zero
  · exact zero
  · exact zero
  · exact magnetic 0
  · exact magnetic 1
  · exact magnetic 2

theorem source_word_yukawa (point : BasePoint) (P : Polynomial) :
    Commute (Compatibility.yukawaAction point) (evaluate actual P) :=
  word_commutes actual _ (field_yukawa point) P

end
end SaturationMonoid.PhysicsCore.YangMills.Ward.Pure
