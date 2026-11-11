import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusRActionSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.TotalSource.BFiniteResidualSource

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRJointMobiusStrictSource
open Complex MeasureTheory Set BurnolPhysicalState OriginalRieszSource
open OriginalKCrossParameterRAdjointSource OriginalKDirectRCofinalOutsideVolterraSource
open scoped InnerProductSpace
open private sourceResidualNe from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.TotalSource.BFiniteResidualSource
namespace D
export OriginalWholeDebtRJointMobiusRActionSource
  (sourceInput sourceNext actual_source_effect actual_complete_update actual_programme_energy actual_effect_zero_iff)
end D
namespace U
export OriginalWholeDebtRJointMobiusUnitSource (sourceRaw responseRaw response actual_raw actual_programme_price)
end U
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "outside" => OriginalKCombPhysicalAction.physicalRemainder

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "programme" => OriginalNextEndpointProgramme.programmePrice c (Real.log stageZeroSonineQ)

/-- The same original source's fixed-shift rigidity pays this coefficient; no target enters the R constructor. -/
theorem actual_programme_ne_zero : programme ≠ 0 := by
  intro zero
  apply sourceResidualNe observation nontrivial half
  rw [installedOriginalKReceiptAt_eq_source]
  change burnolPaFixedShiftResidual c observation.mathlibZero = 0
  rw [OriginalNextEndpointProgramme.original_fixedResidual_programme observation nontrivial half]
  exact zero

theorem actual_effect_ne_zero : outside (D.sourceNext observation nontrivial half) ≠ 0 :=
  fun zero => actual_programme_ne_zero observation nontrivial half
    ((D.actual_effect_zero_iff observation nontrivial half).mp zero)

/-- The independently generated full inverse tail survives the same-c unit payment. -/
theorem actual_inverse_tail_ne_zero : U.sourceRaw c ≠ 0 := by
  intro zero
  have rawZero : U.responseRaw c = 0 := by
    funext x
    unfold OriginalWholeDebtRJointMobiusUnitSource.responseRaw
    rw [zero]
    simp only [burnolInnerGapForward, Pi.zero_apply, mul_zero, tsum_zero]
  have valueZero : U.response c = 0 := by
    apply Lp.ext
    filter_upwards [U.actual_raw c, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x actual zeroRead
    simp only [rawZero, Pi.zero_apply] at actual zeroRead
    exact actual.trans zeroRead.symm
  have paid := U.actual_programme_price observation nontrivial half
  rw [valueZero, inner_zero_right, neg_zero] at paid
  exact actual_programme_ne_zero observation nontrivial half paid

/-- This is the strict real physical cost of that actual action, not an integer ledger debit. -/
theorem actual_physical_strict_loss :
    ‖(D.sourceInput observation nontrivial half : BurnolL2) +
      (CayleyEnergySource.sourceDamping c : ℂ) •
        (burnolEvenAmbientProjection (D.sourceNext observation nontrivial half) : BurnolL2)‖ ^ 2 <
      ‖(D.sourceInput observation nontrivial half : BurnolL2)‖ ^ 2 := by
  have damping : 0 < CayleyEnergySource.sourceDamping c := CayleyEnergySource.sourceDamping_pos c
  have column : 0 < ‖hPowerPhysicalCorrection (barC c)‖ :=
    norm_pos_iff.mpr (UnweightedCayleySource.powerCorrection_ne_zero (barC c))
  have price : 0 < ‖programme‖ := norm_pos_iff.mpr (actual_programme_ne_zero observation nontrivial half)
  have positive : 0 < 4 * CayleyEnergySource.sourceDamping c ^ 2 *
      ‖hPowerPhysicalCorrection (barC c)‖ ^ 2 * ‖programme‖ ^ 2 := by positivity
  have cost := D.actual_programme_energy observation nontrivial half
  linarith

end OriginalWholeDebtRJointMobiusStrictSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
