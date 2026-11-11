import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRQuarterUnitSettlementReceiptConsumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRAdjointContactSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.TotalSource.RSourceChannelsConsumer

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 6000
set_option cleanup.letToHave false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRAdjointContactReceiptConsumer
open Complex BurnolPhysicalState OriginalWholeDebtRAdjointContactSource
open OriginalRSourceCoupledChannels
open OriginalKFiniteOrderRelease.UnitPowerSource
open OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
open private correction_physical_price from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRAdjointContactSource
open private power_succ_left from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerSource
open private outside_eq from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
open scoped InnerProductSpace
local notation "C" => OriginalKPairedBEulerJunctionSource.BandFullStockEuler.correctionRaw
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "g" => Recurrence.physicalUpdated observation nontrivial half depth ordinal
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "e" => burnolAnalyticComplementExpectedPhysicalFourierRead ActualAnalyticOwner observation

private theorem installed_source_cotest :
    inner ℂ (C c) (OriginalWholeDebtRSourceReceiptConsumer.actualValue
      observation nontrivial half depth)=
    inner ℂ (sourceField c c) (OriginalKPairedBEulerJunctionSource.BandFullStockAction.wholeDebt c) := by
  rw [OriginalWholeDebtRSourceReceiptConsumer.actual_value_source]
  exact actual_R_cotest c c _

private def actualPaDelta : BurnolPaAmbientCarrier :=
  OriginalKCombCofinalPaAction.actualPa observation nontrivial half depth (ordinal+3)-
    OriginalKCombCofinalPaAction.actualPa observation nontrivial half depth (ordinal+1)

private theorem actualPaDelta_mem : actualPaDelta observation nontrivial half depth ordinal ∈
    burnolCompactCoPoissonClosedRange :=
  burnolCompactCoPoissonClosedRange.sub_mem
    (OriginalKCombCofinalPaAction.actualPa_mem observation nontrivial half depth (ordinal+3))
    (OriginalKCombCofinalPaAction.actualPa_mem observation nontrivial half depth (ordinal+1))

private theorem actualPaDelta_source : actualPaDelta observation nontrivial half depth ordinal=
    OriginalKCombCofinalPaAction.E g := by
  rw [Recurrence.original_updated_total]
  simp only [actualPaDelta,OriginalKCombCofinalPaAction.actualPa,map_sub]

private theorem actualPaDelta_coefficient :
    burnolPaResolventSourceCoefficient c (actualPaDelta observation nontrivial half depth ordinal)=
      OriginalKDirectRCofinalDivision.sourceCoefficient observation nontrivial half depth (ordinal+3)-
        OriginalKDirectRCofinalDivision.sourceCoefficient observation nontrivial half depth (ordinal+1) := by
  rw [actualPaDelta,map_sub]
  rfl

private theorem actual_pa_contact_effect :
    inner ℂ (T c (OriginalKPairedBEulerJunctionSource.BandFullStockEuler.regularSource c)+contactLift c c)
      (actualPaDelta observation nontrivial half depth ordinal : BurnolL2)=0 :=
  original_Pa_contact_effect observation nontrivial half _
    (actualPaDelta_mem observation nontrivial half depth ordinal)

private theorem top_unit_source :
    inner ℂ (C c) (unitPower observation half m)=
      (-2*e)*inner ℂ (C c) (physicalOutsideColumn c) := by
  have positive := generatedRiemannXiZeroOrder_pos observation nontrivial
  let before : BurnolPaAmbientCarrier :=
    ⟨unitPower observation half (m-1),unitPower_physical observation nontrivial half (m-1) (by omega)⟩
  have step : unitPower observation half m=burnolDirectRightResolventCLM c (before : BurnolL2) := by
    have actual := power_succ_left observation half (m-1) (burnolUnitTailResponse c 4)
    change unitPower observation half (m-1+1)=burnolDirectRightResolventCLM c (before : BurnolL2) at actual
    simpa only [show m-1+1=m by omega] using actual
  have outside := original_R_physical_outside_source c before
  change OriginalKCombPhysicalAction.physicalRemainder (burnolDirectRightResolventCLM c (before : BurnolL2))=
    (-2*inner ℂ (fourierL2 (OriginalKSourceResolventReconstruction.generatedK c))
      (before : BurnolL2)) • physicalOutsideColumn c at outside
  rw [OriginalKSourceResolventReconstruction.generatedK_eq_original] at outside
  have top := unitPower_fourier_top observation nontrivial half
  change inner ℂ (fourierL2 (burnolCompletedMellinRieszVector c : BurnolL2))
    (before : BurnolL2)=e at top
  rw [←step,top] at outside
  have paid := congrArg (fun value : BurnolL2 => inner ℂ (C c) value) outside
  rw [outside_eq,inner_sub_right,
    correction_physical_price c _ (burnolEvenAmbientProjection (unitPower observation half m)).property,
    sub_zero,inner_smul_right] at paid
  exact paid

private theorem actual_pa_first_release :
    (∀ k : Nat,k<m → inner ℂ (sourceEffect c c)
      (CombSource.Division.rawIterate observation half.down k
        (actualPaDelta observation nontrivial half depth ordinal : BurnolL2))=0) ∧
    inner ℂ (sourceEffect c c) (CombSource.Division.rawIterate observation half.down m
      (actualPaDelta observation nontrivial half depth ordinal : BurnolL2))=
      star (sigma c c)*
        (OriginalKDirectRCofinalDivision.sourceCoefficient observation nontrivial half depth (ordinal+3)-
          OriginalKDirectRCofinalDivision.sourceCoefficient observation nontrivial half depth (ordinal+1))*
        ((-2*e)*inner ℂ (C c) (physicalOutsideColumn c)) := by
  have actual := original_Pa_first_release observation nontrivial half
    (actualPaDelta observation nontrivial half depth ordinal)
    (actualPaDelta_mem observation nontrivial half depth ordinal)
  dsimp only at actual
  rw [actualPaDelta_coefficient,top_unit_source] at actual
  exact actual

private noncomputable def consumePoint {point : BurnolL2}
    (same : point=Physical.originalPoint observation nontrivial half depth ordinal) := by
  have action := same.trans (Physical.original_action observation nontrivial half depth ordinal)
  rw [OriginalKCombCofinalRAction.original_R_direct] at action
  change point=burnolDirectRightResolventCLM c g at action
  have cotest : inner ℂ (C c) point=inner ℂ (sourceField c c) g :=
    (congrArg (fun value : BurnolL2 => inner ℂ (C c) value) action).trans (actual_R_cotest c c g)
  exact PProd.mk point (PProd.mk action cotest)

private noncomputable def Result : Sort _ :=
  Σ' prior : type_of% (OriginalWholeDebtRQuarterUnitSettlementReceiptConsumer.actual_quarter_unit_source_whole_next
      observation nontrivial half depth ordinal),
    PProd (prior=OriginalWholeDebtRQuarterUnitSettlementReceiptConsumer.actual_quarter_unit_source_whole_next
        observation nontrivial half depth ordinal)
      (Σ' written : type_of% (OriginalRSourceCoupledChannels.read observation nontrivial half depth ordinal),
        PProd (written=OriginalRSourceCoupledChannels.read observation nontrivial half depth ordinal)
          (PProd
            ((type_of% (actual_source_action c c)) ∧ (type_of% (actual_source_action c (barC c))) ∧
              (type_of% (installed_source_cotest observation nontrivial half depth)) ∧
              (type_of% (actualPaDelta_source observation nontrivial half depth ordinal)) ∧
              (type_of% (actual_pa_contact_effect observation nontrivial half depth ordinal)) ∧
              (type_of% (actual_pa_first_release observation nontrivial half depth ordinal)))
            (type_of% (consumePoint observation nontrivial half depth ordinal written.1.2.2.2.1))))

/-- Both literal source packages retain their whole/next and consume the complete contact field. -/
noncomputable opaque actual_adjoint_contact_source_whole_next :
    Result observation nontrivial half depth ordinal := by
  let prior := OriginalWholeDebtRQuarterUnitSettlementReceiptConsumer.actual_quarter_unit_source_whole_next
    observation nontrivial half depth ordinal
  let written := OriginalRSourceCoupledChannels.read observation nontrivial half depth ordinal
  exact ⟨prior,rfl,written,rfl,⟨actual_source_action c c,actual_source_action c (barC c),
    installed_source_cotest observation nontrivial half depth,
    actualPaDelta_source observation nontrivial half depth ordinal,
    actual_pa_contact_effect observation nontrivial half depth ordinal,
    actual_pa_first_release observation nontrivial half depth ordinal⟩,
    consumePoint observation nontrivial half depth ordinal written.1.2.2.2.1⟩

end OriginalWholeDebtRAdjointContactReceiptConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
