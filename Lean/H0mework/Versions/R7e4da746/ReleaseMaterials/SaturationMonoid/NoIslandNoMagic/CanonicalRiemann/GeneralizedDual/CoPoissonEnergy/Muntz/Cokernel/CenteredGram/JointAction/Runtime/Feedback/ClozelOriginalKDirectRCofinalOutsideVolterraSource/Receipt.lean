import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalOutsideVolterraSource.Action
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFullAdjointSource.Receipt

set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
universe u v
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalOutsideVolterraSource
open Complex MeasureTheory Set Filter BurnolPhysicalState
open OriginalKDirectRCofinalMaterial
open SourceOperationScalarInventoryLift
open scoped InnerProductSpace
local notation "S" => burnolMeanZeroTruncatedFourier
local instance receiptPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local instance receiptGroups (grade : Nat) (target : Unit) :
    AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "H" => OriginalKFullAdjointSource.sourceAdjointField c
local notation "raw" => D.raw observation nontrivial half depth ordinal
local notation "rawNext" => D.raw observation nontrivial half depth (ordinal+1)
local notation "g" => sourceOutsideColumn c raw
local notation "d" => sourceFourierGap c raw
local notation "K" => (burnolCompletedMellinRieszVector c : BurnolL2)
local notation "receiptK" => (installedOriginalKReceiptAt observation nontrivial half.down).kernel
local notation "alpha" => OriginalKDirectRCofinalDivision.sourceCoefficient observation nontrivial half depth (ordinal+1)
local notation "Qunit" => (OriginalKDirectRCofinalDivision.sourceUnit observation nontrivial half : BurnolL2)
local notation "inputRaw" => OriginalKDirectRCofinalCalculatedSource.calculatedInputRaw observation nontrivial half depth (ordinal+1)
local notation "born" => D.packet observation nontrivial half depth ((ordinal+1)+1)
local notation "bornValue" => CF.collapseValue born.1 (born.2.1.1.activeEnvironment () (),0)
local notation "bornRaw" => (bornValue.1.1+bornValue.1.2)+(bornValue.2.1+bornValue.2.2)

private theorem outside_slot_from
    (vector : (D.input observation nontrivial half depth (ordinal+1)).2=sourceOutsideField c raw) :
    rawNext-(burnolEvenAmbientProjection rawNext : BurnolL2)=sourceOutsideField c raw := by
  have split := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.starProjection_add_starProjection_orthogonal rawNext
  rw [D.next_pair,←D.raw_successor] at vector
  change (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.orthogonal.starProjection rawNext=sourceOutsideField c raw at vector
  rw [vector] at split
  change rawNext-(evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.starProjection rawNext=_
  linear_combination (norm:=module) -split

private theorem source_B_price_from
    (equation : burnolMeanZeroOneMinusSquare g=d) :
    inner ℂ (outsideCotest H) g=inner ℂ (outsideCotest H) d+inner ℂ (outsideCotest H) (S (S g)) := by
  have actual := congrArg (inner ℂ (outsideCotest H)) equation
  change inner ℂ (outsideCotest H) (g-S (S g))=inner ℂ (outsideCotest H) d at actual
  rw [inner_sub_right] at actual
  linear_combination actual

private theorem source_actual_input_profile : sourceFourierInput c raw=fourierL2 inputRaw := by
  rw [OriginalKDirectRCofinalCalculatedSource.calculated_input_raw,D.raw_successor,
    OriginalKCombCofinalRAction.original_R_direct]
  exact source_fourier_input c raw

private theorem receipt_Q_normal (value : BurnolL2) :
    inner ℂ K (PA.Q value : BurnolL2)=inner ℂ K value := by
  have orthogonal := riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal c observation.mathlibZero
  have pa := burnolCompactCoPoissonClosedRange.toSubmodule.orthogonal.inner_orthogonalProjectionOnto_eq_of_mem_left
    ⟨burnolCompletedMellinRieszVector c,orthogonal⟩ (burnolEvenAmbientProjection value)
  have physical := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_left
    (burnolCompletedMellinRieszVector c) value
  exact pa.trans physical

private theorem installed_born_B_read_from (equation : burnolMeanZeroOneMinusSquare g=d) :
    inner ℂ receiptK bornRaw=
      alpha*inner ℂ receiptK Qunit+inner ℂ H (PA.Q rawNext : BurnolL2)+
        inner ℂ (outsideCotest H) d+inner ℂ (outsideCotest H) (S (S g)) := by
  have anchor := congrArg (fun receipt:OriginalRieszFiniteSource.Receipt => receipt.kernel)
    (installedOriginalKReceiptAt_eq_source observation nontrivial half.down)
  change receiptK=K at anchor
  have branches := Full.complete_of_branches observation nontrivial half _ _
    (actual_successor_branches observation nontrivial half depth (ordinal+1))
  have bornToRaw : bornRaw=D.raw observation nontrivial half depth ((ordinal+1)+1) :=
    branches.2.2.1.trans (D.raw_successor observation nontrivial half depth (ordinal+1)).symm
  rw [anchor,bornToRaw,←receipt_Q_normal observation nontrivial half]
  have actual := actual_nextQ_source_action observation nontrivial half depth ordinal
  rw [source_B_price_from observation nontrivial half depth ordinal equation] at actual
  simpa only [add_assoc] using actual

/-- A five-input dependent consumer transforms the already installed original whole-next read by the new full source action. -/
def consume_actual_outside_source {Result : Sort u}
    (consumer :
      type_of% (@OriginalKFullAdjointSource.actual_normal_source_on_original_whole_next observation nontrivial half depth (ordinal+1)).2.2.2.1 →
      type_of% (source_fourier_input c raw) →
      type_of% (source_outside_B_action c raw) →
      type_of% (actual_born_outside_source observation nontrivial half depth ordinal) →
      type_of% (source_outside_pairing c raw H) → Result) : Result :=
  consumer (@OriginalKFullAdjointSource.actual_normal_source_on_original_whole_next observation nontrivial half depth (ordinal+1)).2.2.2.1
    (source_fourier_input c raw) (source_outside_B_action c raw)
    (actual_born_outside_source observation nontrivial half depth ordinal) (source_outside_pairing c raw H)

/-- The installed whole/next proof is carried intact; the source callback computes the same born scalar and full input profile. -/
theorem actual_outside_source_on_original_whole_next :
    type_of% (@OriginalKFullAdjointSource.actual_normal_source_on_original_whole_next observation nontrivial half depth (ordinal+1)) ∧
    (inner ℂ receiptK bornRaw=
      alpha*inner ℂ receiptK Qunit+inner ℂ H (PA.Q rawNext : BurnolL2)+
        inner ℂ (outsideCotest H) d+inner ℂ (outsideCotest H) (S (S g))) ∧
    (sourceFourierInput c raw=fourierL2 inputRaw) ∧
    (inner ℂ receiptK (P.R observation nontrivial half (PA.invisible rawNext))=
      inner ℂ H (PA.Q rawNext : BurnolL2)+inner ℂ (outsideCotest H) d+inner ℂ (outsideCotest H) (S (S g))) ∧
    (inner ℂ H (PA.E rawNext : BurnolL2)=alpha*inner ℂ receiptK Qunit) := by
  have prior := @OriginalKFullAdjointSource.actual_normal_source_on_original_whole_next observation nontrivial half depth (ordinal+1)
  refine ⟨prior,?_⟩
  apply consume_actual_outside_source observation nontrivial half depth ordinal
  intro invisible inputSource equation vector pairing
  have outside := outside_slot_from observation nontrivial half depth ordinal vector
  have second := source_B_price_from observation nontrivial half depth ordinal equation
  rw [outside,pairing,second] at invisible
  have profile : sourceFourierInput c raw=fourierL2 inputRaw := by
    rw [OriginalKDirectRCofinalCalculatedSource.calculated_input_raw,D.raw_successor,
      OriginalKCombCofinalRAction.original_R_direct]
    exact inputSource
  refine ⟨installed_born_B_read_from observation nontrivial half depth ordinal equation,profile,?_,prior.2.2.2.2⟩
  simpa only [add_assoc] using invisible

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalOutsideVolterraSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
