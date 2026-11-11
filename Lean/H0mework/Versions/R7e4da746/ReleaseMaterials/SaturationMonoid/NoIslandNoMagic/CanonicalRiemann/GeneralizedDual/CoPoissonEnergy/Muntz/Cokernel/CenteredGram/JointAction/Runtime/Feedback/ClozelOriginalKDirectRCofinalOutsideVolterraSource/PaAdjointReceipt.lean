import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalOutsideVolterraSource.AdjointGapSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalOutsideVolterraSource.Receipt

set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalOutsideVolterraSource
open Complex MeasureTheory Set BurnolPhysicalState
open OriginalKFullAdjointSource OriginalKDirectRCofinalMaterial
open SourceOperationScalarInventoryLift
open scoped InnerProductSpace
local instance paReceiptPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local instance paReceiptQuarterComplete : CompleteSpace BurnolQuarterMeanZeroCarrier := by
  apply IsComplete.completeSpace_coe
  exact burnolQuarterMeanZeroClosedFace.isClosed.isComplete
local notation "S" => burnolMeanZeroTruncatedFourier
local instance paReceiptGroups (grade : Nat) (target : Unit) :
    AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target

private theorem full_E_selfAdjoint (left right : BurnolL2) :
    inner ℂ left (OriginalKCombCofinalPaAction.E right : BurnolL2) =
      inner ℂ (OriginalKCombCofinalPaAction.E left : BurnolL2) right := by
  have ambient := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_right
    (OriginalKCombCofinalPaAction.E right) left
  have pa := burnolCompactCoPoissonClosedRange.toSubmodule.inner_starProjection_left_eq_right
    (burnolEvenAmbientProjection left) (burnolEvenAmbientProjection right)
  have physical := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_left
    (OriginalKCombCofinalPaAction.E left) right
  exact ambient.symm.trans (pa.symm.trans physical)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "H" => sourceAdjointField c
local notation "K" => (burnolCompletedMellinRieszVector c : BurnolL2)
local notation "raw" => D.raw observation nontrivial half depth ordinal
local notation "rawNext" => D.raw observation nontrivial half depth (ordinal+1)
local notation "g" => sourceOutsideColumn c raw
local notation "receiptK" => (installedOriginalKReceiptAt observation nontrivial half.down).kernel
local notation "alpha" => OriginalKDirectRCofinalDivision.sourceCoefficient observation nontrivial half depth (ordinal+1)
local notation "Qunit" => (OriginalKDirectRCofinalDivision.sourceUnit observation nontrivial half : BurnolL2)
local notation "born" => D.packet observation nontrivial half depth ((ordinal+1)+1)
local notation "bornValue" => CF.collapseValue born.1 (born.2.1.1.activeEnvironment () (),0)
local notation "bornRaw" => (bornValue.1.1+bornValue.1.2)+(bornValue.2.1+bornValue.2.2)

/-- The local callback carries source equations, while the exact prior whole receipt remains intact. -/
def consume_actual_pa_q_adjoint {Result : Sort u}
    (consumer :
      (PA.E H=paAdjointSource c) →
      ((PA.Q H : BurnolL2)=qAdjointSource c) →
      (inner ℂ K (P.R observation nontrivial half (PA.invisible rawNext))=
        inner ℂ H (PA.Q rawNext : BurnolL2)+inner ℂ (outsideCotest H) g) →
      (inner ℂ H (PA.Q rawNext : BurnolL2)=inner ℂ (qAdjointSource c) rawNext) →
      (quarterCotest (fourierL2.symm H)=0) → Result) : Result :=
  let orthogonal := riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal c observation.mathlibZero
  consumer (paAdjointSource_actual c orthogonal) (qAdjointSource_actual c orthogonal)
    (actual_invisible_source_action observation nontrivial half depth ordinal)
    (qAdjointSource_full_input c orthogonal rawNext) (adjoint_inverseFourier_quarterCotest_zero c)

/-- The original Q-unit's K price is computed on its own physical whole unit, using paid K Pa orthogonality. -/
theorem actual_Qunit_source_price : inner ℂ K Qunit=wholeUnitSourcePrice c := by
  have orthogonal := riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal c observation.mathlibZero
  have pa := burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.inner_orthogonalProjectionOnto_eq_of_mem_left
    ⟨burnolCompletedMellinRieszVector c,orthogonal⟩
    (OriginalKDirectRCofinalPaUpdate.sourceWholeUnit observation nontrivial half)
  change inner ℂ K Qunit=inner ℂ K (burnolUnitTailResponse c 4) at pa
  rw [pa,wholeUnitSourcePrice,OriginalKSourceResolventReconstruction.generatedK_eq_original]

private theorem actual_paAdjoint_unit_price_from (source : PA.E H=paAdjointSource c) :
    inner ℂ (paAdjointSource c : BurnolL2) rawNext=alpha*inner ℂ receiptK Qunit := by
  have belongs : paAdjointSource c∈burnolCompactCoPoissonClosedRange := by
    rw [←source]
    exact Submodule.starProjection_apply_mem _ _
  have nextPa : PA.E rawNext∈burnolCompactCoPoissonClosedRange := Submodule.starProjection_apply_mem _ _
  have normal := OriginalKCombCofinalPaAction.wholePa_normal_read rawNext (paAdjointSource c) belongs
  have computed : inner ℂ (paAdjointSource c) (PA.E rawNext)=wholeUnitSourcePrice c*alpha := by
    rw [paAdjointSource,inner_smul_left]
    change star (star (wholeUnitSourcePrice c))*inner ℂ (paCoefficientSource c) (PA.E rawNext)=_
    rw [star_star,paCoefficientSource_read c (PA.E rawNext) nextPa]
    rfl
  have anchor := congrArg (fun receipt:OriginalRieszFiniteSource.Receipt => receipt.kernel)
    (installedOriginalKReceiptAt_eq_source observation nontrivial half.down)
  change receiptK=K at anchor
  rw [anchor,actual_Qunit_source_price]
  exact normal.symm.trans (computed.trans (mul_comm _ _))

private theorem installed_born_complete_adjoint_read :
    inner ℂ receiptK bornRaw=alpha*inner ℂ receiptK Qunit+
      inner ℂ (qAdjointSource c) rawNext+inner ℂ (outsideCotest H) g := by
  have anchor := congrArg (fun receipt:OriginalRieszFiniteSource.Receipt => receipt.kernel)
    (installedOriginalKReceiptAt_eq_source observation nontrivial half.down)
  change receiptK=K at anchor
  have branches := Full.complete_of_branches observation nontrivial half _ _
    (actual_successor_branches observation nontrivial half depth (ordinal+1))
  have bornToRaw : bornRaw=D.raw observation nontrivial half depth ((ordinal+1)+1) :=
    branches.2.2.1.trans (D.raw_successor observation nontrivial half depth (ordinal+1)).symm
  have orthogonal := riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal c observation.mathlibZero
  have normal : inner ℂ K (PA.Q (D.raw observation nontrivial half depth ((ordinal+1)+1)) : BurnolL2)=
      inner ℂ K (D.raw observation nontrivial half depth ((ordinal+1)+1)) := by
    have pa := burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.inner_orthogonalProjectionOnto_eq_of_mem_left
      ⟨burnolCompletedMellinRieszVector c,orthogonal⟩
      (burnolEvenAmbientProjection (D.raw observation nontrivial half depth ((ordinal+1)+1)))
    have physical := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_left
      (burnolCompletedMellinRieszVector c) (D.raw observation nontrivial half depth ((ordinal+1)+1))
    exact pa.trans physical
  rw [anchor,bornToRaw,←normal]
  exact actual_nextQ_complete_source observation nontrivial half depth ordinal

/-- The complete source Pa/Q vectors and both actual prices are consumed beside the same unmodified whole/next. -/
theorem actual_pa_q_adjoint_on_original_whole_next :
    type_of% (actual_outside_source_on_original_whole_next observation nontrivial half depth ordinal) ∧
    (PA.E H=paAdjointSource c) ∧
    ((PA.Q H : BurnolL2)=qAdjointSource c) ∧
    (inner ℂ receiptK (P.R observation nontrivial half (PA.invisible rawNext))=
      inner ℂ (qAdjointSource c) rawNext+inner ℂ (outsideCotest H) g) ∧
    (inner ℂ (paAdjointSource c : BurnolL2) rawNext=alpha*inner ℂ receiptK Qunit) ∧
    (inner ℂ receiptK bornRaw=alpha*inner ℂ receiptK Qunit+
      inner ℂ (qAdjointSource c) rawNext-inner ℂ (quarterCotest H) (S g)) := by
  have prior := actual_outside_source_on_original_whole_next observation nontrivial half depth ordinal
  refine ⟨prior,?_⟩
  apply consume_actual_pa_q_adjoint observation nontrivial half depth ordinal
  intro paVector qVector invisible qRead gapZero
  have anchor := congrArg (fun receipt:OriginalRieszFiniteSource.Receipt => receipt.kernel)
    (installedOriginalKReceiptAt_eq_source observation nontrivial half.down)
  have bornRead := installed_born_complete_adjoint_read observation nontrivial half depth ordinal
  have cotest : outsideCotest H=-(S).adjoint (quarterCotest H) := by
    rw [outsideCotest,gapZero,zero_sub]
  rw [cotest,inner_neg_left,ContinuousLinearMap.adjoint_inner_left] at bornRead
  rw [qRead] at invisible
  refine ⟨paVector,qVector,?_,actual_paAdjoint_unit_price_from observation nontrivial half depth ordinal paVector,?_⟩
  · rw [anchor]
    exact invisible
  · simpa only [sub_eq_add_neg] using bornRead

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalOutsideVolterraSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
