import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFullAdjointSource.Action
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalMaterial.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
universe u v
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFullAdjointSource
open Complex MeasureTheory Set
open BurnolPhysicalState BurnolPhysicalState.OriginalRieszSource
open OriginalKSourceResolventReconstruction OriginalKSourceGramAction
open OriginalKDirectRCofinalMaterial
open SourceOperationScalarInventoryLift
open scoped InnerProductSpace
local instance receiptPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local instance receiptGroups (grade : Nat) (target : Unit) :
    AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target

private theorem pair_heq {A B : Type u} {C D : Type v} {a : A} {b : B} {c : C} {d : D}
    (first : HEq a b) (second : HEq c d) : HEq (a,c) (b,d) := by
  cases first
  cases second
  rfl

private theorem original_Q_normal (coordinate : BurnolCompletedMellinCoordinate)
    (orthogonal : burnolCompletedMellinRieszVector coordinate ∈
      burnolCompactCoPoissonClosedRange.toSubmoduleᗮ) (value : BurnolL2) :
    inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2)
      (OriginalKCombCofinalPaAction.Q value : BurnolL2) =
      inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2) value := by
  have pa := burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.inner_orthogonalProjectionOnto_eq_of_mem_left
    ⟨burnolCompletedMellinRieszVector coordinate,orthogonal⟩ (burnolEvenAmbientProjection value)
  have physical := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_left
    (burnolCompletedMellinRieszVector coordinate) value
  change inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2)
    (OriginalKCombCofinalPaAction.Q value : BurnolL2) =
    inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2) (burnolEvenAmbientProjection value : BurnolL2) at pa
  exact pa.trans physical

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "H" => sourceAdjointField c
local notation "K" => (burnolCompletedMellinRieszVector c : BurnolL2)
local notation "alpha" => OriginalKDirectRCofinalDivision.sourceCoefficient observation nontrivial half depth ordinal
local notation "Qunit" => (OriginalKDirectRCofinalDivision.sourceUnit observation nontrivial half : BurnolL2)
local notation "receiptK" => (installedOriginalKReceiptAt observation nontrivial half.down).kernel
local notation "factory" => D.factory observation nontrivial half
local notation "initial" => D.initial observation nontrivial half depth
local notation "cfg" => D.firstCfg observation nontrivial half depth
local notation "targetRaw" => OriginalKDirectRCofinalCalculatedSource.calculatedTargetRaw observation nontrivial half depth ordinal
local notation "inputRaw" => OriginalKDirectRCofinalCalculatedSource.calculatedInputRaw observation nontrivial half depth ordinal
local notation "raw" => D.raw observation nontrivial half depth ordinal
local notation "born" => D.packet observation nontrivial half depth (ordinal+1)
local notation "bornValue" => CF.collapseValue born.1 (born.2.1.1.activeEnvironment () (),0)
local notation "bornRaw" => (bornValue.1.1+bornValue.1.2)+(bornValue.2.1+bornValue.2.2)

private theorem installed_normal_source_read : inner ℂ receiptK targetRaw = inner ℂ H inputRaw := by
  have anchor := congrArg (fun receipt : OriginalRieszFiniteSource.Receipt => receipt.kernel)
    (installedOriginalKReceiptAt_eq_source observation nontrivial half.down)
  rw [anchor]
  exact calculated_source_input_action observation nontrivial half depth ordinal

private theorem original_nextQ_source_from
    (orthogonal : burnolCompletedMellinRieszVector c ∈ burnolCompactCoPoissonClosedRange.toSubmoduleᗮ)
    (paid : type_of% (OriginalKDirectRCofinalDivision.actual_original_K_read observation nontrivial half depth ordinal))
    (invisible : type_of% (actual_invisible_source_read observation nontrivial half depth ordinal)) :
    inner ℂ K (OriginalKCombCofinalPaAction.Q (D.raw observation nontrivial half depth (ordinal+1)) : BurnolL2) =
      alpha*inner ℂ K Qunit + inner ℂ H (OriginalKCombCofinalPaAction.Q raw : BurnolL2)+
        inner ℂ H (raw-(burnolEvenAmbientProjection raw : BurnolL2)) := by
  have returnRead := original_Q_normal c orthogonal
    (P.R observation nontrivial half (OriginalKCombCofinalPaAction.invisible raw))
  change inner ℂ K (OriginalKDirectRCofinalDivision.sourceReturn observation nontrivial half depth ordinal : BurnolL2) =
    inner ℂ K (P.R observation nontrivial half (OriginalKCombCofinalPaAction.invisible raw)) at returnRead
  change inner ℂ K (OriginalKCombCofinalPaAction.Q (D.raw observation nontrivial half depth (ordinal+1)) : BurnolL2) =
    alpha*inner ℂ K Qunit +
      inner ℂ K (OriginalKDirectRCofinalDivision.sourceReturn observation nontrivial half depth ordinal : BurnolL2) at paid
  rw [returnRead,invisible] at paid
  simpa only [add_assoc] using paid

private theorem installed_born_source_read : inner ℂ receiptK bornRaw =
    alpha*inner ℂ receiptK Qunit+inner ℂ H (OriginalKCombCofinalPaAction.Q raw : BurnolL2)+
      inner ℂ H (raw-(burnolEvenAmbientProjection raw : BurnolL2)) := by
  have anchor := congrArg (fun receipt : OriginalRieszFiniteSource.Receipt => receipt.kernel)
    (installedOriginalKReceiptAt_eq_source observation nontrivial half.down)
  change receiptK=K at anchor
  have orthogonal := riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal c observation.mathlibZero
  have branches := Full.complete_of_branches observation nontrivial half _ _
    (actual_successor_branches observation nontrivial half depth ordinal)
  have source := original_nextQ_source_from observation nontrivial half depth ordinal orthogonal
    (OriginalKDirectRCofinalDivision.actual_original_K_read observation nontrivial half depth ordinal)
    (actual_invisible_source_read observation nontrivial half depth ordinal)
  have bornAction : bornRaw=P.R observation nontrivial half raw := branches.2.2.1
  have bornToRaw := bornAction.trans (D.raw_successor observation nontrivial half depth ordinal).symm
  rw [anchor,bornToRaw,←original_Q_normal c orthogonal]
  exact source

/-- Every argument belongs to this original source packet, its actual normal and its original generated whole-next. -/
def consume_actual_normal_source {Result : Sort u}
    (consumer :
      type_of% (sourceAdjoint_original c) →
      type_of% (installedOriginalKReceiptAt_eq_source observation nontrivial half.down) →
      type_of% (OriginalKDirectRCofinalCalculatedSource.actual_material_calculated_state observation nontrivial half depth ordinal) →
      type_of% (OriginalKDirectRCofinalCalculatedSource.actual_material_calculated_history observation nontrivial half depth ordinal) →
      type_of% (OriginalKDirectRCofinalCalculatedSource.calculated_input_raw observation nontrivial half depth ordinal) →
      type_of% (OriginalKDirectRCofinalCalculatedSource.calculated_full_R_action observation nontrivial half depth ordinal) →
      type_of% (actual_successor_branches observation nontrivial half depth ordinal) →
      type_of% (OriginalKDirectRCofinalDivision.actual_original_K_read observation nontrivial half depth ordinal) →
      type_of% (riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal c observation.mathlibZero) →
      type_of% (RC.original_whole factory initial cfg rfl (ordinal+1)) →
      type_of% (RC.actual_generated_current factory initial cfg rfl (ordinal+1)) → Result) : Result :=
  consumer (sourceAdjoint_original c)
    (installedOriginalKReceiptAt_eq_source observation nontrivial half.down)
    (OriginalKDirectRCofinalCalculatedSource.actual_material_calculated_state observation nontrivial half depth ordinal)
    (OriginalKDirectRCofinalCalculatedSource.actual_material_calculated_history observation nontrivial half depth ordinal)
    (OriginalKDirectRCofinalCalculatedSource.calculated_input_raw observation nontrivial half depth ordinal)
    (OriginalKDirectRCofinalCalculatedSource.calculated_full_R_action observation nontrivial half depth ordinal)
    (actual_successor_branches observation nontrivial half depth ordinal)
    (OriginalKDirectRCofinalDivision.actual_original_K_read observation nontrivial half depth ordinal)
    (riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal c observation.mathlibZero)
    (RC.original_whole factory initial cfg rfl (ordinal+1))
    (RC.actual_generated_current factory initial cfg rfl (ordinal+1))

/-- Whole destination and original generated next carry the actual normal and born readings of the new full source H. -/
theorem actual_normal_source_on_original_whole_next :
    type_of% (OriginalKDirectRCofinalCalculatedSource.calculated_material_target_from observation nontrivial half depth ordinal
      (OriginalKDirectRCofinalCalculatedSource.actual_material_calculated_state observation nontrivial half depth ordinal)) ∧
    type_of% (OriginalKDirectRCofinalCalculatedSource.calculated_face_history_from observation nontrivial half depth ordinal
      (OriginalKDirectRCofinalCalculatedSource.actual_material_calculated_history observation nontrivial half depth ordinal)) ∧
    type_of% (pair_heq (RC.original_whole factory initial cfg rfl (ordinal+1))
      (pair_heq (heq_of_eq (RC.actual_generated_current factory initial cfg rfl (ordinal+1)))
        (pair_heq (heq_of_eq (installed_normal_source_read observation nontrivial half depth ordinal))
          (heq_of_eq (installed_born_source_read observation nontrivial half depth ordinal))))) ∧
    (inner ℂ receiptK (P.R observation nontrivial half (OriginalKCombCofinalPaAction.invisible raw)) =
      inner ℂ H (OriginalKCombCofinalPaAction.Q raw : BurnolL2)+
      inner ℂ H (raw-(burnolEvenAmbientProjection raw : BurnolL2))) ∧
    (inner ℂ H (OriginalKCombCofinalPaAction.E raw : BurnolL2) = alpha*inner ℂ receiptK Qunit) := by
  apply consume_actual_normal_source observation nontrivial half depth ordinal
  intro adjointSource sourceAnchor state trace sourceInput targetAction bornBranches divisionRead orthogonal whole next
  have kernel : receiptK = (burnolCompletedMellinRieszVector c : BurnolL2) :=
    congrArg (fun receipt : OriginalRieszFiniteSource.Receipt => receipt.kernel) sourceAnchor
  have read (value : BurnolL2) :
      inner ℂ receiptK (P.R observation nontrivial half value) = inner ℂ H value := by
    rw [kernel,OriginalKCombCofinalRAction.original_R_direct]
    have right := OriginalKCombCofinalRAction.parameter_rightQuarter observation half
    have actual := OriginalKCompactAdjointRSource.actual_original_R_adjoint
      (observation.coordinate/2) right (burnolCompletedMellinRieszVector c : BurnolL2) value
    simp only [star_div₀,star_ofNat] at actual
    change inner ℂ (burnolCompletedMellinRieszVector c : BurnolL2)
      (burnolDirectRightResolvent (observation.coordinate/2) value) =
      inner ℂ (sourceAdjoint c (burnolCompletedMellinRieszVector c : BurnolL2)) value at actual
    rw [adjointSource] at actual
    exact actual
  have normalRead : inner ℂ receiptK targetRaw = inner ℂ H inputRaw := by
    have target : targetRaw = P.R observation nontrivial half raw := targetAction.2.2
    rw [target,sourceInput]
    exact read raw
  have bornAction := Full.complete_of_branches observation nontrivial half _ _ bornBranches
  have invisible : inner ℂ K (P.R observation nontrivial half (OriginalKCombCofinalPaAction.invisible raw)) =
      inner ℂ H (OriginalKCombCofinalPaAction.Q raw : BurnolL2)+
      inner ℂ H (raw-(burnolEvenAmbientProjection raw : BurnolL2)) :=
    actual_invisible_source_read observation nontrivial half depth ordinal
  have nextQRead := original_nextQ_source_from observation nontrivial half depth ordinal orthogonal divisionRead invisible
  have bornRead : inner ℂ receiptK bornRaw =
      alpha*inner ℂ receiptK Qunit+inner ℂ H (OriginalKCombCofinalPaAction.Q raw : BurnolL2)+
        inner ℂ H (raw-(burnolEvenAmbientProjection raw : BurnolL2)) := by
    have bornR : bornRaw=P.R observation nontrivial half raw := bornAction.2.2.1
    have bornToRaw := bornR.trans (D.raw_successor observation nontrivial half depth ordinal).symm
    rw [kernel,bornToRaw,←original_Q_normal c orthogonal]
    exact nextQRead
  have nextRaw : inner ℂ K (D.raw observation nontrivial half depth (ordinal+1)) =
      alpha*inner ℂ K Qunit+inner ℂ H (OriginalKCombCofinalPaAction.Q raw : BurnolL2)+
        inner ℂ H (raw-(burnolEvenAmbientProjection raw : BurnolL2)) := by
    rw [←original_Q_normal c orthogonal]
    exact nextQRead
  have paPrice : inner ℂ H (OriginalKCombCofinalPaAction.E raw : BurnolL2) =
      alpha*inner ℂ receiptK Qunit := by
    rw [kernel]
    have complete := actual_raw_source_inventory observation nontrivial half depth ordinal
    linear_combination nextRaw-complete
  refine ⟨OriginalKDirectRCofinalCalculatedSource.calculated_material_target_from observation nontrivial half depth ordinal state,
    OriginalKDirectRCofinalCalculatedSource.calculated_face_history_from observation nontrivial half depth ordinal trace,
    pair_heq whole (pair_heq (heq_of_eq next) (pair_heq (heq_of_eq normalRead) (heq_of_eq bornRead))),?_,paPrice⟩
  rw [kernel]
  exact actual_invisible_source_read observation nontrivial half depth ordinal

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFullAdjointSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
