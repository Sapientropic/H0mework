import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CayleyEnergySource
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.PhysicalDefectMaterialConsumer

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_energy_on_original_whole_next"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_born_energy_consumer"
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCrossParameterRAdjointSource.CayleyEnergyMaterialConsumer
open Complex MeasureTheory Set BurnolPhysicalState
open OriginalKDirectRCofinalMaterial OriginalKFullAdjointSource OriginalKDirectRCofinalOutsideVolterraSource
open SourceOperationScalarInventoryLift
open scoped InnerProductSpace
local instance energyMaterialGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
local instance energyMaterialComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "δ" => CayleyEnergySource.sourceDamping c
local notation "proj" => burnolEvenAmbientProjection
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "gK" => OriginalKSourceResolventReconstruction.generatedK
local notation "K" => (burnolCompletedMellinRieszVector c : BurnolL2)
local notation "H" => sourceAdjointField c
local notation "receiptK" => (installedOriginalKReceiptAt observation nontrivial half.down).kernel
local notation "raw" => D.raw observation nontrivial half depth ordinal
local notation "rawNext" => D.raw observation nontrivial half depth (ordinal+1)
local notation "inputRaw" => OriginalKDirectRCofinalCalculatedSource.calculatedInputRaw observation nontrivial half depth ordinal
local notation "targetRaw" => OriginalKDirectRCofinalCalculatedSource.calculatedTargetRaw observation nontrivial half depth ordinal
local notation "bornRaw" => OriginalKDirectRCofinalPaUpdate.DirectRPaUpdateControls.bornRead observation nontrivial half depth ordinal
local notation "factory" => D.factory observation nontrivial half
local notation "initial" => D.initial observation nontrivial half depth
local notation "cfg" => D.firstCfg observation nontrivial half depth

/-- This deduction uses the already generated complete outside-to-Q response. -/
def incomingDeduction (value : BurnolL2) : BurnolL2 :=
 (δ:ℂ) • PhysicalDefectMaterialConsumer.outsideSource observation half value
def correctedPhysicalRead (input target : BurnolL2) : BurnolL2 :=
 (proj input : BurnolL2)+(δ:ℂ) • (proj target : BurnolL2)-incomingDeduction observation half input
def lossProduct (value : BurnolL2) : ℝ :=
 ‖hPowerPhysicalCorrection (barC c)‖^2*‖inner ℂ (fourierL2 (gK c)) (proj value : BurnolL2)‖^2

/-- Full source energy, both charged projections and the actual K adjoint belong to this original born. -/
theorem actual_energy_on_original_whole_next :
 type_of% (PhysicalDefectMaterialConsumer.actual_coupled_source_on_original_whole_next observation nontrivial half depth ordinal) ∧
 type_of% (OriginalKDirectRCofinalCalculatedSource.calculated_material_target_from observation nontrivial half depth ordinal
  (OriginalKDirectRCofinalCalculatedSource.actual_material_calculated_state observation nontrivial half depth ordinal)) ∧
 type_of% (OriginalKDirectRCofinalCalculatedSource.calculated_face_history_from observation nontrivial half depth ordinal
  (OriginalKDirectRCofinalCalculatedSource.actual_material_calculated_history observation nontrivial half depth ordinal)) ∧
 (‖inputRaw+(δ:ℂ) • targetRaw‖=‖inputRaw‖) ∧
 (‖raw+(δ:ℂ) • rawNext‖=‖raw‖) ∧
 (‖raw+(δ:ℂ) • bornRaw‖=‖raw‖) ∧
 (‖(proj inputRaw : BurnolL2)‖^2-‖correctedPhysicalRead observation half inputRaw targetRaw‖^2=
  4*δ^2*lossProduct observation half inputRaw) ∧
 (‖(proj raw : BurnolL2)‖^2-‖correctedPhysicalRead observation half raw rawNext‖^2=
  4*δ^2*lossProduct observation half raw) ∧
 (‖(proj raw : BurnolL2)‖^2-‖correctedPhysicalRead observation half raw bornRaw‖^2=
  4*δ^2*lossProduct observation half raw) ∧
 ((CayleyEnergySource.sourceCayley c).adjoint receiptK=receiptK+(δ:ℂ) • H) ∧
 (‖(CayleyEnergySource.sourceCayley c).adjoint receiptK‖=‖receiptK‖) ∧
 (‖receiptK‖^2-‖receiptK+(δ:ℂ) • hPhysicalField c‖^2=
  4*δ^2*‖hPowerPhysicalCorrection c‖^2*‖inner ℂ (gK (barC c)) receiptK‖^2) ∧
 type_of% (RC.original_whole factory initial cfg rfl (ordinal+1)) ∧
 type_of% (RC.actual_generated_current factory initial cfg rfl (ordinal+1)) := by
 apply consume_actual_normal_source observation nontrivial half depth ordinal
 intro adjointSource sourceAnchor state trace sourceInput targetAction bornBranches divisionRead orthogonal whole next
 have actualR : burnolDirectRightResolvent ((c).value/2) raw=rawNext := by
  rw [D.raw_successor,OriginalKCombCofinalRAction.original_R_direct]
  rfl
 have full:=CayleyEnergySource.sourceCayley_norm c raw
 rw [CayleyEnergySource.sourceCayley_apply,actualR] at full
 have target : targetRaw=rawNext := targetAction.2.2.trans (D.raw_successor observation nontrivial half depth ordinal).symm
 have calculated:=Full.complete_of_branches observation nontrivial half _ _ bornBranches
 have bornR : bornRaw=P.R observation nontrivial half raw := calculated.2.2.1
 have bornToRaw : bornRaw=rawNext := bornR.trans (D.raw_successor observation nontrivial half depth ordinal).symm
 have vector (input target : BurnolL2) : correctedPhysicalRead observation half input target=
   (proj input : BurnolL2)+(δ:ℂ) • (proj target : BurnolL2)+
    (2*(δ:ℂ)*inner ℂ (hPowerPhysicalCorrection c) (P.physicalRemainder input)) • gK (barC c) := by
  unfold correctedPhysicalRead incomingDeduction PhysicalDefectMaterialConsumer.outsideSource PhysicalDefectMaterialConsumer.outsideAmplitude
  module
 have generated:=CayleyEnergySource.actual_physical_incoming_energy observation nontrivial half depth ordinal
 have energy : ‖(proj raw : BurnolL2)‖^2-‖correctedPhysicalRead observation half raw rawNext‖^2=
   4*δ^2*lossProduct observation half raw := by
  rw [vector]
  simpa only [lossProduct,mul_assoc] using generated
 have normalFull : ‖inputRaw+(δ:ℂ) • targetRaw‖=‖inputRaw‖ := by rw [sourceInput,target];exact full
 have bornFull : ‖raw+(δ:ℂ) • bornRaw‖=‖raw‖ := by rw [bornToRaw];exact full
 have normalEnergy : ‖(proj inputRaw : BurnolL2)‖^2-‖correctedPhysicalRead observation half inputRaw targetRaw‖^2=
   4*δ^2*lossProduct observation half inputRaw := by rw [sourceInput,target];exact energy
 have bornEnergy : ‖(proj raw : BurnolL2)‖^2-‖correctedPhysicalRead observation half raw bornRaw‖^2=
   4*δ^2*lossProduct observation half raw := by rw [bornToRaw];exact energy
 have kernel : receiptK=K := congrArg (fun receipt : OriginalRieszFiniteSource.Receipt=>receipt.kernel) sourceAnchor
 have originalAdjoint : sourceAdjoint c K=H := adjointSource
 have adjointK : (CayleyEnergySource.sourceCayley c).adjoint receiptK=receiptK+(δ:ℂ) • H := by
  rw [CayleyEnergySource.sourceCayley_actual_adjoint,CayleyEnergySource.sourceAdjointCayley,kernel,originalAdjoint]
 have adjointNorm : ‖(CayleyEnergySource.sourceCayley c).adjoint receiptK‖=‖receiptK‖ := by
  rw [CayleyEnergySource.sourceCayley_actual_adjoint]
  exact CayleyEnergySource.sourceAdjointCayley_norm c receiptK
 have kLoss:=CayleyEnergySource.physical_adjoint_exact_loss c (burnolCompletedMellinRieszVector c)
 rw [originalAdjoint,hPhysicalField_actual] at kLoss
 have receiptLoss : ‖receiptK‖^2-‖receiptK+(δ:ℂ) • hPhysicalField c‖^2=
   4*δ^2*‖hPowerPhysicalCorrection c‖^2*‖inner ℂ (gK (barC c)) receiptK‖^2 := by
  rw [kernel]
  exact kLoss
 exact ⟨PhysicalDefectMaterialConsumer.actual_coupled_source_on_original_whole_next observation nontrivial half depth ordinal,
  OriginalKDirectRCofinalCalculatedSource.calculated_material_target_from observation nontrivial half depth ordinal state,
  OriginalKDirectRCofinalCalculatedSource.calculated_face_history_from observation nontrivial half depth ordinal trace,
  normalFull,full,bornFull,normalEnergy,energy,bornEnergy,adjointK,adjointNorm,receiptLoss,whole,next⟩

/-- The independent reader retains the full actual born/decoder and consumes its charged energy and original K loss. -/
theorem actual_born_energy_consumer :
 type_of% (PhysicalDefectMaterialConsumer.actual_born_decoder_coupled_consumer observation nontrivial half depth ordinal) ∧
 (‖raw+(δ:ℂ) • bornRaw‖=‖raw‖) ∧
 (‖(proj raw : BurnolL2)‖^2-‖correctedPhysicalRead observation half raw bornRaw‖^2=
  4*δ^2*lossProduct observation half raw) ∧
 ((CayleyEnergySource.sourceCayley c).adjoint receiptK=receiptK+(δ:ℂ) • H) ∧
 (‖(CayleyEnergySource.sourceCayley c).adjoint receiptK‖=‖receiptK‖) ∧
 (‖receiptK‖^2-‖receiptK+(δ:ℂ) • hPhysicalField c‖^2=
  4*δ^2*‖hPowerPhysicalCorrection c‖^2*‖inner ℂ (gK (barC c)) receiptK‖^2) ∧
 type_of% (RC.original_whole factory initial cfg rfl (ordinal+1)) ∧
 type_of% (RC.actual_generated_current factory initial cfg rfl (ordinal+1)) := by
 have actual:=actual_energy_on_original_whole_next observation nontrivial half depth ordinal
 exact ⟨PhysicalDefectMaterialConsumer.actual_born_decoder_coupled_consumer observation nontrivial half depth ordinal,
  actual.2.2.2.2.2.1,actual.2.2.2.2.2.2.2.2.1,actual.2.2.2.2.2.2.2.2.2.1,
  actual.2.2.2.2.2.2.2.2.2.2.1,actual.2.2.2.2.2.2.2.2.2.2.2.1,
  actual.2.2.2.2.2.2.2.2.2.2.2.2.1,actual.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Zero incoming deduction removes only that term; the complete outgoing loss is still charged. -/
theorem actual_zero_incoming_override (zero : incomingDeduction observation half raw=0) :
 ‖(proj raw : BurnolL2)‖^2-‖(proj raw : BurnolL2)+(δ:ℂ) • (proj bornRaw : BurnolL2)‖^2=
  4*δ^2*lossProduct observation half raw := by
 have actual:=(actual_born_energy_consumer observation nontrivial half depth ordinal).2.2.1
 simpa only [correctedPhysicalRead,zero,sub_zero] using actual

/-- The exact zero product gives equality for the charged physical read without selecting either factor. -/
theorem actual_zero_loss_product_override (zero : lossProduct observation half raw=0) :
 ‖correctedPhysicalRead observation half raw bornRaw‖^2=‖(proj raw : BurnolL2)‖^2 := by
 have actual:=(actual_born_energy_consumer observation nontrivial half depth ordinal).2.2.1
 rw [zero,mul_zero] at actual
 exact (sub_eq_zero.mp actual).symm

/-- A nonzero real source column cannot be omitted from the incoming correction vector. -/
theorem actual_incoming_source_cannot_be_dropped
 (nonzero : PhysicalDefectMaterialConsumer.outsideSource observation half raw≠0) :
 correctedPhysicalRead observation half raw bornRaw≠(proj raw : BurnolL2)+(δ:ℂ) • (proj bornRaw : BurnolL2) := by
 have damping : (δ:ℂ)≠0 := by exact_mod_cast (ne_of_gt (CayleyEnergySource.sourceDamping_pos c))
 have deduction : incomingDeduction observation half raw≠0 := smul_ne_zero damping nonzero
 intro erased
 exact deduction (sub_eq_self.mp erased)

/-- A nonzero loss product prevents reporting the charged physical output as norm preserving. -/
theorem actual_nonzero_loss_cannot_be_erased (nonzero : lossProduct observation half raw≠0) :
 ‖correctedPhysicalRead observation half raw bornRaw‖^2≠‖(proj raw : BurnolL2)‖^2 := by
 have damping : δ≠0 := ne_of_gt (CayleyEnergySource.sourceDamping_pos c)
 have charge : 4*δ^2*lossProduct observation half raw≠0 :=
  mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ damping)) nonzero
 intro erased
 have actual:=(actual_born_energy_consumer observation nontrivial half depth ordinal).2.2.1
 rw [erased,sub_self] at actual
 exact charge actual.symm

end OriginalKCrossParameterRAdjointSource.CayleyEnergyMaterialConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
