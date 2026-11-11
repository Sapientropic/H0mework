import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.UnweightedCayleySource
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CayleyIntertwiningMaterialConsumer

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_return_on_original_whole_next"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_return_born_consumer"
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCrossParameterRAdjointSource.UnweightedCayleyMaterialConsumer
open Complex MeasureTheory Set BurnolPhysicalState
open OriginalKDirectRCofinalMaterial OriginalKFullAdjointSource OriginalKDirectRCofinalOutsideVolterraSource
open OriginalKSourceResolventReconstruction SourceOperationScalarInventoryLift
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing.CoPoisson.Ward
open scoped InnerProductSpace
namespace Old
export OriginalKElementaryArithmeticAction.FullOriginalRUnitSource
 (sourceFK unitAdjointSource unit_adjoint_source full_original_R_fields)
end Old
namespace PA
export OriginalKCombCofinalPaAction (E Q)
end PA
local instance unweightedMaterialGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
local instance unweightedMaterialComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def unitAdjointField (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
 star (star coordinate.value*GapEuler.gapMean (1/4) coordinate) •
  (generatedK coordinate-star ((1-star coordinate.value)/2) • fourierL2 (UnweightedCayleySource.sourceFKAction coordinate))
def outsidePrice (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) : ℂ :=
 star (2*((‖generatedK (OriginalPrimitiveRankBalance.conjugateCoordinate coordinate)‖^2:ℝ):ℂ))*
  inner ℂ (hPowerPhysicalCorrection coordinate) (P.physicalRemainder value)
def nextBarPrice (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) : ℂ :=
 star (UnweightedCayleySource.sourceAdjointRatio coordinate/(CayleyEnergySource.sourceDamping coordinate:ℂ))*
   inner ℂ (fourierL2 (generatedK coordinate)) value-
  star ((CayleyEnergySource.sourceDamping coordinate:ℂ)⁻¹)*
   inner ℂ (generatedK (OriginalPrimitiveRankBalance.conjugateCoordinate coordinate)) value-outsidePrice coordinate value

/-- The existing full original source fields now consume the c-only unweighted action. -/
theorem original_FK_source_fields (coordinate : BurnolCompletedMellinCoordinate) :
 sourceFKResponse coordinate coordinate=UnweightedCayleySource.sourceFKAction coordinate ∧
 Old.sourceFK coordinate=UnweightedCayleySource.sourceFKAction coordinate := by
 have generated:=UnweightedCayleySource.original_R_FK_generated coordinate
 have cross : burnolDirectRightResolvent (coordinate.value/2) (fourierL2 (generatedK coordinate))=
   sourceFKResponse coordinate coordinate := by
  simpa only [generatedK_eq_original] using source_FK_response coordinate coordinate
 have old : burnolDirectRightResolvent (coordinate.value/2) (fourierL2 (generatedK coordinate))=Old.sourceFK coordinate := by
  simpa only [generatedK_eq_original] using (Old.full_original_R_fields coordinate).2
 exact ⟨cross.symm.trans generated,old.symm.trans generated⟩

theorem original_unit_adjoint_actual (coordinate : BurnolCompletedMellinCoordinate) :
 Old.unitAdjointSource coordinate=unitAdjointField coordinate := by
 unfold Old.unitAdjointSource unitAdjointField
 rw [(original_FK_source_fields coordinate).2]

theorem original_unit_price (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
 inner ℂ (generatedK coordinate) (OriginalKElementaryArithmeticAction.unitResolventSource coordinate value)=
  inner ℂ (unitAdjointField coordinate) value := by
 rw [generatedK_eq_original,Old.unit_adjoint_source,original_unit_adjoint_actual]

/-- True original-R duality applies the full independent adjoint source to every complete input. -/
theorem conjugateK_R_price (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
 inner ℂ (generatedK (OriginalPrimitiveRankBalance.conjugateCoordinate coordinate))
  (burnolDirectRightResolvent (coordinate.value/2) value)=nextBarPrice coordinate value := by
 have right : 1/4<(coordinate.value/2).re := by rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]
 have dual:=OriginalKCompactAdjointRSource.actual_original_R_adjoint (coordinate.value/2) right
  (generatedK (OriginalPrimitiveRankBalance.conjugateCoordinate coordinate)) value
 simp only [star_div₀,star_ofNat] at dual
 change inner ℂ (generatedK (OriginalPrimitiveRankBalance.conjugateCoordinate coordinate))
   (burnolDirectRightResolvent (coordinate.value/2) value)=
  inner ℂ (sourceAdjoint coordinate (generatedK (OriginalPrimitiveRankBalance.conjugateCoordinate coordinate))) value at dual
 rw [UnweightedCayleySource.original_R_adjoint_conjugateK_generated] at dual
 have stock:=(evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmoduleᗮ.inner_orthogonalProjectionOnto_eq_of_mem_left
  ⟨hPowerPhysicalCorrection coordinate,CayleyIntertwiningSource.powerCorrection_orthogonal coordinate⟩ value
 change inner ℂ (hPowerPhysicalCorrection coordinate) (P.physicalRemainder value)=
  inner ℂ (hPowerPhysicalCorrection coordinate) value at stock
 rw [dual]
 unfold UnweightedCayleySource.sourceConjugateAdjointAction nextBarPrice outsidePrice
 simp only [inner_sub_left,inner_smul_left,starRingEnd_apply]
 rw [←stock]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "δ" => (CayleyEnergySource.sourceDamping c : ℂ)
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "K" => generatedK c
local notation "Kbar" => generatedK (barC c)
local notation "FK" => fourierL2 K
local notation "V" => PhysicalOutsideSource.physicalOutsideColumn c
local notation "σ" => CayleyIntertwiningSource.sourceSigma c

include nontrivial in
/-- Actual cross-unit Pa payment is consumed before the newly computed original Q return is read. -/
theorem actual_FK_Q_return :
 PA.E (UnweightedCayleySource.sourceFKAction c)=0 ∧
 (PA.Q (Old.sourceFK c) : BurnolL2)=
  (UnweightedCayleySource.sourceForwardRatio c/δ) • Kbar-δ⁻¹ • FK := by
 have oldZero:=(CayleyIntertwiningMaterialConsumer.actual_FK_Pa_return_zero observation nontrivial half).2.2
 have field:=(original_FK_source_fields c).2
 have newZero:=(congrArg PA.E field).symm.trans oldZero
 have split:=burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_add_starProjection_orthogonal
  (burnolEvenAmbientProjection (Old.sourceFK c))
 have inventory:=congrArg (fun value : BurnolPaAmbientCarrier=>(value : BurnolL2)) split
 change (PA.E (Old.sourceFK c) : BurnolL2)+(PA.Q (Old.sourceFK c) : BurnolL2)=
  (burnolEvenAmbientProjection (Old.sourceFK c) : BurnolL2) at inventory
 rw [oldZero,ZeroMemClass.coe_zero,zero_add] at inventory
 have pK : (burnolEvenAmbientProjection Kbar : BurnolL2)=Kbar := by
  rw [generatedK_eq_original]
  exact congrArg (fun value : BurnolPaAmbientCarrier=>(value : BurnolL2))
   (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (burnolCompletedMellinRieszVector (barC c)))
 have pFK : (burnolEvenAmbientProjection FK : BurnolL2)=FK := by
  rw [generatedK_eq_original]
  exact congrArg (fun value : BurnolPaAmbientCarrier=>(value : BurnolL2))
   (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
    (evenFaceFourierEquiv burnolUnscaledCommonGapRadius (burnolCompletedMellinRieszVector c)))
 have pV : (burnolEvenAmbientProjection V : BurnolL2)=0 := by
  have zero : burnolEvenAmbientProjection V=0 :=
   Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal (CayleyIntertwiningSource.outsideColumn_orthogonal c)
  rw [zero,ZeroMemClass.coe_zero]
 have projected:=congrArg burnolEvenAmbientProjectionEndomorphism field
 unfold UnweightedCayleySource.sourceFKAction at projected
 rw [map_sub,map_sub,map_smul,map_smul,map_smul] at projected
 change (burnolEvenAmbientProjection (Old.sourceFK c) : BurnolL2)=
  (UnweightedCayleySource.sourceForwardRatio c/δ) • (burnolEvenAmbientProjection Kbar : BurnolL2)-
   δ⁻¹ • (burnolEvenAmbientProjection FK : BurnolL2)-
   (2*((‖K‖^2:ℝ):ℂ)) • (burnolEvenAmbientProjection V : BurnolL2) at projected
 rw [pK,pFK,pV,smul_zero,sub_zero] at projected
 exact ⟨newZero,inventory.trans projected⟩

variable (depth ordinal : Nat)
local notation "raw" => D.raw observation nontrivial half depth ordinal
local notation "rawNext" => D.raw observation nontrivial half depth (ordinal+1)
local notation "inputRaw" => OriginalKDirectRCofinalCalculatedSource.calculatedInputRaw observation nontrivial half depth ordinal
local notation "targetRaw" => OriginalKDirectRCofinalCalculatedSource.calculatedTargetRaw observation nontrivial half depth ordinal
local notation "bornRaw" => OriginalKDirectRCofinalPaUpdate.DirectRPaUpdateControls.bornRead observation nontrivial half depth ordinal
local notation "receiptK" => (installedOriginalKReceiptAt observation nontrivial half.down).kernel
local notation "unitQuery" => OriginalKElementaryArithmeticAction.unitResolventSource c
local notation "factory" => D.factory observation nontrivial half
local notation "initial" => D.initial observation nontrivial half depth
local notation "cfg" => D.firstCfg observation nontrivial half depth

/-- Source-owned normalization replaces the old full fields and this same born's complete next prices. -/
theorem actual_return_on_original_whole_next :
 type_of% (CayleyIntertwiningMaterialConsumer.actual_weighted_return_on_original_whole_next observation nontrivial half depth ordinal) ∧
 type_of% (OriginalKDirectRCofinalCalculatedSource.calculated_material_target_from observation nontrivial half depth ordinal
  (OriginalKDirectRCofinalCalculatedSource.actual_material_calculated_state observation nontrivial half depth ordinal)) ∧
 type_of% (OriginalKDirectRCofinalCalculatedSource.calculated_face_history_from observation nontrivial half depth ordinal
  (OriginalKDirectRCofinalCalculatedSource.actual_material_calculated_history observation nontrivial half depth ordinal)) ∧
 (sourceFKResponse c c=UnweightedCayleySource.sourceFKAction c) ∧
 (Old.sourceFK c=UnweightedCayleySource.sourceFKAction c) ∧
 (PA.E (UnweightedCayleySource.sourceFKAction c)=0) ∧
 ((PA.Q (Old.sourceFK c) : BurnolL2)=(UnweightedCayleySource.sourceForwardRatio c/δ) • Kbar-δ⁻¹ • FK) ∧
 (Old.unitAdjointSource c=unitAdjointField c) ∧
 (inner ℂ Kbar targetRaw=nextBarPrice c inputRaw) ∧
 (inner ℂ Kbar rawNext=nextBarPrice c raw) ∧
 (inner ℂ Kbar bornRaw=nextBarPrice c raw) ∧
 (inner ℂ receiptK (unitQuery bornRaw)=inner ℂ (unitAdjointField c) bornRaw) ∧
 type_of% (RC.original_whole factory initial cfg rfl (ordinal+1)) ∧
 type_of% (RC.actual_generated_current factory initial cfg rfl (ordinal+1)) := by
 apply consume_actual_normal_source observation nontrivial half depth ordinal
 intro adjointSource sourceAnchor state trace sourceInput targetAction bornBranches divisionRead orthogonal whole next
 have actualR : burnolDirectRightResolvent ((c).value/2) raw=rawNext := by
  rw [D.raw_successor,OriginalKCombCofinalRAction.original_R_direct]
  rfl
 have rawPrice:=conjugateK_R_price c raw
 rw [actualR] at rawPrice
 have target : targetRaw=rawNext := targetAction.2.2.trans (D.raw_successor observation nontrivial half depth ordinal).symm
 have normalPrice : inner ℂ Kbar targetRaw=nextBarPrice c inputRaw := by rw [target,sourceInput];exact rawPrice
 have calculated:=Full.complete_of_branches observation nontrivial half _ _ bornBranches
 have bornR : bornRaw=P.R observation nontrivial half raw := calculated.2.2.1
 have bornToRaw : bornRaw=rawNext := bornR.trans (D.raw_successor observation nontrivial half depth ordinal).symm
 have bornPrice : inner ℂ Kbar bornRaw=nextBarPrice c raw := by rw [bornToRaw];exact rawPrice
 have kernel : receiptK=K :=
  (congrArg (fun receipt : OriginalRieszFiniteSource.Receipt=>receipt.kernel) sourceAnchor).trans (generatedK_eq_original c).symm
 have unitPrice : inner ℂ receiptK (unitQuery bornRaw)=inner ℂ (unitAdjointField c) bornRaw := by
  rw [kernel]
  exact original_unit_price c bornRaw
 have original:=original_FK_source_fields c
 have Qreturn:=actual_FK_Q_return observation nontrivial half
 exact ⟨CayleyIntertwiningMaterialConsumer.actual_weighted_return_on_original_whole_next observation nontrivial half depth ordinal,
  OriginalKDirectRCofinalCalculatedSource.calculated_material_target_from observation nontrivial half depth ordinal state,
  OriginalKDirectRCofinalCalculatedSource.calculated_face_history_from observation nontrivial half depth ordinal trace,
  original.1,original.2,Qreturn.1,Qreturn.2,original_unit_adjoint_actual c,
  normalPrice,rawPrice,bornPrice,unitPrice,whole,next⟩

theorem actual_return_born_consumer :
 type_of% (CayleyIntertwiningMaterialConsumer.actual_weighted_return_born_consumer observation nontrivial half depth ordinal) ∧
 (Old.sourceFK c=UnweightedCayleySource.sourceFKAction c) ∧
 type_of% (actual_FK_Q_return observation nontrivial half) ∧
 (Old.unitAdjointSource c=unitAdjointField c) ∧
 (inner ℂ Kbar bornRaw=nextBarPrice c raw) ∧
 (inner ℂ receiptK (unitQuery bornRaw)=inner ℂ (unitAdjointField c) bornRaw) ∧
 type_of% (RC.original_whole factory initial cfg rfl (ordinal+1)) ∧
 type_of% (RC.actual_generated_current factory initial cfg rfl (ordinal+1)) := by
 have actual:=actual_return_on_original_whole_next observation nontrivial half depth ordinal
 exact ⟨CayleyIntertwiningMaterialConsumer.actual_weighted_return_born_consumer observation nontrivial half depth ordinal,
  actual.2.2.2.2.1,⟨actual.2.2.2.2.2.1,actual.2.2.2.2.2.2.1⟩,actual.2.2.2.2.2.2.2.1,
  actual.2.2.2.2.2.2.2.2.2.2.1,actual.2.2.2.2.2.2.2.2.2.2.2.1,
  actual.2.2.2.2.2.2.2.2.2.2.2.2.1,actual.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Zero coupling retains the entire independent FK and outside columns. -/
theorem zero_sigma_forward_override (zero : σ=0) :
 Old.sourceFK c= -(δ⁻¹ • FK)-(2*((‖K‖^2:ℝ):ℂ)) • V := by
 rw [(original_FK_source_fields c).2]
 simp only [UnweightedCayleySource.sourceFKAction,UnweightedCayleySource.sourceForwardRatio,zero,
  zero_div,zero_smul,zero_sub]

theorem actual_zero_outside_price_override (zero : outsidePrice c raw=0) :
 inner ℂ Kbar bornRaw=star (UnweightedCayleySource.sourceAdjointRatio c/δ)*inner ℂ FK raw-
  star (δ⁻¹)*inner ℂ Kbar raw := by
 have actual:=(actual_return_born_consumer observation nontrivial half depth ordinal).2.2.2.2.1
 simpa only [nextBarPrice,zero,sub_zero] using actual

theorem actual_zero_sigma_next_override (zero : σ=0) :
 inner ℂ Kbar bornRaw= -star (δ⁻¹)*inner ℂ Kbar raw-outsidePrice c raw := by
 have actual:=(actual_return_born_consumer observation nontrivial half depth ordinal).2.2.2.2.1
 simpa only [nextBarPrice,UnweightedCayleySource.sourceAdjointRatio,zero,star_zero,zero_div,zero_mul,zero_sub,neg_mul] using actual

theorem nonzero_full_outside_column_cannot_be_dropped
 (nonzero : (2*((‖K‖^2:ℝ):ℂ)) • V≠0) :
 Old.sourceFK c≠(UnweightedCayleySource.sourceForwardRatio c/δ) • Kbar-δ⁻¹ • FK := by
 intro erased
 have actual:=(original_FK_source_fields c).2
 unfold UnweightedCayleySource.sourceFKAction at actual
 rw [erased] at actual
 exact nonzero (sub_eq_self.mp actual.symm)

theorem actual_nonzero_outside_price_cannot_be_dropped (nonzero : outsidePrice c raw≠0) :
 inner ℂ Kbar bornRaw≠star (UnweightedCayleySource.sourceAdjointRatio c/δ)*inner ℂ FK raw-
  star (δ⁻¹)*inner ℂ Kbar raw := by
 intro erased
 have actual:=(actual_return_born_consumer observation nontrivial half depth ordinal).2.2.2.2.1
 change _=(_-_)-outsidePrice c raw at actual
 rw [erased] at actual
 exact nonzero (sub_eq_self.mp actual.symm)

end OriginalKCrossParameterRAdjointSource.UnweightedCayleyMaterialConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
