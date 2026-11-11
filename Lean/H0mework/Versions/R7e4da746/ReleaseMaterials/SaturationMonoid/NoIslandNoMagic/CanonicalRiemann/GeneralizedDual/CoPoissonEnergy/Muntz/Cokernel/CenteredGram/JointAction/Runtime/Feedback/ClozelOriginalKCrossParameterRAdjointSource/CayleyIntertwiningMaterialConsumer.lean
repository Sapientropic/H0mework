import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CayleyIntertwiningSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CrossUnitKSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CayleyEnergyMaterialConsumer

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_weighted_return_on_original_whole_next"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_weighted_return_born_consumer"
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCrossParameterRAdjointSource.CayleyIntertwiningMaterialConsumer
open Complex MeasureTheory Set BurnolPhysicalState
open OriginalKDirectRCofinalMaterial OriginalKFullAdjointSource OriginalKDirectRCofinalOutsideVolterraSource
open OriginalKSourceResolventReconstruction
open SourceOperationScalarInventoryLift OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing.CoPoisson.Ward
open scoped InnerProductSpace
namespace Old
export OriginalKElementaryArithmeticAction.FullOriginalRUnitSource
 (sourceFK unitAdjointSource unit_adjoint_source full_original_R_fields)
end Old
namespace PA
export OriginalKCombCofinalPaAction (E Q wholePa_normal_read)
end PA
local instance returnMaterialGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
local instance returnMaterialComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "δ" => (CayleyEnergySource.sourceDamping c : ℂ)
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "K" => generatedK c
local notation "Kbar" => generatedK (barC c)
local notation "FK" => fourierL2 K
local notation "W" => hPowerPhysicalCorrection c
local notation "V" => PhysicalOutsideSource.physicalOutsideColumn c
local notation "a" => (((‖W‖^2:ℝ):ℂ))
local notation "b" => (((‖hPowerPhysicalCorrection (barC c)‖^2:ℝ):ℂ))
local notation "kn" => (((‖K‖^2:ℝ):ℂ))
local notation "kbn" => (((‖Kbar‖^2:ℝ):ℂ))
local notation "σ" => CayleyIntertwiningSource.sourceSigma c
local notation "outside" => P.physicalRemainder
local notation "unitQuery" => OriginalKElementaryArithmeticAction.unitResolventSource c

def weightedForwardReturn : BurnolL2 := σ • Kbar-b • FK-(2*δ*b*kn) • V
def weightedUnitAdjoint : BurnolL2 :=
 star (star (c).value*GapEuler.gapMean (1/4) c) •
  ((δ*b) • K-star ((1-star (c).value)/2) • fourierL2 (weightedForwardReturn observation half))
def outsideFeedback (value : BurnolL2) : ℂ := star (a*(2*δ*kbn))*inner ℂ W (outside value)
def nextBarPrice (value : BurnolL2) : ℂ :=
 σ*inner ℂ FK value-star a*inner ℂ Kbar value-outsideFeedback observation half value

include nontrivial in
/-- The new cross price pays this true Pa return before Q is read. -/
theorem actual_FK_Pa_return_zero :
 PA.E FK=0 ∧ PA.E (burnolDirectRightResolvent ((c).value/2) FK)=0 ∧ PA.E (Old.sourceFK c)=0 := by
 let f:=evenFaceFourierEquiv burnolUnscaledCommonGapRadius
 let k:=burnolCompletedMellinRieszVector c
 have original:=riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal c observation.mathlibZero
 have Fourier : f k∈burnolCompactCoPoissonClosedRange.toSubmoduleᗮ := by
  intro g inside
  have FgPa:=burnolCompactCoPoissonActionSquare.toIsometricSquare.target_mem_closedRange inside
  have killed:=original (f g) FgPa
  have paired:=(evenFaceFourierEquiv burnolUnscaledCommonGapRadius).inner_map_map (f g) k
  have invol : f (f g)=g := evenFaceFourier_involutive burnolUnscaledCommonGapRadius g
  change inner ℂ (f (f g)) (f k)=inner ℂ (f g) k at paired
  rw [invol] at paired
  exact paired.trans killed
 have own : PA.E FK∈burnolCompactCoPoissonClosedRange := Submodule.starProjection_apply_mem _ _
 have self : inner ℂ (PA.E FK) (PA.E FK)=0 := by
  rw [PA.wholePa_normal_read FK (PA.E FK) own]
  have killed:=Fourier (PA.E FK) own
  change inner ℂ (PA.E FK : BurnolL2) (fourierL2 (burnolCompletedMellinRieszVector c : BurnolL2))=0 at killed
  simpa only [generatedK_eq_original] using killed
 have Ezero : PA.E FK=0 := inner_self_eq_zero.mp self
 have returned:=OriginalKDirectRCofinalReentrySourceAction.full_pa_reentry_action c FK Ezero
 change PA.E (burnolDirectRightResolvent ((c).value/2) FK)=
  inner ℂ (fourierL2 (burnolUnitTailResponse (barC c) 4)) FK •
   (OriginalKDirectRCofinalReentrySourceAction.sourceReentryVector c : BurnolPaAmbientCarrier) at returned
 rw [CrossUnitKSource.conjugate_unit_FK_reentry_price_zero observation nontrivial half,zero_smul] at returned
 have old : burnolDirectRightResolvent ((c).value/2) FK=Old.sourceFK c := by
  simpa only [generatedK_eq_original] using (Old.full_original_R_fields c).2
 exact ⟨Ezero,returned,(congrArg PA.E old).symm.trans returned⟩

/-- Both existing original full-R source mouths are consumed before their complete weighted field is read. -/
theorem weighted_forward_source_actual :
 (δ*b) • Old.sourceFK c=weightedForwardReturn observation half := by
 have cross : burnolDirectRightResolvent ((c).value/2) FK=sourceFKResponse c c := by
  simpa only [generatedK_eq_original] using source_FK_response c c
 have old : burnolDirectRightResolvent ((c).value/2) FK=Old.sourceFK c := by
  simpa only [generatedK_eq_original] using (Old.full_original_R_fields c).2
 have aligned:=cross.symm.trans old
 have generated:=CayleyIntertwiningSource.source_FK_full_action c
 rw [cross,aligned] at generated
 unfold weightedForwardReturn
 linear_combination (norm := module) generated

include nontrivial in
theorem weighted_Q_forward_source_actual :
 (δ*b) • (PA.Q (Old.sourceFK c) : BurnolL2)=σ • Kbar-b • FK := by
 have prior:=actual_FK_Pa_return_zero observation nontrivial half
 have split:=burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_add_starProjection_orthogonal
  (burnolEvenAmbientProjection (Old.sourceFK c))
 have inventory:=congrArg (fun value : BurnolPaAmbientCarrier=>(value : BurnolL2)) split
 change (PA.E (Old.sourceFK c) : BurnolL2)+(PA.Q (Old.sourceFK c) : BurnolL2)=
  (burnolEvenAmbientProjection (Old.sourceFK c) : BurnolL2) at inventory
 rw [prior.2.2,ZeroMemClass.coe_zero,zero_add] at inventory
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
 have projected:=congrArg burnolEvenAmbientProjectionEndomorphism (weighted_forward_source_actual observation half)
 unfold weightedForwardReturn at projected
 rw [map_smul,map_sub,map_sub,map_smul,map_smul,map_smul] at projected
 change (δ*b) • (burnolEvenAmbientProjection (Old.sourceFK c) : BurnolL2)=
  σ • (burnolEvenAmbientProjection Kbar : BurnolL2)-b • (burnolEvenAmbientProjection FK : BurnolL2)-
   (2*δ*b*kn) • (burnolEvenAmbientProjection V : BurnolL2) at projected
 rw [pK,pFK,pV,smul_zero,sub_zero,←inventory] at projected
 exact projected

/-- The complete Fourier source enters the old unit-adjoint formula with its actual original coefficients. -/
theorem weighted_unit_adjoint_actual : (δ*b) • Old.unitAdjointSource c=weightedUnitAdjoint observation half := by
 unfold weightedUnitAdjoint Old.unitAdjointSource
 rw [←weighted_forward_source_actual observation half,map_smul]
 module

theorem weighted_unit_source_price (value : BurnolL2) :
 star (δ*b)*inner ℂ K (unitQuery value)=inner ℂ (weightedUnitAdjoint observation half) value := by
 rw [generatedK_eq_original,Old.unit_adjoint_source,←weighted_unit_adjoint_actual observation half,inner_smul_left]
 simp only [starRingEnd_apply,star_mul]

/-- This is duality of the full original R on the complete input, including its whole outside price. -/
theorem weighted_conjugateK_R_price (value : BurnolL2) :
 star (a*δ)*inner ℂ Kbar (burnolDirectRightResolvent ((c).value/2) value)=nextBarPrice observation half value := by
 have action:=CayleyIntertwiningSource.source_conjugateK_full_adjoint_action c
 have paired:=congrArg (fun field : BurnolL2=>inner ℂ field value) action
 simp only [inner_smul_left,inner_add_left] at paired
 have right : 1/4<((c).value/2).re := by rw [Complex.div_re];norm_num;linarith [(c).rightHalf]
 have dual:=OriginalKCompactAdjointRSource.actual_original_R_adjoint ((c).value/2) right Kbar value
 simp only [star_div₀,star_ofNat] at dual
 change inner ℂ Kbar (burnolDirectRightResolvent ((c).value/2) value)=inner ℂ (sourceAdjoint c Kbar) value at dual
 rw [←dual] at paired
 have stock:=(evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmoduleᗮ.inner_orthogonalProjectionOnto_eq_of_mem_left
  ⟨W,CayleyIntertwiningSource.powerCorrection_orthogonal c⟩ value
 change inner ℂ W (outside value)=inner ℂ W value at stock
 rw [←stock] at paired
 change star a*(inner ℂ Kbar value+star δ*inner ℂ Kbar (burnolDirectRightResolvent ((c).value/2) value)+
  star (2*δ*kbn)*inner ℂ W (outside value))=star (star σ)*inner ℂ FK value at paired
 simp only [star_star] at paired
 unfold nextBarPrice outsideFeedback
 simp only [star_mul] at paired ⊢
 linear_combination paired

variable (depth ordinal : Nat)
local notation "raw" => D.raw observation nontrivial half depth ordinal
local notation "rawNext" => D.raw observation nontrivial half depth (ordinal+1)
local notation "inputRaw" => OriginalKDirectRCofinalCalculatedSource.calculatedInputRaw observation nontrivial half depth ordinal
local notation "targetRaw" => OriginalKDirectRCofinalCalculatedSource.calculatedTargetRaw observation nontrivial half depth ordinal
local notation "bornRaw" => OriginalKDirectRCofinalPaUpdate.DirectRPaUpdateControls.bornRead observation nontrivial half depth ordinal
local notation "receiptK" => (installedOriginalKReceiptAt observation nontrivial half.down).kernel
local notation "factory" => D.factory observation nontrivial half
local notation "initial" => D.initial observation nontrivial half depth
local notation "cfg" => D.firstCfg observation nontrivial half depth

/-- New complete vector returns and weighted next prices are consumed on the actual original normal and born. -/
theorem actual_weighted_return_on_original_whole_next :
 type_of% (CayleyEnergyMaterialConsumer.actual_energy_on_original_whole_next observation nontrivial half depth ordinal) ∧
 type_of% (OriginalKDirectRCofinalCalculatedSource.calculated_material_target_from observation nontrivial half depth ordinal
  (OriginalKDirectRCofinalCalculatedSource.actual_material_calculated_state observation nontrivial half depth ordinal)) ∧
 type_of% (OriginalKDirectRCofinalCalculatedSource.calculated_face_history_from observation nontrivial half depth ordinal
  (OriginalKDirectRCofinalCalculatedSource.actual_material_calculated_history observation nontrivial half depth ordinal)) ∧
 type_of% (actual_FK_Pa_return_zero observation nontrivial half) ∧
 ((δ*b) • Old.sourceFK c=weightedForwardReturn observation half) ∧
 ((δ*b) • (PA.Q (Old.sourceFK c) : BurnolL2)=σ • Kbar-b • FK) ∧
 ((δ*b) • Old.unitAdjointSource c=weightedUnitAdjoint observation half) ∧
 (star (a*δ)*inner ℂ Kbar targetRaw=nextBarPrice observation half inputRaw) ∧
 (star (a*δ)*inner ℂ Kbar rawNext=nextBarPrice observation half raw) ∧
 (star (a*δ)*inner ℂ Kbar bornRaw=nextBarPrice observation half raw) ∧
 (star (δ*b)*inner ℂ receiptK (unitQuery bornRaw)=inner ℂ (weightedUnitAdjoint observation half) bornRaw) ∧
 type_of% (RC.original_whole factory initial cfg rfl (ordinal+1)) ∧
 type_of% (RC.actual_generated_current factory initial cfg rfl (ordinal+1)) := by
 apply consume_actual_normal_source observation nontrivial half depth ordinal
 intro adjointSource sourceAnchor state trace sourceInput targetAction bornBranches divisionRead orthogonal whole next
 have actualR : burnolDirectRightResolvent ((c).value/2) raw=rawNext := by
  rw [D.raw_successor,OriginalKCombCofinalRAction.original_R_direct]
  rfl
 have rawPrice:=weighted_conjugateK_R_price observation half raw
 rw [actualR] at rawPrice
 have target : targetRaw=rawNext := targetAction.2.2.trans (D.raw_successor observation nontrivial half depth ordinal).symm
 have normalPrice : star (a*δ)*inner ℂ Kbar targetRaw=nextBarPrice observation half inputRaw := by
  rw [target,sourceInput]
  exact rawPrice
 have calculated:=Full.complete_of_branches observation nontrivial half _ _ bornBranches
 have bornR : bornRaw=P.R observation nontrivial half raw := calculated.2.2.1
 have bornToRaw : bornRaw=rawNext := bornR.trans (D.raw_successor observation nontrivial half depth ordinal).symm
 have bornPrice : star (a*δ)*inner ℂ Kbar bornRaw=nextBarPrice observation half raw := by rw [bornToRaw];exact rawPrice
 have kernel : receiptK=K :=
  (congrArg (fun receipt : OriginalRieszFiniteSource.Receipt=>receipt.kernel) sourceAnchor).trans (generatedK_eq_original c).symm
 have unitPrice : star (δ*b)*inner ℂ receiptK (unitQuery bornRaw)=inner ℂ (weightedUnitAdjoint observation half) bornRaw := by
  rw [kernel]
  exact weighted_unit_source_price observation half bornRaw
 exact ⟨CayleyEnergyMaterialConsumer.actual_energy_on_original_whole_next observation nontrivial half depth ordinal,
  OriginalKDirectRCofinalCalculatedSource.calculated_material_target_from observation nontrivial half depth ordinal state,
  OriginalKDirectRCofinalCalculatedSource.calculated_face_history_from observation nontrivial half depth ordinal trace,
  actual_FK_Pa_return_zero observation nontrivial half,weighted_forward_source_actual observation half,
  weighted_Q_forward_source_actual observation nontrivial half,weighted_unit_adjoint_actual observation half,
  normalPrice,rawPrice,bornPrice,unitPrice,whole,next⟩

theorem actual_weighted_return_born_consumer :
 type_of% (PhysicalDefectMaterialConsumer.actual_born_decoder_coupled_consumer observation nontrivial half depth ordinal) ∧
 type_of% (actual_FK_Pa_return_zero observation nontrivial half) ∧
 ((δ*b) • Old.sourceFK c=weightedForwardReturn observation half) ∧
 ((δ*b) • (PA.Q (Old.sourceFK c) : BurnolL2)=σ • Kbar-b • FK) ∧
 ((δ*b) • Old.unitAdjointSource c=weightedUnitAdjoint observation half) ∧
 (star (a*δ)*inner ℂ Kbar bornRaw=nextBarPrice observation half raw) ∧
 (star (δ*b)*inner ℂ receiptK (unitQuery bornRaw)=inner ℂ (weightedUnitAdjoint observation half) bornRaw) ∧
 type_of% (RC.original_whole factory initial cfg rfl (ordinal+1)) ∧
 type_of% (RC.actual_generated_current factory initial cfg rfl (ordinal+1)) := by
 have actual:=actual_weighted_return_on_original_whole_next observation nontrivial half depth ordinal
 exact ⟨PhysicalDefectMaterialConsumer.actual_born_decoder_coupled_consumer observation nontrivial half depth ordinal,
  actual.2.2.2.1,actual.2.2.2.2.1,actual.2.2.2.2.2.1,actual.2.2.2.2.2.2.1,
  actual.2.2.2.2.2.2.2.2.2.1,actual.2.2.2.2.2.2.2.2.2.2.1,
  actual.2.2.2.2.2.2.2.2.2.2.2.1,actual.2.2.2.2.2.2.2.2.2.2.2.2⟩

theorem actual_zero_sigma_override (zero : σ=0) :
 star (a*δ)*inner ℂ Kbar bornRaw= -star a*inner ℂ Kbar raw-outsideFeedback observation half raw := by
 have actual:=(actual_weighted_return_born_consumer observation nontrivial half depth ordinal).2.2.2.2.2.1
 simpa only [nextBarPrice,zero,zero_mul,zero_sub,neg_mul] using actual

theorem zero_forward_weight_preserves_degenerate_source (zero : b=0) : σ • Kbar=0 := by
 have actual:=CayleyIntertwiningSource.source_FK_full_action c
 simpa only [zero,zero_smul] using actual.symm

theorem actual_nonzero_outside_feedback_cannot_be_dropped (nonzero : outsideFeedback observation half raw≠0) :
 star (a*δ)*inner ℂ Kbar bornRaw≠σ*inner ℂ FK raw-star a*inner ℂ Kbar raw := by
 intro erased
 have actual:=(actual_weighted_return_born_consumer observation nontrivial half depth ordinal).2.2.2.2.2.1
 change _=(_-_)-outsideFeedback observation half raw at actual
 rw [erased] at actual
 exact nonzero (sub_eq_self.mp actual.symm)

include nontrivial in
/-- Only the actual conjugate-unit coefficient pays this Pa return; a replacement with nonzero effect fails. -/
theorem actual_cross_price_cannot_be_replaced (price : ℂ)
 (changes : price • (OriginalKDirectRCofinalReentrySourceAction.sourceReentryVector c : BurnolPaAmbientCarrier)≠0) :
 PA.E (burnolDirectRightResolvent ((c).value/2) FK)≠
  price • (OriginalKDirectRCofinalReentrySourceAction.sourceReentryVector c : BurnolPaAmbientCarrier) := by
 rw [(actual_FK_Pa_return_zero observation nontrivial half).2.1]
 exact Ne.symm changes

end OriginalKCrossParameterRAdjointSource.CayleyIntertwiningMaterialConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
