import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.BPowerCayleySource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.UnweightedCayleyMaterialConsumer

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_power_return_on_original_whole_next"
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_power_return_born_consumer"
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCrossParameterRAdjointSource.BPowerCayleyMaterialConsumer
open Complex MeasureTheory Set BurnolPhysicalState
open OriginalKDirectRCofinalMaterial OriginalKFullAdjointSource OriginalKDirectRCofinalOutsideVolterraSource
open OriginalKSourceResolventReconstruction SourceOperationScalarInventoryLift
open scoped InnerProductSpace
local instance powerMaterialGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
local instance powerMaterialComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def powerPrice (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) : ℂ :=
 inner ℂ (hPowerPhysicalCorrection coordinate) (P.physicalRemainder value)
def columnPrice (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) : ℂ :=
 inner ℂ (PhysicalOutsideSource.physicalOutsideColumn coordinate) (P.physicalRemainder value)

private theorem power_outside_read (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
 inner ℂ (hPowerPhysicalCorrection coordinate) value=powerPrice coordinate value := by
 symm
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmoduleᗮ.inner_orthogonalProjectionOnto_eq_of_mem_left
  ⟨hPowerPhysicalCorrection coordinate,CayleyIntertwiningSource.powerCorrection_orthogonal coordinate⟩ value
private theorem column_outside_read (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
 inner ℂ (PhysicalOutsideSource.physicalOutsideColumn coordinate) value=columnPrice coordinate value := by
 symm
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmoduleᗮ.inner_orthogonalProjectionOnto_eq_of_mem_left
  ⟨PhysicalOutsideSource.physicalOutsideColumn coordinate,CayleyIntertwiningSource.outsideColumn_orthogonal coordinate⟩ value

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "δ" => (CayleyEnergySource.sourceDamping c : ℂ)
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "Kbar" => generatedK (barC c)
local notation "FK" => fourierL2 (generatedK c)
local notation "W" => hPowerPhysicalCorrection c
local notation "V" => PhysicalOutsideSource.physicalOutsideColumn c
local notation "A" => ((‖W‖^2:ℝ):ℂ)
local notation "B" => ((‖hPowerPhysicalCorrection (barC c)‖^2:ℝ):ℂ)
local notation "g" => BPowerCayleySource.sourcePowerCoupling observation half
local notation "h" => BPowerCayleySource.sourceReturnCoupling observation half
local notation "σ" => CayleyIntertwiningSource.sourceSigma c

def nextColumnPrice (value : BurnolL2) : ℂ :=
 -2*B*inner ℂ FK (burnolEvenAmbientProjection value:BurnolL2)-
  δ⁻¹*(columnPrice c value+star h*powerPrice c value)
def inversePowerPrice (current born : BurnolL2) : ℂ :=
 -2*δ*A*(inner ℂ Kbar current+δ*inner ℂ Kbar born)-
  star g*(columnPrice c current+δ*columnPrice c born)

include nontrivial in
/-- The true complete column adjoint reads the full physical Pa+Q input and both outside prices. -/
theorem original_R_column_price (value : BurnolL2) :
 columnPrice c (burnolDirectRightResolvent ((c).value/2) value)=nextColumnPrice observation half value := by
 exact BPowerCayleySource.original_R_outside_pair_action observation nontrivial half value

include nontrivial in
/-- Full UW and preservation of the original inner product write the computed update back to its input. -/
theorem original_R_power_writeback (value : BurnolL2) :
 powerPrice c value=inversePowerPrice observation half value (burnolDirectRightResolvent ((c).value/2) value) := by
 have generated:=CayleyEnergySource.sourceCayley_inner c W value
 have power : CayleyEnergySource.sourceCayley c W=(-2*δ*A) • Kbar-g • V :=
  BPowerCayleySource.actual_power_cayley_source observation nontrivial half
 rw [power,CayleyEnergySource.sourceCayley_apply] at generated
 simp only [inner_sub_left,inner_smul_left,inner_add_right,inner_smul_right] at generated
 have dampingStar : star δ=δ := Complex.conj_ofReal _
 have massStar : star A=A := Complex.conj_ofReal _
 simp only [starRingEnd_apply,star_mul,star_neg,star_ofNat,dampingStar,massStar] at generated
 rw [column_outside_read c value,column_outside_read c (burnolDirectRightResolvent ((c).value/2) value),
  power_outside_read c value] at generated
 unfold inversePowerPrice
 linear_combination -generated

variable (depth ordinal : Nat)
local notation "raw" => D.raw observation nontrivial half depth ordinal
local notation "rawNext" => D.raw observation nontrivial half depth (ordinal+1)
local notation "inputRaw" => OriginalKDirectRCofinalCalculatedSource.calculatedInputRaw observation nontrivial half depth ordinal
local notation "targetRaw" => OriginalKDirectRCofinalCalculatedSource.calculatedTargetRaw observation nontrivial half depth ordinal
local notation "bornRaw" => OriginalKDirectRCofinalPaUpdate.DirectRPaUpdateControls.bornRead observation nontrivial half depth ordinal
local notation "factory" => D.factory observation nontrivial half
local notation "initial" => D.initial observation nontrivial half depth
local notation "cfg" => D.firstCfg observation nontrivial half depth

/-- The original action generates this born before the two-time conservation law reads it back. -/
theorem actual_power_return_on_original_whole_next :
 type_of% (UnweightedCayleyMaterialConsumer.actual_return_on_original_whole_next observation nontrivial half depth ordinal) ∧
 type_of% (OriginalKDirectRCofinalCalculatedSource.calculated_material_target_from observation nontrivial half depth ordinal
  (OriginalKDirectRCofinalCalculatedSource.actual_material_calculated_state observation nontrivial half depth ordinal)) ∧
 type_of% (OriginalKDirectRCofinalCalculatedSource.calculated_face_history_from observation nontrivial half depth ordinal
  (OriginalKDirectRCofinalCalculatedSource.actual_material_calculated_history observation nontrivial half depth ordinal)) ∧
 (CayleyEnergySource.sourceCayley c W=BPowerCayleySource.sourcePowerCayley observation half) ∧
 (sourceAdjoint c V=δ⁻¹ • (BPowerCayleySource.sourceColumnAdjointCayley observation half-V)) ∧
 (CayleyEnergySource.sourceCayley c inputRaw=inputRaw+δ • targetRaw) ∧
 (CayleyEnergySource.sourceCayley c raw=raw+δ • bornRaw) ∧
 (columnPrice c targetRaw=nextColumnPrice observation half inputRaw) ∧
 (columnPrice c rawNext=nextColumnPrice observation half raw) ∧
 (columnPrice c bornRaw=nextColumnPrice observation half raw) ∧
 (powerPrice c inputRaw=inversePowerPrice observation half inputRaw targetRaw) ∧
 (powerPrice c raw=inversePowerPrice observation half raw rawNext) ∧
 (powerPrice c raw=inversePowerPrice observation half raw bornRaw) ∧
 type_of% (RC.original_whole factory initial cfg rfl (ordinal+1)) ∧
 type_of% (RC.actual_generated_current factory initial cfg rfl (ordinal+1)) := by
 apply consume_actual_normal_source observation nontrivial half depth ordinal
 intro adjointSource sourceAnchor state trace sourceInput targetAction bornBranches divisionRead orthogonal whole next
 have actualR : burnolDirectRightResolvent ((c).value/2) raw=rawNext := by
  rw [D.raw_successor,OriginalKCombCofinalRAction.original_R_direct]
  rfl
 have target : targetRaw=rawNext := targetAction.2.2.trans (D.raw_successor observation nontrivial half depth ordinal).symm
 have calculated:=Full.complete_of_branches observation nontrivial half _ _ bornBranches
 have bornR : bornRaw=P.R observation nontrivial half raw := calculated.2.2.1
 have bornToRaw : bornRaw=rawNext := bornR.trans (D.raw_successor observation nontrivial half depth ordinal).symm
 have generatedRaw : CayleyEnergySource.sourceCayley c raw=raw+δ • bornRaw := by
  rw [CayleyEnergySource.sourceCayley_apply,actualR,bornToRaw]
 have generatedNormal : CayleyEnergySource.sourceCayley c inputRaw=inputRaw+δ • targetRaw := by
  rw [sourceInput,target,←bornToRaw]
  exact generatedRaw
 have rawPrice:=original_R_column_price observation nontrivial half raw
 have rawWriteback:=original_R_power_writeback observation nontrivial half raw
 rw [actualR] at rawPrice rawWriteback
 have normalPrice : columnPrice c targetRaw=nextColumnPrice observation half inputRaw := by
  rw [sourceInput,target]
  exact rawPrice
 have bornPrice : columnPrice c bornRaw=nextColumnPrice observation half raw := by rw [bornToRaw];exact rawPrice
 have normalWriteback : powerPrice c inputRaw=inversePowerPrice observation half inputRaw targetRaw := by
  rw [sourceInput,target]
  exact rawWriteback
 have bornWriteback : powerPrice c raw=inversePowerPrice observation half raw bornRaw := by
  rw [bornToRaw]
  exact rawWriteback
 exact ⟨UnweightedCayleyMaterialConsumer.actual_return_on_original_whole_next observation nontrivial half depth ordinal,
  OriginalKDirectRCofinalCalculatedSource.calculated_material_target_from observation nontrivial half depth ordinal state,
  OriginalKDirectRCofinalCalculatedSource.calculated_face_history_from observation nontrivial half depth ordinal trace,
  BPowerCayleySource.actual_power_cayley_source observation nontrivial half,
  BPowerCayleySource.actual_R_adjoint_column_source observation nontrivial half,
  generatedNormal,generatedRaw,normalPrice,rawPrice,bornPrice,normalWriteback,rawWriteback,bornWriteback,whole,next⟩

/-- The independent consumer retains the original complete born decoder and consumes both actual directions. -/
theorem actual_power_return_born_consumer :
 type_of% (UnweightedCayleyMaterialConsumer.actual_return_born_consumer observation nontrivial half depth ordinal) ∧
 (CayleyEnergySource.sourceCayley c raw=raw+δ • bornRaw) ∧
 (columnPrice c bornRaw=nextColumnPrice observation half raw) ∧
 (powerPrice c raw=inversePowerPrice observation half raw bornRaw) ∧
 type_of% (RC.original_whole factory initial cfg rfl (ordinal+1)) ∧
 type_of% (RC.actual_generated_current factory initial cfg rfl (ordinal+1)) := by
 have actual:=actual_power_return_on_original_whole_next observation nontrivial half depth ordinal
 exact ⟨UnweightedCayleyMaterialConsumer.actual_return_born_consumer observation nontrivial half depth ordinal,
  actual.2.2.2.2.2.2.1,actual.2.2.2.2.2.2.2.2.2.1,
  actual.2.2.2.2.2.2.2.2.2.2.2.2.1,actual.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
  actual.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- A zero current power price leaves the full physical and current-column terms in the forward price. -/
theorem actual_zero_power_price_override (zero : powerPrice c raw=0) :
 columnPrice c bornRaw= -2*B*inner ℂ FK (burnolEvenAmbientProjection raw:BurnolL2)-δ⁻¹*columnPrice c raw := by
 have actual:=(actual_power_return_born_consumer observation nontrivial half depth ordinal).2.2.1
 simpa only [nextColumnPrice,zero,mul_zero,add_zero] using actual

/-- Zero current V price preserves both generated future V cost and both Kbar time faces. -/
theorem actual_zero_column_price_writeback_override (zero : columnPrice c raw=0) :
 powerPrice c raw= -2*δ*A*(inner ℂ Kbar raw+δ*inner ℂ Kbar bornRaw)-star g*(δ*columnPrice c bornRaw) := by
 have actual:=(actual_power_return_born_consumer observation nontrivial half depth ordinal).2.2.2.1
 simpa only [inversePowerPrice,zero,zero_add] using actual

/-- When sigma vanishes, the independently generated Kbar two-time responsibility remains. -/
theorem actual_zero_sigma_writeback_override (zero : σ=0) :
 powerPrice c raw= -2*δ*A*(inner ℂ Kbar raw+δ*inner ℂ Kbar bornRaw) := by
 have actual:=(actual_power_return_born_consumer observation nontrivial half depth ordinal).2.2.2.1
 simpa only [inversePowerPrice,BPowerCayleySource.sourcePowerCoupling,UnweightedCayleySource.sourceAdjointRatio,
  zero,star_zero,zero_div,zero_mul,zero_smul,mul_zero,sub_zero] using actual

theorem actual_zero_sigma_forward_override (zero : σ=0) :
 columnPrice c bornRaw= -2*B*inner ℂ FK (burnolEvenAmbientProjection raw:BurnolL2)-δ⁻¹*columnPrice c raw := by
 have actual:=(actual_power_return_born_consumer observation nontrivial half depth ordinal).2.2.1
 simpa only [nextColumnPrice,BPowerCayleySource.sourceReturnCoupling,UnweightedCayleySource.sourceForwardRatio,
  zero,zero_div,zero_mul,star_zero,mul_zero,add_zero] using actual

/-- The weighted actual cost, rather than an unweighted W read, controls erasure. -/
theorem actual_nonzero_weighted_power_cost_cannot_be_dropped
 (nonzero : δ⁻¹*(star h*powerPrice c raw)≠0) :
 columnPrice c bornRaw≠ -2*B*inner ℂ FK (burnolEvenAmbientProjection raw:BurnolL2)-δ⁻¹*columnPrice c raw := by
 intro erased
 have actual:=(actual_power_return_born_consumer observation nontrivial half depth ordinal).2.2.1
 change _=(_)-δ⁻¹*(_+_) at actual
 rw [erased,mul_add,←sub_sub] at actual
 exact nonzero (sub_eq_self.mp actual.symm)

theorem actual_nonzero_weighted_column_cost_cannot_be_dropped
 (nonzero : star g*(columnPrice c raw+δ*columnPrice c bornRaw)≠0) :
 powerPrice c raw≠ -2*δ*A*(inner ℂ Kbar raw+δ*inner ℂ Kbar bornRaw) := by
 intro erased
 have actual:=(actual_power_return_born_consumer observation nontrivial half depth ordinal).2.2.2.1
 change _=(_)-star g*(_+_) at actual
 rw [erased] at actual
 exact nonzero (sub_eq_self.mp actual.symm)

end OriginalKCrossParameterRAdjointSource.BPowerCayleyMaterialConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
