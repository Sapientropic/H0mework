import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCenteredMobiusRSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerJordanMaterialConsumer

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "CofinalCanonicalSourceMaterial"
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial
open Complex MeasureTheory Set Filter BurnolPhysicalState
open OriginalKDirectRCofinalMaterial OriginalKFullAdjointSource SourceOperationScalarInventoryLift
open OriginalKCrossParameterRAdjointSource OriginalKDirectRCofinalOutsideVolterraSource OriginalPaPhysicalGreen
open scoped InnerProductSpace Topology
local notation "q" => (1/4:ℝ)
namespace PA
export OriginalKCombCofinalPaAction (E Q invisible)
end PA
local instance canonicalMaterialGroups (grade:Nat) (target:Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
local instance canonicalMaterialComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

/-- Both recursions use the actual inward R operation, with no future read witness as input. -/
def rawIterate (c:BurnolCompletedMellinCoordinate) (seed:ℝ → ℂ) : Nat → ℝ → ℂ
 | 0 => seed
 | j+1 => OriginalKCenteredMobiusRSource.sourceRRaw c (rawIterate c seed j)

def actualIterate (c:BurnolCompletedMellinCoordinate) (seed:BurnolL2) : Nat → BurnolL2
 | 0 => seed
 | j+1 => burnolDirectRightResolvent ((c).value/2) (actualIterate c seed j)

theorem actual_iterate_power (c:BurnolCompletedMellinCoordinate) (seed:BurnolL2) (j:Nat) :
 actualIterate c seed j=((burnolDirectRightResolventCLM c)^j) seed := by
 induction j with
 | zero => rfl
 | succ j previous =>
  rw [actualIterate,previous,pow_succ',mul_apply_eq_comp]
  rfl

theorem raw_iterate_gap (c:BurnolCompletedMellinCoordinate) (seed:ℝ → ℂ)
 (gap:∀{x:ℝ},|x|≤q → seed x=seed 0) (j:Nat) :
 ∀{x:ℝ},|x|≤q → rawIterate c seed j x=rawIterate c seed j 0 := by
 induction j with
 | zero => exact gap
 | succ j previous =>
  intro x inside
  rw [rawIterate,OriginalKCenteredMobiusRSource.sourceRRaw_gap c _ previous inside,
   OriginalKCenteredMobiusRSource.sourceRRaw_zero]

theorem raw_iterate_mean_update (c:BurnolCompletedMellinCoordinate) (seed:ℝ → ℂ) (j:Nat) :
 rawIterate c seed (j+1) 0= -2*rawIterate c seed j 0/(c).value :=
 OriginalKCenteredMobiusRSource.sourceRRaw_zero c _

private theorem actual_R_reflect (c:BurnolCompletedMellinCoordinate) (value:BurnolL2) :
 reflectL2 (burnolDirectRightResolvent ((c).value/2) value)=
   burnolDirectRightResolvent ((c).value/2) (reflectL2 value) := by
 apply fourierL2.injective
 rw [fourierL2_reflectL2_commute,←source_fourier_input]
 change reflectL2 (sourceVolterraResolvent c (fourierL2 value))=_
 rw [sourceVolterraResolvent_reflect,←fourierL2_reflectL2_commute]
 exact source_fourier_input c (reflectL2 value)

theorem actual_iterate_even (c:BurnolCompletedMellinCoordinate) (seed:BurnolL2)
 (even:reflectL2 seed=seed) (j:Nat) : reflectL2 (actualIterate c seed j)=actualIterate c seed j := by
 induction j with
 | zero => exact even
 | succ j previous => rw [actualIterate,actual_R_reflect,previous]

/-- Reflection extends the generated positive kernel read on the same full even actual value. -/
theorem actual_R_even_read (c:BurnolCompletedMellinCoordinate) (value:BurnolL2) (raw:ℝ → ℂ)
 (read:(value:ℝ → ℂ)=ᵐ[volume]raw) (gap:∀{x:ℝ},|x|≤q → raw x=raw 0)
 (even:reflectL2 value=value) :
 (burnolDirectRightResolvent ((c).value/2) value:ℝ → ℂ)=ᵐ[volume]
   OriginalKCenteredMobiusRSource.sourceRRaw c raw := by
 let acted:=burnolDirectRightResolvent ((c).value/2) value
 have positive:=OriginalKCenteredMobiusRSource.actual_R_positive_read c value raw read gap
 have actedEven:reflectL2 acted=acted := (actual_R_reflect c value).trans (congrArg _ even)
 have nonzero:∀ᵐ x:ℝ ∂volume,x≠0:=ae_iff.mpr (by simp)
 filter_upwards [positive,negMeasurePreserving.quasiMeasurePreserving.ae positive,
  Lp.coeFn_compMeasurePreserving acted negMeasurePreserving,nonzero] with x first second reflected nz
 have reflectedRead:acted x=acted (-x) := by
  change reflectL2 acted x=acted (-x) at reflected
  rw [actedEven] at reflected
  exact reflected
 by_cases pos:0<x
 · exact first pos
 · have negpos:0< -x:=by
    have negative:x<0:=lt_of_le_of_ne (le_of_not_gt pos) nz
    linarith
   calc
    acted x=acted (-x):=reflectedRead
    _=OriginalKCenteredMobiusRSource.sourceRRaw c raw (-x):=second negpos
    _=OriginalKCenteredMobiusRSource.sourceRRaw c raw x:=by
      simp only [OriginalKCenteredMobiusRSource.sourceRRaw,abs_neg]

theorem iterate_raw_read (c:BurnolCompletedMellinCoordinate) (value:BurnolL2) (raw:ℝ → ℂ)
 (read:(value:ℝ → ℂ)=ᵐ[volume]raw) (gap:∀{x:ℝ},|x|≤q → raw x=raw 0)
 (even:reflectL2 value=value) (j:Nat) :
 (actualIterate c value j:ℝ → ℂ)=ᵐ[volume]rawIterate c raw j := by
 induction j with
 | zero => exact read
 | succ j previous =>
  exact actual_R_even_read c (actualIterate c value j) (rawIterate c raw j) previous
   (raw_iterate_gap c raw gap j) (actual_iterate_even c value even j)

theorem iterate_raw_native (c:BurnolCompletedMellinCoordinate) (value:BurnolL2) (raw:ℝ → ℂ)
 (read:(value:ℝ → ℂ)=ᵐ[volume]raw) (gap:∀{x:ℝ},|x|≤q → raw x=raw 0)
 (even:reflectL2 value=value) (j:Nat) : MemLp (rawIterate c raw j) 2 volume :=
 (memLp_congr_ae (iterate_raw_read c value raw read gap even j)).mp (Lp.memLp _)

/-- Native membership and literal gap are generated internally before the inverse acts. -/
theorem iterate_inverse_R_action (c:BurnolCompletedMellinCoordinate) (value:BurnolL2) (raw:ℝ → ℂ)
 (read:(value:ℝ → ℂ)=ᵐ[volume]raw) (gap:∀{x:ℝ},|x|≤q → raw x=raw 0)
 (even:reflectL2 value=value) (j:Nat) (t:ℝ) (positive:0<t) :
 burnolCenteredMobiusInverse (rawIterate c raw (j+1)) t=
  -2*(t:ℂ)^(-(c).value)*(∫ v:ℝ in 0..t,(v:ℂ)^((c).value-1)*burnolCenteredMobiusInverse (rawIterate c raw j) v) :=
 OriginalKCenteredMobiusRSource.source_inverse_R_action c (rawIterate c raw j)
  (iterate_raw_native c value raw read gap even j) (raw_iterate_gap c raw gap j) t positive

private theorem quarter_read_of_source (value:BurnolL2) (raw:ℝ → ℂ)
 (read:(value:ℝ → ℂ)=ᵐ[volume]raw) (gap:∀{x:ℝ},|x|≤q → raw x=raw 0) :
 burnolQuarterRestriction value=raw 0 • intervalConstant q := by
 apply Lp.ext
 filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) value,
  ae_restrict_of_ae read,ae_restrict_mem (measurableSet_symmetricInterval q),
  Lp.coeFn_smul (raw 0) (intervalConstant q),intervalConstant_coeFn q]
  with x restriction source inside scalar constant
 have small:|x|≤q:=abs_le.mpr inside
 change burnolQuarterRestriction value x=value x at restriction
 simp only [restriction,source,gap small,scalar,constant,Pi.smul_apply,smul_eq_mul,mul_one]

/-- The source starts with the actual counted harmonic band, including its logarithmic mean. -/
def seedRaw (x:ℝ) : ℂ := 2*burnolHarmonicStepWaveRaw 1 (3/2) x

private theorem seed_raw_read :
 ((burnolPaCombApproximation 0:BurnolL2):ℝ → ℂ)=ᵐ[volume]seedRaw := by
 convert burnolPaCombApproximation_coeFn 0 using 1
 norm_num [seedRaw,burnolPaCombSourceWidth]
 rfl

private theorem seed_raw_gap : ∀{x:ℝ},|x|≤q → seedRaw x=seedRaw 0 := by
 intro x small
 have first:⌊|x|⌋₊=0:=Nat.floor_eq_zero.mpr (by linarith)
 have second:⌊|x|/(3/2:ℝ)⌋₊=0:=Nat.floor_eq_zero.mpr (by rw [div_lt_one (by norm_num)];linarith)
 simp only [seedRaw,burnolHarmonicStepWaveRaw,burnolHarmonicStepChannels,div_one,first,second,
  Finset.Ioc_self,Finset.sum_empty,zero_sub,abs_zero,zero_div,Nat.floor_zero]

private theorem seed_raw_mean : seedRaw 0= -2*(Real.log (3/2:ℝ):ℂ) := by
 simp only [seedRaw,burnolHarmonicStepWaveRaw,burnolHarmonicStepChannels,abs_zero,zero_div,
  Nat.floor_zero,Finset.Ioc_self,Finset.sum_empty,zero_sub,div_one]
 ring

private theorem seed_raw_mean_ne : seedRaw 0≠0 := by
 rw [seed_raw_mean]
 exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num))))

theorem raw_iterate_mean_ne (c:BurnolCompletedMellinCoordinate) (seed:ℝ → ℂ)
 (initial:seed 0≠0) (j:Nat) : rawIterate c seed j 0≠0 := by
 have parameter:(c).value≠0:=by
  intro zero
  have right:=c.rightHalf
  rw [zero] at right
  norm_num at right
 induction j with
 | zero => exact initial
 | succ j previous =>
  rw [raw_iterate_mean_update]
  exact div_ne_zero (mul_ne_zero (by norm_num) previous) parameter

private theorem seed_even : reflectL2 (burnolPaCombApproximation 0:BurnolL2)=(burnolPaCombApproximation 0:BurnolL2) :=
 mem_evenL2ClosedFace_iff.mp (burnolPaCombApproximation 0).property.2

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate

def sourceIndex (ordinal:Nat) : Nat := m+(ordinal+2)
def canonicalRaw (ordinal:Nat) : ℝ → ℂ := rawIterate c seedRaw (sourceIndex observation ordinal)

theorem actual_raw_field (depth ordinal:Nat) :
 D.raw observation nontrivial half depth ordinal=
 actualIterate c (burnolPaCombApproximation 0:BurnolL2) (sourceIndex observation ordinal) := by
 rw [OriginalKCombFirstFullSourceDynamics.raw_xi_source,actual_iterate_power]
 change (((P.R observation nontrivial half).toLinearMap)^sourceIndex observation ordinal)
  (burnolPaCombApproximation 0:BurnolL2)=_
 rw [←ContinuousLinearMap.toLinearMap_pow]
 rfl

theorem actual_raw_source (depth ordinal:Nat) :
 (D.raw observation nontrivial half depth ordinal:ℝ → ℂ)=ᵐ[volume]canonicalRaw observation half ordinal := by
 rw [actual_raw_field]
 exact iterate_raw_read c (burnolPaCombApproximation 0:BurnolL2) seedRaw seed_raw_read seed_raw_gap seed_even _

theorem canonical_source_gap (ordinal:Nat) :
 ∀{x:ℝ},|x|≤q → canonicalRaw observation half ordinal x=canonicalRaw observation half ordinal 0 :=
 raw_iterate_gap c seedRaw seed_raw_gap _

theorem canonical_source_native (ordinal:Nat) : MemLp (canonicalRaw observation half ordinal) 2 volume :=
 iterate_raw_native c (burnolPaCombApproximation 0:BurnolL2) seedRaw seed_raw_read seed_raw_gap seed_even _

theorem canonical_source_mean_ne (ordinal:Nat) : canonicalRaw observation half ordinal 0≠0 :=
 raw_iterate_mean_ne c seedRaw seed_raw_mean_ne _

theorem actual_raw_quarter (depth ordinal:Nat) :
 burnolQuarterRestriction (D.raw observation nontrivial half depth ordinal)=
   canonicalRaw observation half ordinal 0 • intervalConstant q :=
 quarter_read_of_source _ _ (actual_raw_source observation nontrivial half depth ordinal) (canonical_source_gap observation half ordinal)

variable (depth ordinal:Nat)
local notation "lastOrdinal" => ordinal+(m-1)
local notation "inputRaw" => OriginalKDirectRCofinalCalculatedSource.calculatedInputRaw observation nontrivial half depth lastOrdinal
local notation "targetRaw" => OriginalKDirectRCofinalCalculatedSource.calculatedTargetRaw observation nontrivial half depth lastOrdinal
local notation "bornRaw" => OriginalKDirectRCofinalPaUpdate.DirectRPaUpdateControls.bornRead observation nontrivial half depth lastOrdinal
local notation "factory" => D.factory observation nontrivial half
local notation "initial" => D.initial observation nontrivial half depth
local notation "cfg" => D.firstCfg observation nontrivial half depth
local notation "Z" => OriginalKLossFreeAdjointMaterial.installedKernelCombo observation nontrivial half
local notation "H" => UnitPowerSource.fulladjointPowerZ observation half
local notation "endSource" => canonicalRaw observation half (ordinal+m)
local notation "inputSource" => canonicalRaw observation half lastOrdinal

structure MaterialAt : Prop where
 inherited : UnitPowerJordanMaterialConsumer.MaterialAt observation nontrivial half depth ordinal
 unitSourceRead : (burnolUnitTailResponse c 4:ℝ → ℂ)=ᵐ[volume]OriginalKCenteredMobiusRSource.unitRaw c
 unitSourceMean : OriginalKCenteredMobiusRSource.unitRaw c 0=(4:ℂ)^(-(c).value)/(c).value
 unitSourceInverse : ∀t:ℝ,burnolCenteredMobiusInverse (OriginalKCenteredMobiusRSource.unitRaw c) t=
   burnolRadiusUnitTailRaw (c).value 4 t
 sourceInput : inputRaw=D.raw observation nontrivial half depth lastOrdinal
 rawAE : (D.raw observation nontrivial half depth ordinal:ℝ → ℂ)=ᵐ[volume]canonicalRaw observation half ordinal
 inputAE : (inputRaw:ℝ → ℂ)=ᵐ[volume]inputSource
 normalAE : (targetRaw:ℝ → ℂ)=ᵐ[volume]endSource
 bornAE : (bornRaw:ℝ → ℂ)=ᵐ[volume]endSource
 inputGap : burnolQuarterRestriction inputRaw=inputSource 0 • intervalConstant q
 bornGap : burnolQuarterRestriction bornRaw=endSource 0 • intervalConstant q
 inputNative : MemLp inputSource 2 volume
 bornNative : MemLp endSource 2 volume
 sourceWordIndex : sourceIndex observation lastOrdinal+1=sourceIndex observation (ordinal+m)
 bornAction : bornRaw=P.R observation nontrivial half inputRaw
 sourceMean : endSource 0= -2*inputSource 0/(c).value
 sourceMeanNonzero : endSource 0≠0
 sourceInverse : ∀t:ℝ,0<t → burnolCenteredMobiusInverse endSource t=
   -2*(t:ℂ)^(-(c).value)*(∫ v:ℝ in 0..t,(v:ℂ)^((c).value-1)*burnolCenteredMobiusInverse inputSource v)

theorem actual_cofinal_canonical_on_original_whole_next : MaterialAt observation nontrivial half depth ordinal := by
 have previous:=UnitPowerJordanMaterialConsumer.actual_unit_jordan_on_original_whole_next observation nontrivial half depth ordinal
 have sourceInput:=OriginalKDirectRCofinalCalculatedSource.calculated_input_raw observation nontrivial half depth lastOrdinal
 have word:sourceIndex observation lastOrdinal+1=sourceIndex observation (ordinal+m):=by
  have positive:=generatedRiemannXiZeroOrder_pos observation nontrivial
  unfold sourceIndex
  omega
 have inputAE:(inputRaw:ℝ → ℂ)=ᵐ[volume]inputSource:=by
  rw [sourceInput]
  exact actual_raw_source observation nontrivial half depth lastOrdinal
 exact {
  inherited:=previous
  unitSourceRead:=OriginalKCenteredMobiusRSource.unitRaw_read c
  unitSourceMean:=OriginalKCenteredMobiusRSource.unitRaw_zero c
  unitSourceInverse:=OriginalKCenteredMobiusRSource.original_unit_inverse_source c
  sourceInput:=sourceInput
  rawAE:=actual_raw_source observation nontrivial half depth ordinal
  inputAE:=inputAE
  normalAE:=by rw [previous.inherited.normalGenerated];exact actual_raw_source observation nontrivial half depth (ordinal+m)
  bornAE:=by rw [previous.inherited.bornGenerated];exact actual_raw_source observation nontrivial half depth (ordinal+m)
  inputGap:=by rw [sourceInput];exact actual_raw_quarter observation nontrivial half depth lastOrdinal
  bornGap:=by rw [previous.inherited.bornGenerated];exact actual_raw_quarter observation nontrivial half depth (ordinal+m)
  inputNative:=canonical_source_native observation half lastOrdinal
  bornNative:=canonical_source_native observation half (ordinal+m)
  sourceWordIndex:=word
  bornAction:=previous.inherited.bornGenerated.trans (previous.inherited.normalGenerated.symm.trans previous.inherited.sourceAction)
  sourceMean:=by
   unfold canonicalRaw
   rw [←word]
   exact raw_iterate_mean_update c seedRaw _
  sourceMeanNonzero:=canonical_source_mean_ne observation half (ordinal+m)
  sourceInverse:=by
   intro t positive
   unfold canonicalRaw
   rw [←word]
   exact iterate_inverse_R_action c (burnolPaCombApproximation 0:BurnolL2) seedRaw
    seed_raw_read seed_raw_gap seed_even _ t positive }

/-- The independent reader couples the generated native source equation to every retained physical price and native next. -/
theorem actual_cofinal_canonical_born_consumer :
 (inputRaw=D.raw observation nontrivial half depth lastOrdinal) ∧
 ((inputRaw:ℝ → ℂ)=ᵐ[volume]inputSource) ∧
 (bornRaw=P.R observation nontrivial half inputRaw) ∧
 (sourceIndex observation lastOrdinal+1=sourceIndex observation (ordinal+m)) ∧
 ((burnolUnitTailResponse c 4:ℝ → ℂ)=ᵐ[volume]OriginalKCenteredMobiusRSource.unitRaw c) ∧
 (OriginalKCenteredMobiusRSource.unitRaw c 0=(4:ℂ)^(-(c).value)/(c).value) ∧
 (∀t:ℝ,burnolCenteredMobiusInverse (OriginalKCenteredMobiusRSource.unitRaw c) t=burnolRadiusUnitTailRaw (c).value 4 t) ∧
 ((bornRaw:ℝ → ℂ)=ᵐ[volume]endSource) ∧
 (burnolQuarterRestriction bornRaw=endSource 0 • intervalConstant q) ∧
 (endSource 0= -2*inputSource 0/(c).value) ∧
 (endSource 0≠0) ∧
 (∀t:ℝ,0<t → burnolCenteredMobiusInverse endSource t=
   -2*(t:ℂ)^(-(c).value)*(∫ v:ℝ in 0..t,(v:ℂ)^((c).value-1)*burnolCenteredMobiusInverse inputSource v)) ∧
 ((PA.Q H:BurnolL2)=UnitPowerJordanSource.sourceQ observation half) ∧
 (UnitPowerJordanSource.sourceQCarrier observation half∈burnolCompactCoPoissonClosedRange.toSubmoduleᗮ) ∧
 (H=(UnitPowerSource.paPowerField observation half:BurnolL2)+UnitPowerJordanSource.sourceQ observation half+
   UnitPowerJordanSource.sourceOutside c m) ∧
 (burnolAmbientEvenMeanZeroCorrection H=UnitPowerJordanSource.sourceOutside c m) ∧
 (inner ℂ Z bornRaw=UnitPowerMaterialConsumer.actualPaFee observation half (D.raw observation nontrivial half depth ordinal)+
   UnitPowerJordanMaterialConsumer.actualQPrice observation half (D.raw observation nontrivial half depth ordinal)+
   UnitPowerJordanMaterialConsumer.actualOutsidePrice observation half (D.raw observation nontrivial half depth ordinal)) ∧
 (lastOrdinal+1=ordinal+m) ∧
 type_of% (RC.original_whole factory initial cfg rfl (lastOrdinal+1)) ∧
 type_of% (RC.actual_generated_current factory initial cfg rfl (lastOrdinal+1)) := by
 have actual:=actual_cofinal_canonical_on_original_whole_next observation nontrivial half depth ordinal
 exact ⟨actual.sourceInput,actual.inputAE,actual.bornAction,actual.sourceWordIndex,actual.unitSourceRead,actual.unitSourceMean,actual.unitSourceInverse,actual.bornAE,actual.bornGap,actual.sourceMean,actual.sourceMeanNonzero,actual.sourceInverse,actual.inherited.actualQSource,
  actual.inherited.qMember,actual.inherited.sourceInventory,actual.inherited.completeBSource,actual.inherited.bornPrice,
  actual.inherited.inherited.generatedIndex,actual.inherited.inherited.whole,actual.inherited.inherited.next⟩

/-- A zero actual centred prefix never erases the independently generated full mean or physical price. -/
theorem actual_zero_prefix_override (t:ℝ) (positive:0<t)
 (zero:(∫ v:ℝ in 0..t,(v:ℂ)^((c).value-1)*burnolCenteredMobiusInverse inputSource v)=0) :
 burnolCenteredMobiusInverse endSource t=0 ∧ endSource 0≠0 ∧
 inner ℂ Z bornRaw=UnitPowerJordanMaterialConsumer.completePrice observation half
   (D.raw observation nontrivial half depth ordinal) := by
 have actual:=actual_cofinal_canonical_on_original_whole_next observation nontrivial half depth ordinal
 exact ⟨by rw [actual.sourceInverse t positive,zero,mul_zero],actual.sourceMeanNonzero,actual.inherited.bornPrice⟩

/-- The full generated mean cannot be dropped from the actual born quarter carrier. -/
theorem actual_born_quarter_cannot_be_zero : burnolQuarterRestriction bornRaw≠0 := by
 have actual:=actual_cofinal_canonical_on_original_whole_next observation nontrivial half depth ordinal
 rw [actual.bornGap]
 exact smul_ne_zero actual.sourceMeanNonzero (intervalConstant_ne_zero (by norm_num))

end OriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
