import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerJordanSource
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerMaterialConsumer

-- The native dependent ledger projections are excluded only from suggestion indexing.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "UnitPowerJordanMaterialConsumer"
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.UnitPowerJordanMaterialConsumer
open Complex MeasureTheory Set BurnolPhysicalState
open OriginalKDirectRCofinalMaterial OriginalKFullAdjointSource SourceOperationScalarInventoryLift
open OriginalKCrossParameterRAdjointSource OriginalKDirectRCofinalOutsideVolterraSource
open scoped InnerProductSpace
namespace PA
export OriginalKCombCofinalPaAction (E Q invisible)
end PA
local instance jordanMaterialGroups (grade:Nat) (target:Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
local instance jordanMaterialComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "H" => UnitPowerSource.fulladjointPowerZ observation half
local notation "Z" => OriginalKLossFreeAdjointMaterial.installedKernelCombo observation nontrivial half
local notation "Qsource" => UnitPowerJordanSource.sourceQ observation half
local notation "Osource" => UnitPowerJordanSource.sourceOutside c m

def actualQPrice (value:BurnolL2) : ℂ := inner ℂ Qsource value

def actualOutsidePrice (value:BurnolL2) : ℂ :=
 ∑ k∈Finset.range m,star (UnitPowerJordanSource.sourceCoefficient c m k)*
   inner ℂ (UnitPowerJordanSource.logOutsideColumn c k) value

def completePrice (value:BurnolL2) : ℂ :=
 UnitPowerMaterialConsumer.actualPaFee observation half value+
   actualQPrice observation half value+actualOutsidePrice observation half value

include nontrivial in
/-- Both complete old prices are evaluated by the generated Q vector and every finite B column. -/
theorem source_prices_generated (value:BurnolL2) :
 UnitPowerMaterialConsumer.actualQPrice observation half value=actualQPrice observation half value ∧
 UnitPowerMaterialConsumer.actualOutsidePrice observation half value=actualOutsidePrice observation half value :=
 ⟨UnitPowerJordanSource.actual_Q_price observation nontrivial half value,
  UnitPowerJordanSource.actual_outside_price observation half value⟩

include nontrivial in
theorem complete_price_generated (value:BurnolL2) :
 UnitPowerMaterialConsumer.completePrice observation half value=completePrice observation half value := by
 unfold UnitPowerMaterialConsumer.completePrice completePrice
 rw [(source_prices_generated observation nontrivial half value).1,
   (source_prices_generated observation nontrivial half value).2]

variable (depth ordinal:Nat)
local notation "raw" => D.raw observation nontrivial half depth ordinal
local notation "rawEnd" => D.raw observation nontrivial half depth (ordinal+m)
local notation "lastOrdinal" => ordinal+(m-1)
local notation "targetRaw" => OriginalKDirectRCofinalCalculatedSource.calculatedTargetRaw observation nontrivial half depth lastOrdinal
local notation "bornRaw" => OriginalKDirectRCofinalPaUpdate.DirectRPaUpdateControls.bornRead observation nontrivial half depth lastOrdinal
local notation "factory" => D.factory observation nontrivial half
local notation "initial" => D.initial observation nontrivial half depth
local notation "cfg" => D.firstCfg observation nontrivial half depth

/-- The same original material occurrence consumes the computed finite B source and its complete Q. -/
structure MaterialAt : Prop where
 inherited : UnitPowerMaterialConsumer.MaterialAt observation nontrivial half depth ordinal
 sourceWord : UnitPowerJordanSource.sourceField c m=H
 positionSource : burnolQuarterRestriction H=
   UnitPowerJordanSource.sourceConstant c m • intervalConstant (1/4:ℝ)+
     UnitPowerJordanSource.finiteQuarterSource c m
 fourierSource : burnolQuarterRestriction (fourierL2.symm H)=
   UnitPowerJordanSource.sourceFourierConstant c m • intervalConstant (1/4:ℝ)
 positionDrive : quarterCotest H=UnitPowerJordanSource.finiteBDrive c m
 firstBSource : burnolAmbientMeanZeroFirstCorrection H=
   ∑ k∈Finset.range m,UnitPowerJordanSource.sourceCoefficient c m k • UnitPowerJordanSource.logBFirst c k
 secondBSource : burnolAmbientMeanZeroSecondCorrection H=
   ∑ k∈Finset.range m,UnitPowerJordanSource.sourceCoefficient c m k • UnitPowerJordanSource.logBSecond c k
 completeBSource : burnolAmbientEvenMeanZeroCorrection H=Osource
 finiteOutsideSource : H-(burnolEvenAmbientProjection H:BurnolL2)=Osource
 outsideMember : Osource∈(evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmoduleᗮ
 actualQSource : (PA.Q H:BurnolL2)=Qsource
 qMember : UnitPowerJordanSource.sourceQCarrier observation half∈burnolCompactCoPoissonClosedRange.toSubmoduleᗮ
 sourceInventory : H=(UnitPowerSource.paPowerField observation half:BurnolL2)+Qsource+Osource
 qPrice : UnitPowerMaterialConsumer.actualQPrice observation half raw=actualQPrice observation half raw
 outsidePrice : UnitPowerMaterialConsumer.actualOutsidePrice observation half raw=actualOutsidePrice observation half raw
 normalPrice : inner ℂ Z targetRaw=completePrice observation half raw
 rawPrice : inner ℂ Z rawEnd=completePrice observation half raw
 bornPrice : inner ℂ Z bornRaw=completePrice observation half raw
 invisibleInventory : UnitPowerMaterialConsumer.actualInvisiblePrice observation half raw=
   actualQPrice observation half raw+actualOutsidePrice observation half raw

/-- No callback is replayed: its actual native whole/current and exact endIndex are inherited together. -/
theorem actual_unit_jordan_on_original_whole_next : MaterialAt observation nontrivial half depth ordinal := by
 have previous := UnitPowerMaterialConsumer.actual_unit_power_on_original_whole_next observation nontrivial half depth ordinal
 have word := UnitPowerJordanSource.actual_sourceField observation half
 have prices := source_prices_generated observation nontrivial half raw
 have complete := complete_price_generated observation nontrivial half raw
 exact {
  inherited := previous
  sourceWord := word
  positionSource := by rw [←word]; exact UnitPowerJordanSource.source_quarter_finite c m
  fourierSource := by rw [←word]; exact UnitPowerJordanSource.source_inverseFourier_quarter c m
  positionDrive := by rw [←word]; exact UnitPowerJordanSource.source_centered_quarter c m
  firstBSource := by rw [←word]; exact UnitPowerJordanSource.source_B_first c m
  secondBSource := by rw [←word]; exact UnitPowerJordanSource.source_B_second c m
  completeBSource := by rw [←word]; exact UnitPowerJordanSource.source_complete_B_correction c m
  finiteOutsideSource := by rw [←word]; exact UnitPowerJordanSource.source_outside_actual c m
  outsideMember := UnitPowerJordanSource.source_outside_orthogonal c m
  actualQSource := UnitPowerJordanSource.sourceQ_actual observation nontrivial half
  qMember := UnitPowerJordanSource.sourceQ_mem observation nontrivial half
  sourceInventory := UnitPowerJordanSource.source_full_inventory observation half
  qPrice := prices.1
  outsidePrice := prices.2
  normalPrice := previous.normalPrice.trans complete
  rawPrice := previous.rawPrice.trans complete
  bornPrice := previous.bornPrice.trans complete
  invisibleInventory := by rw [previous.invisibleInventory,prices.1,prices.2] }

/-- The independent reader consumes actual B/Q membership, both raw mean equations and the same born whole-next. -/
theorem actual_unit_jordan_born_consumer :
 (PA.E H=UnitPowerSource.paPowerField observation half) ∧
 (∀ j:Nat,j<m → PA.E ((((P.R observation nontrivial half)^j).adjoint) Z)=0) ∧
 (UnitPowerSource.feedbackCoefficient observation half≠0) ∧
 (PA.E H≠0) ∧
 (burnolQuarterRestriction H=UnitPowerJordanSource.sourceConstant c m • intervalConstant (1/4:ℝ)+
   UnitPowerJordanSource.finiteQuarterSource c m) ∧
 (burnolQuarterRestriction (fourierL2.symm H)=UnitPowerJordanSource.sourceFourierConstant c m • intervalConstant (1/4:ℝ)) ∧
 (quarterCotest H=UnitPowerJordanSource.finiteBDrive c m) ∧
 (burnolAmbientEvenMeanZeroCorrection H=Osource) ∧
 (H-(burnolEvenAmbientProjection H:BurnolL2)=Osource) ∧
 (Osource∈(evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmoduleᗮ) ∧
 ((PA.Q H:BurnolL2)=Qsource) ∧
 (UnitPowerJordanSource.sourceQCarrier observation half∈burnolCompactCoPoissonClosedRange.toSubmoduleᗮ) ∧
 (H=(UnitPowerSource.paPowerField observation half:BurnolL2)+Qsource+Osource) ∧
 (UnitPowerMaterialConsumer.actualQPrice observation half raw=actualQPrice observation half raw) ∧
 (UnitPowerMaterialConsumer.actualOutsidePrice observation half raw=actualOutsidePrice observation half raw) ∧
 (bornRaw=rawEnd) ∧
 (inner ℂ Z bornRaw=UnitPowerMaterialConsumer.actualPaFee observation half raw+
   actualQPrice observation half raw+actualOutsidePrice observation half raw) ∧
 (UnitPowerMaterialConsumer.actualInvisiblePrice observation half raw=
   actualQPrice observation half raw+actualOutsidePrice observation half raw) ∧
 (lastOrdinal+1=ordinal+m) ∧
 type_of% (RC.original_whole factory initial cfg rfl (lastOrdinal+1)) ∧
 type_of% (RC.actual_generated_current factory initial cfg rfl (lastOrdinal+1)) := by
 have actual := actual_unit_jordan_on_original_whole_next observation nontrivial half depth ordinal
 exact ⟨actual.inherited.sourceField,actual.inherited.lowerSource,actual.inherited.feedbackSource,
  actual.inherited.sourceFieldNonzero,actual.positionSource,actual.fourierSource,actual.positionDrive,
  actual.completeBSource,actual.finiteOutsideSource,actual.outsideMember,actual.actualQSource,actual.qMember,actual.sourceInventory,actual.qPrice,
  actual.outsidePrice,actual.inherited.bornGenerated,actual.bornPrice,actual.invisibleInventory,
  actual.inherited.generatedIndex,actual.inherited.whole,actual.inherited.next⟩

/-- The first exact order retains the complete accepted simple-order price. -/
theorem actual_simple_order_price (simple:m=1) :
 Osource=0 ∧ actualOutsidePrice observation half raw=0 ∧
 completePrice observation half raw=UnitJetMaterialConsumer.nextQPrice observation half raw ∧
 inner ℂ Z bornRaw=UnitJetMaterialConsumer.nextQPrice observation half raw := by
 have outsideSource : Osource=0 := by rw [simple]; exact UnitPowerJordanSource.source_outside_one c
 have outsidePrice : actualOutsidePrice observation half raw=0 := by
  unfold actualOutsidePrice
  rw [simple]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,UnitPowerJordanSource.sourceCoefficient,
   UnitPowerJordanSource.source_initial_amplitude_zero,star_zero,zero_mul,zero_add]
 have old := UnitPowerMaterialConsumer.actual_simple_order_feedback observation nontrivial half depth ordinal simple
 have complete : completePrice observation half raw=UnitJetMaterialConsumer.nextQPrice observation half raw :=
  (complete_price_generated observation nontrivial half raw).symm.trans old.2.2.1
 exact ⟨outsideSource,outsidePrice,complete,
  (actual_unit_jordan_on_original_whole_next observation nontrivial half depth ordinal).bornPrice.trans complete⟩

/-- An explicit zero finite source fee keeps the full generated Q and Pa fees. -/
theorem actual_zero_outside_override (zero:actualOutsidePrice observation half raw=0) :
 inner ℂ Z bornRaw=UnitPowerMaterialConsumer.actualPaFee observation half raw+actualQPrice observation half raw := by
 have actual := (actual_unit_jordan_on_original_whole_next observation nontrivial half depth ordinal).bornPrice
 simpa only [completePrice,zero,add_zero] using actual

theorem actual_zero_Q_override (zero:actualQPrice observation half raw=0) :
 inner ℂ Z bornRaw=UnitPowerMaterialConsumer.actualPaFee observation half raw+actualOutsidePrice observation half raw := by
 have actual := (actual_unit_jordan_on_original_whole_next observation nontrivial half depth ordinal).bornPrice
 simpa only [completePrice,zero,add_zero] using actual

theorem actual_zero_coefficient_override
 (zero:burnolPaResolventSourceCoefficient c (PA.E raw)=0) :
 inner ℂ Z bornRaw=actualQPrice observation half raw+actualOutsidePrice observation half raw := by
 have actual := (actual_unit_jordan_on_original_whole_next observation nontrivial half depth ordinal).bornPrice
 simpa only [completePrice,UnitPowerMaterialConsumer.actualPaFee,zero,mul_zero,zero_add] using actual

/-- The complete finite source fee is retained whenever its actual value is nonzero. -/
theorem actual_nonzero_outside_price_cannot_be_dropped (nonzero:actualOutsidePrice observation half raw≠0) :
 inner ℂ Z bornRaw≠UnitPowerMaterialConsumer.actualPaFee observation half raw+actualQPrice observation half raw := by
 intro erased
 have actual := (actual_unit_jordan_on_original_whole_next observation nontrivial half depth ordinal).bornPrice
 change _=UnitPowerMaterialConsumer.actualPaFee observation half raw+actualQPrice observation half raw+
   actualOutsidePrice observation half raw at actual
 rw [erased] at actual
 exact nonzero (by linear_combination -actual)

theorem actual_nonzero_Q_price_cannot_be_dropped (nonzero:actualQPrice observation half raw≠0) :
 inner ℂ Z bornRaw≠UnitPowerMaterialConsumer.actualPaFee observation half raw+actualOutsidePrice observation half raw := by
 intro erased
 have actual := (actual_unit_jordan_on_original_whole_next observation nontrivial half depth ordinal).bornPrice
 change _=UnitPowerMaterialConsumer.actualPaFee observation half raw+actualQPrice observation half raw+
   actualOutsidePrice observation half raw at actual
 rw [erased] at actual
 exact nonzero (by linear_combination -actual)

theorem actual_nonzero_Pa_fee_cannot_be_dropped (nonzero:UnitPowerMaterialConsumer.actualPaFee observation half raw≠0) :
 inner ℂ Z bornRaw≠actualQPrice observation half raw+actualOutsidePrice observation half raw := by
 intro erased
 have actual := (actual_unit_jordan_on_original_whole_next observation nontrivial half depth ordinal).bornPrice
 change _=UnitPowerMaterialConsumer.actualPaFee observation half raw+actualQPrice observation half raw+
   actualOutsidePrice observation half raw at actual
 rw [erased] at actual
 exact nonzero (by linear_combination -actual)

end OriginalKFiniteOrderRelease.UnitPowerJordanMaterialConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
