import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalOutsideVolterraSource.HProjectionSource
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalReentrySourceAction.Physical

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCrossParameterRAdjointSource.PhysicalDefectSource
open Complex MeasureTheory Set BurnolPhysicalState
open OriginalKSourceResolventReconstruction OriginalKFullAdjointSource OriginalPaPhysicalGreen
open OriginalKDirectRCofinalOutsideVolterraSource OriginalKForcingGapAction
open OriginalRieszFinitePairing.CoPoisson.Ward
open scoped InnerProductSpace
local notation "q" => (1/4:ℝ)
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "outside" => OriginalKCombPhysicalAction.physicalRemainder
namespace PA
export OriginalKCombCofinalPaAction (E Q invisible)
end PA
local instance physicalDefectComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local instance physicalDefectQuarterComplete : CompleteSpace BurnolQuarterMeanZeroCarrier := by
  apply IsComplete.completeSpace_coe
  exact burnolQuarterMeanZeroClosedFace.isClosed.isComplete

/-- The input mean and complete tail are the already generated conjugate Mellin functional. -/
def physicalAmplitude (c : BurnolCompletedMellinCoordinate) : BurnolPaAmbientCarrier →L[ℂ] ℂ :=
  (-2:ℂ) • burnolCompletedMellinEvaluator (barC c)

/-- The full physical response column is generated from the original conjugate-parameter source. -/
def outsidePhysicalSource (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  (-2:ℂ) • generatedK (barC c)

-- Reuse the exact independently paid generic term, without changing its owning source.
elab "paidPhysicalVolterraQuarter" : term => do
  let head := ("_private.H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalOutsideVolterraSource.HQuarterSource".splitOn ".").foldl Lean.Name.str Lean.Name.anonymous
  let full := ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalOutsideVolterraSource.conjugate_volterra_quarter".splitOn ".").foldl Lean.Name.str (Lean.Name.num head 0)
  return Lean.mkConst full

private theorem rightQuarter (c : BurnolCompletedMellinCoordinate) : 1/4<(c.value/2).re := by
  rw [Complex.div_re];norm_num;linarith [c.rightHalf]
private theorem starRightQuarter (c : BurnolCompletedMellinCoordinate) : 1/4<(star c.value/2).re := by
  rw [Complex.div_re];norm_num;linarith [c.rightHalf]
private theorem physical_even (v : BurnolPaAmbientCarrier) : reflectL2 (v:BurnolL2)=v :=
  mem_evenL2ClosedFace_iff.mp v.property.2
private theorem physical_gap (v : BurnolPaAmbientCarrier) :
    burnolQuarterRestriction (v:BurnolL2)=burnolConstantGapCoefficient q v • intervalConstant q := by
  exact (burnolGenericPhysicalValue_gap v).symm

theorem physicalAmplitude_native (c : BurnolCompletedMellinCoordinate) (v : BurnolPaAmbientCarrier) :
    physicalAmplitude c v = -2*(burnolRadiusMellinTailEvaluator q (by norm_num) (star c.value)
      (by simpa only [Complex.star_def,Complex.conj_re] using c.rightHalf) (v:BurnolL2)+
        burnolConstantGapCoefficient q v*(q:ℂ)^(1-star c.value)/(1-star c.value)) := by
  change (-2:ℂ)*burnolCompletedMellinEvaluator (barC c) v=_
  rw [burnolCompletedMellinEvaluator_apply]
  change (-2:ℂ)*((q:ℂ)^(1-star c.value)/(1-star c.value)*
    burnolConstantGapCoefficient q v+_)=_
  unfold burnolMellinTailEvaluator
  change (-2:ℂ)*((q:ℂ)^(1-star c.value)/(1-star c.value)*
    burnolConstantGapCoefficient q v+burnolRadiusMellinTailEvaluator q (by norm_num) (star c.value)
      (by simpa only [Complex.star_def,Complex.conj_re] using c.rightHalf) (v:BurnolL2))=_
  ring

theorem outsidePhysicalSource_read (c : BurnolCompletedMellinCoordinate) (v : BurnolPaAmbientCarrier) :
    inner ℂ (outsidePhysicalSource c) (v:BurnolL2)=physicalAmplitude c v := by
  rw [outsidePhysicalSource,generatedK_eq_original,inner_smul_left]
  change star (-2:ℂ)*inner ℂ (burnolCompletedMellinRieszVector (barC c)) v=_
  rw [burnolCompletedMellinRieszVector_readback]
  simp only [star_neg,star_ofNat]
  rfl

theorem outsidePhysicalSource_mem (c : BurnolCompletedMellinCoordinate) :
    outsidePhysicalSource c∈evenBurnolClosedFace q := by
  rw [outsidePhysicalSource,generatedK_eq_original]
  exact (evenBurnolClosedFace q).toSubmodule.smul_mem _ (burnolCompletedMellinRieszVector (barC c)).property

private theorem adjoint_volterra (c : BurnolCompletedMellinCoordinate) (v : BurnolL2) :
    sourceAdjoint c v=sourceVolterraResolvent (barC c) v :=
  FiniteMobiusResolventFlux.Rplus_tate (star c.value/2) (starRightQuarter c) v

private theorem adjoint_even (c : BurnolCompletedMellinCoordinate) (v : BurnolPaAmbientCarrier) :
    reflectL2 (sourceAdjoint c v)=sourceAdjoint c v := by
  rw [adjoint_volterra,sourceVolterraResolvent_reflect,physical_even]

theorem physical_adjoint_quarter_source (c : BurnolCompletedMellinCoordinate) (v : BurnolPaAmbientCarrier) :
    quarterCotest (sourceAdjoint c v)=physicalAmplitude c v • SingularCounting.centeredPower c := by
  have source := paidPhysicalVolterraQuarter c (v:BurnolL2) (burnolConstantGapCoefficient q v)
    (physical_gap v) (physical_even v)
  apply Subtype.ext
  change burnolQuarterMeanZeroProjection (burnolQuarterRestriction (sourceAdjoint c v))=_
  rw [adjoint_volterra,source,map_add,map_smul,map_smul]
  have constantZero : burnolQuarterMeanZeroProjection (intervalConstant q)=0 :=
    (burnolQuarterMeanZeroProjection_eq_zero_iff _).mpr (Submodule.mem_span_singleton_self _)
  rw [constantZero,smul_zero,zero_add,physicalAmplitude_native]
  rfl

private theorem inverseFourier_physical (v : BurnolPaAmbientCarrier) :
    fourierL2.symm (v:BurnolL2)=
      (evenFaceFourierEquiv burnolUnscaledCommonGapRadius v:BurnolL2) := by
  apply fourierL2.injective
  rw [fourierL2.apply_symm_apply]
  exact (congrArg (fun x:BurnolPaAmbientCarrier => (x:BurnolL2))
    (evenFaceFourier_involutive burnolUnscaledCommonGapRadius v)).symm

private theorem adjoint_inverseFourier (c : BurnolCompletedMellinCoordinate) (v : BurnolL2) :
    fourierL2.symm (sourceAdjoint c v)=
      burnolDirectRightResolvent (star c.value/2) (fourierL2.symm v) := by
  have acted := FiniteMobiusResolventFlux.fourier_R (star c.value/2) (starRightQuarter c) (fourierL2.symm v)
  rw [fourierL2.apply_symm_apply] at acted
  exact (congrArg fourierL2.symm acted).symm.trans (fourierL2.symm_apply_apply _)

theorem physical_adjoint_inverseFourier_quarter_zero (c : BurnolCompletedMellinCoordinate)
    (v : BurnolPaAmbientCarrier) : quarterCotest (fourierL2.symm (sourceAdjoint c v))=0 := by
  let fv := evenFaceFourierEquiv burnolUnscaledCommonGapRadius v
  have acted := right_resolvent_quarter_constant (star c.value/2) (starRightQuarter c)
    (fv:BurnolL2) (burnolConstantGapCoefficient q fv) (physical_gap fv)
  apply Subtype.ext
  change burnolQuarterMeanZeroProjection (burnolQuarterRestriction (fourierL2.symm (sourceAdjoint c v)))=0
  rw [adjoint_inverseFourier,inverseFourier_physical,acted,map_smul]
  have constantZero : burnolQuarterMeanZeroProjection (intervalConstant q)=0 :=
    (burnolQuarterMeanZeroProjection_eq_zero_iff _).mpr (Submodule.mem_span_singleton_self _)
  rw [constantZero,smul_zero]

private theorem adjoint_evenPart (c : BurnolCompletedMellinCoordinate) (v : BurnolPaAmbientCarrier) :
    burnolAmbientEvenPart (sourceAdjoint c v)=sourceAdjoint c v := by
  unfold burnolAmbientEvenPart
  rw [adjoint_even]
  module
private theorem adjoint_fourier_eq_inverse (c : BurnolCompletedMellinCoordinate) (v : BurnolPaAmbientCarrier) :
    fourierL2 (sourceAdjoint c v)=fourierL2.symm (sourceAdjoint c v) := by
  apply fourierL2.injective
  rw [fourierL2_fourierL2,adjoint_even,fourierL2.apply_symm_apply]

/-- The complete B solve for every physical input uses the same fixed power source column. -/
theorem physical_adjoint_complete_correction (c : BurnolCompletedMellinCoordinate) (v : BurnolPaAmbientCarrier) :
    burnolAmbientEvenMeanZeroCorrection (sourceAdjoint c v)=physicalAmplitude c v • hPowerPhysicalCorrection c := by
  have position : burnolAmbientMeanZeroPosition (sourceAdjoint c v)=
      physicalAmplitude c v • SingularCounting.centeredPower c := by
    change quarterCotest (burnolAmbientEvenPart (sourceAdjoint c v))=_
    rw [adjoint_evenPart,physical_adjoint_quarter_source]
  have Fourier : burnolAmbientMeanZeroFourier (sourceAdjoint c v)=0 := by
    change quarterCotest (fourierL2 (burnolAmbientEvenPart (sourceAdjoint c v)))=0
    rw [adjoint_evenPart,adjoint_fourier_eq_inverse,physical_adjoint_inverseFourier_quarter_zero]
  have first : burnolAmbientMeanZeroFirstCorrection (sourceAdjoint c v)=physicalAmplitude c v • hPowerBColumn c := by
    change burnolMeanZeroBlockInverse (burnolAmbientMeanZeroPosition (sourceAdjoint c v)-
      S (burnolAmbientMeanZeroFourier (sourceAdjoint c v)))=_
    rw [position,Fourier,map_zero,sub_zero,map_smul]
    rfl
  have second : burnolAmbientMeanZeroSecondCorrection (sourceAdjoint c v)=physicalAmplitude c v • hPowerBSecond c := by
    change burnolAmbientMeanZeroFourier (sourceAdjoint c v)-S (burnolAmbientMeanZeroFirstCorrection (sourceAdjoint c v))=_
    rw [Fourier,first,map_smul,zero_sub]
    simp only [hPowerBSecond,smul_neg]
  unfold burnolAmbientEvenMeanZeroCorrection burnolAmbientRawMeanZeroCorrection
  rw [first,second]
  simp only [SetLike.val_smul,map_smul]
  rw [←smul_add]
  change burnolAmbientEvenPart (physicalAmplitude c v • _)=_
  unfold burnolAmbientEvenPart
  rw [map_smul]
  change _=physicalAmplitude c v • ((1/2:ℂ) • (_+reflectL2 _))
  module

theorem physical_adjoint_full_defect (c : BurnolCompletedMellinCoordinate) (v : BurnolPaAmbientCarrier) :
    sourceAdjoint c v-(burnolEvenAmbientProjection (sourceAdjoint c v):BurnolL2)=
      physicalAmplitude c v • hPowerPhysicalCorrection c := by
  have projected := burnolEvenOrthogonalProjectionOnto_eq_resolventFormula (sourceAdjoint c v)
  change (burnolEvenAmbientProjection (sourceAdjoint c v):BurnolL2)=_ at projected
  rw [projected]
  unfold burnolAmbientExtendedSonineProjectionFormula
  rw [adjoint_evenPart,physical_adjoint_complete_correction]
  module

/-- True full-L2 adjoint duality computes the entire outside-to-physical channel. -/
theorem original_R_outside_physical_source (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    (burnolEvenAmbientProjection (burnolDirectRightResolvent (c.value/2) (outside value)):BurnolL2)=
      inner ℂ (hPowerPhysicalCorrection c) (outside value) • outsidePhysicalSource c := by
  have member : inner ℂ (hPowerPhysicalCorrection c) (outside value) • outsidePhysicalSource c∈BurnolPaAmbientCarrier :=
    (evenBurnolClosedFace q).toSubmodule.smul_mem _ (outsidePhysicalSource_mem c)
  suffices equal : burnolEvenAmbientProjection (burnolDirectRightResolvent (c.value/2) (outside value))=
      (⟨inner ℂ (hPowerPhysicalCorrection c) (outside value) • outsidePhysicalSource c,member⟩:BurnolPaAmbientCarrier) by
    exact congrArg (fun x:BurnolPaAmbientCarrier => (x:BurnolL2)) equal
  apply ext_inner_left ℂ
  intro test
  have projected := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_left test
    (burnolDirectRightResolvent (c.value/2) (outside value))
  change inner ℂ test (burnolEvenAmbientProjection (burnolDirectRightResolvent (c.value/2) (outside value)))=_ at projected
  rw [projected]
  change inner ℂ (test:BurnolL2) (burnolDirectRightResolvent (c.value/2) (outside value))=_
  have dual := OriginalKCompactAdjointRSource.actual_original_R_adjoint (c.value/2) (rightQuarter c) (test:BurnolL2) (outside value)
  simp only [star_div₀,star_ofNat] at dual
  change inner ℂ (test:BurnolL2) (burnolDirectRightResolvent (c.value/2) (outside value))=
    inner ℂ (sourceAdjoint c test) (outside value) at dual
  rw [dual]
  change inner ℂ (sourceAdjoint c test) (outside value)=
    inner ℂ (test:BurnolL2) (inner ℂ (hPowerPhysicalCorrection c) (outside value) • outsidePhysicalSource c)
  have killed : inner ℂ (burnolEvenAmbientProjection (sourceAdjoint c test):BurnolL2) (outside value)=0 :=
    by
      have outMem : outside value∈(evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmoduleᗮ :=
        Submodule.starProjection_apply_mem _ _
      exact outMem _ (burnolEvenAmbientProjection (sourceAdjoint c test)).property
  have split : sourceAdjoint c test=
      (burnolEvenAmbientProjection (sourceAdjoint c test):BurnolL2)+physicalAmplitude c test • hPowerPhysicalCorrection c := by
    linear_combination (norm := module) physical_adjoint_full_defect c test
  rw [split,inner_add_left,killed,zero_add,inner_smul_left,inner_smul_right]
  have reverse : inner ℂ (test:BurnolL2) (outsidePhysicalSource c)=star (physicalAmplitude c test) := by
    rw [←outsidePhysicalSource_read]
    exact (inner_conj_symm _ _).symm
  rw [reverse]
  simp only [starRingEnd_apply]
  exact mul_comm _ _

theorem original_R_outside_physical_generatedK (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    (burnolEvenAmbientProjection (burnolDirectRightResolvent (c.value/2) (outside value)):BurnolL2)=
      (-2*inner ℂ (hPowerPhysicalCorrection c) (outside value)) • generatedK (barC c) := by
  rw [original_R_outside_physical_source,outsidePhysicalSource,smul_smul]
  congr 1
  ring

section ActualOriginalSource
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
include nontrivial

/-- The original zero-owned Pa-return law leaves the whole generated physical column in Q. -/
theorem actual_R_outside_Q_source (value : BurnolL2) :
    (PA.Q (burnolDirectRightResolvent (observation.coordinate/2) (outside value)):BurnolL2)=
      (-2*inner ℂ (hPowerPhysicalCorrection c) (outside value)) • generatedK (barC c) := by
  have split := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_add_starProjection_orthogonal
    (burnolEvenAmbientProjection (burnolDirectRightResolvent (observation.coordinate/2) (outside value)))
  have all := congrArg (fun x:BurnolPaAmbientCarrier => (x:BurnolL2)) split
  change (PA.E (burnolDirectRightResolvent (observation.coordinate/2) (outside value)):BurnolL2)+
    (PA.Q (burnolDirectRightResolvent (observation.coordinate/2) (outside value)):BurnolL2)=_ at all
  rw [OriginalKDirectRCofinalReentrySourceAction.outside_P_R_E_zero observation nontrivial half.down value,
    ZeroMemClass.coe_zero,zero_add] at all
  exact all.trans (original_R_outside_physical_generatedK c value)

/-- All three original Q-next inputs survive; the full outside input is now a calculated vector. -/
theorem actual_Q_successor_three_sources (depth ordinal : Nat) :
    (PA.Q (OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth (ordinal+1)):BurnolL2)=
      OriginalKDirectRCofinalDivision.sourceCoefficient observation nontrivial half depth ordinal •
        (OriginalKDirectRCofinalDivision.sourceUnit observation nontrivial half:BurnolL2)+
      (PA.Q (burnolDirectRightResolvent (observation.coordinate/2)
        (PA.Q (OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth ordinal):BurnolL2)):BurnolL2)+
      (-2*inner ℂ (hPowerPhysicalCorrection c)
        (outside (OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth ordinal))) • generatedK (barC c) := by
  let raw := OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth ordinal
  have whole := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_add_starProjection_orthogonal
    (burnolEvenAmbientProjection raw)
  have inventory := congrArg (fun x:BurnolPaAmbientCarrier => (x:BurnolL2)) whole
  change (PA.E raw:BurnolL2)+(PA.Q raw:BurnolL2)=(burnolEvenAmbientProjection raw:BurnolL2) at inventory
  have outside_eq : outside raw=raw-(burnolEvenAmbientProjection raw:BurnolL2) :=
    Submodule.starProjection_orthogonal_val raw
  have invisible : PA.invisible raw=(PA.Q raw:BurnolL2)+outside raw := by
    rw [outside_eq]
    unfold PA.invisible
    linear_combination (norm := module) -inventory
  have actual := congrArg (fun x:BurnolPaAmbientCarrier => (x:BurnolL2))
    (OriginalKDirectRCofinalDivision.actual_Q_successor observation nontrivial half depth ordinal)
  change _= _+(PA.Q (OriginalKCombPhysicalAction.R observation nontrivial half (PA.invisible raw)):BurnolL2) at actual
  rw [OriginalKCombCofinalRAction.original_R_direct,invisible] at actual
  change _= _+(PA.Q (burnolDirectRightResolventCLM c ((PA.Q raw:BurnolL2)+outside raw)):BurnolL2) at actual
  rw [map_add,map_add] at actual
  simp only [Submodule.coe_add,Submodule.coe_smul] at actual
  change _=OriginalKDirectRCofinalDivision.sourceCoefficient observation nontrivial half depth ordinal •
    (OriginalKDirectRCofinalDivision.sourceUnit observation nontrivial half:BurnolL2)+
    ((PA.Q (burnolDirectRightResolvent (observation.coordinate/2) (PA.Q raw:BurnolL2)):BurnolL2)+
      (PA.Q (burnolDirectRightResolvent (observation.coordinate/2) (outside raw)):BurnolL2)) at actual
  rw [actual_R_outside_Q_source observation nontrivial half raw] at actual
  simpa only [SetLike.val_smul,add_assoc] using actual
end ActualOriginalSource

end OriginalKCrossParameterRAdjointSource.PhysicalDefectSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
