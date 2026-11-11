import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusForcedPriceConsumer

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRJointMobiusJetFeedbackSource
open Complex MeasureTheory Set BurnolPhysicalState
open OriginalKSourceResolventReconstruction OriginalKDirectRCofinalOutsideVolterraSource
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open OriginalKCrossParameterRAdjointSource.CayleyIntertwiningSource
open OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
open OriginalKCrossParameterRAdjointSource.UnweightedCayleySource
open scoped InnerProductSpace BigOperators
open private paCoefficientSource_mem from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalOutsideVolterraSource.PaAdjointSource
open private source_C_adjoint_block P_O from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CayleyIntertwiningSource
open private actualAdjoint_read from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFullAdjointSource.Source
namespace J
export OriginalKFiniteOrderRelease.UnitPowerJordanSource
  (sourceStep sourceStep_actual sourceField sourceOutside sourceCoefficient sourceConstant
    sourceAmplitude sourceTail logOutsideColumn sourceQ sourceQCarrier sourceQ_mem
    source_outside_actual source_full_inventory)
end J
namespace A
export OriginalWholeDebtRJointMobiusReturnJordanSource
  (jet paJet actual_jet actual_jet_next actual_complete_inventory actual_exact_order_Pa actual_pa_member)
end A
local notation "E" => OriginalKCombCofinalPaAction.E
local notation "Q" => OriginalKCombCofinalPaAction.Q
local notation "P" => burnolEvenAmbientProjectionEndomorphism
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder
local notation "F" => fourierL2
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local instance : CompleteSpace BurnolPaAmbientCarrier :=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

theorem invisible_adjoint_reentry (c : BurnolCompletedMellinCoordinate)
    (input : BurnolL2) (invisible : E input=0) :
    E (J.sourceStep c input)=inner ℂ (burnolUnitTailResponse c 4) input • paCoefficientSource c := by
  have killed (p : BurnolPaAmbientCarrier) (inside : p∈burnolCompactCoPoissonClosedRange) :
      inner ℂ (p : BurnolL2) input=0 := by
    have read:=OriginalKCombCofinalPaAction.wholePa_normal_read input p inside
    rw [invisible,inner_zero_right] at read
    exact read.symm
  have normal (p : BurnolPaAmbientCarrier) (inside : p∈burnolCompactCoPoissonClosedRange) :
      inner ℂ p (E (J.sourceStep c input))=
        inner ℂ p (inner ℂ (burnolUnitTailResponse c 4) input • paCoefficientSource c) := by
    have split : burnolDirectRightResolventCLM c (p : BurnolL2)=
        (burnolPaSourceCorrection c ⟨p,inside⟩ : BurnolL2)+
          burnolPaResolventSourceCoefficient c p • burnolUnitTailResponse c 4 := by
      change burnolDirectRightResolvent ((c).value/2) (p : BurnolL2)=
        (burnolDirectRightResolvent ((c).value/2) (p : BurnolL2)-
          burnolPaResolventSourceCoefficient c p • burnolUnitTailResponse c 4)+_
      module
    have covector:=inner_conj_symm (𝕜:=ℂ) (paCoefficientSource c) p
    rw [paCoefficientSource_read c p inside] at covector
    rw [OriginalKCombCofinalPaAction.wholePa_normal_read _ p inside,
      ←J.sourceStep_actual,ContinuousLinearMap.adjoint_inner_right,split,
      inner_add_left,inner_smul_left,killed _ (burnolPaSourceCorrection_mem c _),
      zero_add,inner_smul_right,←covector]
    simp only [starRingEnd_apply,star_star]
    ring
  have member : E (J.sourceStep c input)-
      inner ℂ (burnolUnitTailResponse c 4) input • paCoefficientSource c∈burnolCompactCoPoissonClosedRange :=
    burnolCompactCoPoissonClosedRange.toSubmodule.sub_mem (Submodule.starProjection_apply_mem _ _)
      (burnolCompactCoPoissonClosedRange.toSubmodule.smul_mem _ (paCoefficientSource_mem c))
  have zero : inner ℂ (E (J.sourceStep c input)-
      inner ℂ (burnolUnitTailResponse c 4) input • paCoefficientSource c)
    (E (J.sourceStep c input)-inner ℂ (burnolUnitTailResponse c 4) input • paCoefficientSource c)=0 := by
    rw [inner_sub_right,normal _ member,sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp zero)

private theorem outside_invisible (value : BurnolL2) : E (O value)=0 := by
  change burnolCompactCoPoissonClosedRange.toSubmodule.starProjection (burnolEvenAmbientProjection (O value))=0
  have zero : burnolEvenAmbientProjection (O value)=0:=Subtype.ext (P_O value)
  rw [zero,map_zero]

private theorem q_invisible (value : BurnolPaAmbientCarrier)
    (inside : value∈burnolCompactCoPoissonClosedRange.toSubmoduleᗮ) : E (value : BurnolL2)=0 := by
  change burnolCompactCoPoissonClosedRange.toSubmodule.starProjection (burnolEvenAmbientProjection (value : BurnolL2))=0
  have physical : burnolEvenAmbientProjection (value : BurnolL2)=value:=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self value
  rw [physical,Submodule.starProjection_apply,
    Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal inside,Submodule.coe_zero]

theorem outside_adjoint_physical (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    P (J.sourceStep c (O value))=
      (-2*inner ℂ (physicalOutsideColumn c) (O value)) • F (generatedK c) := by
  have block:=source_C_adjoint_block c value
  rw [sourceCayley_actual_adjoint,sourceAdjointCayley,map_add,map_smul,P_O,zero_add,
    ←actualAdjoint_read,J.sourceStep_actual] at block
  have nonzero : (sourceDamping c : ℂ)≠0:=Complex.ofReal_ne_zero.mpr (sourceDamping_pos c).ne'
  have scaled:=congrArg (fun v : BurnolL2=>(sourceDamping c : ℂ)⁻¹ • v) block
  rw [smul_smul,inv_mul_cancel₀ nonzero,one_smul,smul_smul] at scaled
  have scalar : (sourceDamping c : ℂ)⁻¹*(-2*(sourceDamping c : ℂ)*inner ℂ (physicalOutsideColumn c) (O value))=
      -2*inner ℂ (physicalOutsideColumn c) (O value) := by field_simp [nonzero]
  rw [scalar] at scaled
  exact scaled

private theorem sourceOutside_succ (c : BurnolCompletedMellinCoordinate) (j : Nat) :
    J.sourceOutside c (j+1)=J.sourceAmplitude c j • J.logOutsideColumn c 0+
      ∑ k∈Finset.range j,(-2*J.sourceCoefficient c j k) • J.logOutsideColumn c (k+1) := by
  unfold J.sourceOutside
  rw [Finset.sum_range_succ']
  simp only [J.sourceCoefficient]
  rw [add_comm]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "eta" => OriginalWholeDebtRJointMobiusReturnAction.returnAmplitude observation nontrivial half
local notation "pi" => A.paJet observation nontrivial half m
local notation "current" => A.jet observation nontrivial half m
local notation "q" => (1/4 : ℝ)

def currentQ : BurnolPaAmbientCarrier:=eta • J.sourceQCarrier observation half

def currentOutside : BurnolL2:=eta • J.sourceOutside c m

def outsidePrice : ℂ:=∑ k∈Finset.range m,
  J.sourceCoefficient c m k*inner ℂ (physicalOutsideColumn c) (J.logOutsideColumn c k)

def unitMoment : ℂ:=inner ℂ (burnolUnitTailResponse c 4) (currentQ observation nontrivial half : BurnolL2)

/-- Current full source tail and the retained homogeneous column generate the next log contact. -/
def nextTail : ℂ := -2*(J.sourceTail c current+
  eta*J.sourceConstant c m*(q : ℂ)^(1-star (c).value)/(1-star (c).value))

/-- All current finite log columns advance together; no next outside target is read. -/
def nextOutside : BurnolL2 := nextTail observation nontrivial half • J.logOutsideColumn c 0+
  ∑ k∈Finset.range m,(-2*eta*J.sourceCoefficient c m k) • J.logOutsideColumn c (k+1)

def nextPa : BurnolPaAmbientCarrier := E (J.sourceStep c (pi : BurnolL2))+
  unitMoment observation nontrivial half • paCoefficientSource c

def nextQ : BurnolPaAmbientCarrier := Q (J.sourceStep c ((pi : BurnolL2)+
  (currentQ observation nontrivial half : BurnolL2)))+
    (-2*eta*outsidePrice observation nontrivial half) •
      evenFaceFourierEquiv burnolUnscaledCommonGapRadius (burnolCompletedMellinRieszVector c)

def nextWhole : BurnolL2 := (nextPa observation nontrivial half : BurnolL2)+
  (nextQ observation nontrivial half : BurnolL2)+nextOutside observation nontrivial half

private theorem current_inventory : current=(pi : BurnolL2)+
    (currentQ observation nontrivial half : BurnolL2)+currentOutside observation nontrivial half := by
  rw [A.actual_complete_inventory observation nontrivial half,A.actual_exact_order_Pa observation nontrivial half]
  unfold currentQ currentOutside J.sourceQCarrier
  simp only [SetLike.val_smul]
  module

private theorem current_Q_member : currentQ observation nontrivial half∈
    burnolCompactCoPoissonClosedRange.toSubmoduleᗮ :=
  burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.smul_mem _ (J.sourceQ_mem observation nontrivial half)

private theorem current_outside : O current=currentOutside observation nontrivial half := by
  have subtraction : O (J.sourceField c m)=J.sourceField c m-P (J.sourceField c m):=
    Submodule.starProjection_orthogonal_val _
  have source : O (J.sourceField c m)=J.sourceOutside c m:=
    subtraction.trans (J.source_outside_actual c m)
  rw [A.actual_jet,map_smul,source]
  rfl

private theorem actual_outside_price : inner ℂ (physicalOutsideColumn c)
    (currentOutside observation nontrivial half)=eta*outsidePrice observation nontrivial half := by
  unfold currentOutside J.sourceOutside outsidePrice
  simp only [inner_smul_right,inner_sum]

private theorem unit_outside_zero : inner ℂ (burnolUnitTailResponse c 4) (O current)=0 := by
  have orthogonal : O current∈(evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmoduleᗮ:=Submodule.starProjection_apply_mem _ _
  exact orthogonal (burnolZeroOwnedUnitTailState observation nontrivial half.down)
    (burnolZeroOwnedUnitTailState observation nontrivial half.down).property

private theorem outside_next_Pa_zero : E (J.sourceStep c (O current))=0 := by
  rw [invisible_adjoint_reentry c _ (outside_invisible current),unit_outside_zero,zero_smul]

/-- Q's actual whole-unit moment, not a finite-window/full-source identification, produces the new Pa component. -/
theorem actual_next_Pa : E (J.sourceStep c current)=nextPa observation nontrivial half := by
  rw [current_inventory,map_add,map_add,map_add,map_add,
    invisible_adjoint_reentry c _ (q_invisible _ (current_Q_member observation nontrivial half))]
  rw [←current_outside, outside_next_Pa_zero,add_zero]
  rfl

/-- The entire log-B input acts through the original C-adjoint block before its Q vector is read. -/
theorem actual_next_Q : Q (J.sourceStep c current)=nextQ observation nontrivial half := by
  have split:=burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_add_starProjection_orthogonal
    (burnolEvenAmbientProjection (J.sourceStep c (O current)))
  have typed:=congrArg (fun value : BurnolPaAmbientCarrier=>(value : BurnolL2)) split
  change (E (J.sourceStep c (O current)) : BurnolL2)+(Q (J.sourceStep c (O current)) : BurnolL2)=
    P (J.sourceStep c (O current)) at typed
  rw [outside_next_Pa_zero,ZeroMemClass.coe_zero,zero_add,outside_adjoint_physical] at typed
  have price : inner ℂ (physicalOutsideColumn c) (O current)=eta*outsidePrice observation nontrivial half := by
    rw [current_outside,actual_outside_price]
  rw [price] at typed
  have source : Q (J.sourceStep c (O current))=
      (-2*eta*outsidePrice observation nontrivial half) • evenFaceFourierEquiv burnolUnscaledCommonGapRadius (burnolCompletedMellinRieszVector c) := by
    apply Subtype.ext
    rw [typed]
    simp only [SetLike.val_smul,generatedK_eq_original]
    congr 1
    ring
  rw [current_inventory,map_add,map_add]
  rw [←current_outside,source]
  rfl

private theorem actual_next_tail : nextTail observation nontrivial half=eta*J.sourceAmplitude c m := by
  unfold nextTail J.sourceAmplitude
  rw [A.actual_jet,map_smul]
  simp only [smul_eq_mul]
  ring

/-- The outside/log successor is generated by the previous full tail and every previous log column. -/
theorem actual_next_outside : O (J.sourceStep c current)=nextOutside observation nontrivial half := by
  have subtraction : O (J.sourceField c (m+1))=J.sourceField c (m+1)-P (J.sourceField c (m+1)):=
    Submodule.starProjection_orthogonal_val _
  have source : O (J.sourceField c (m+1))=J.sourceOutside c (m+1):=
    subtraction.trans (J.source_outside_actual c (m+1))
  have next : J.sourceStep c current=A.jet observation nontrivial half (m+1):=by
    rw [A.actual_jet_next,J.sourceStep_actual]
  rw [next,A.actual_jet,map_smul,source,sourceOutside_succ,smul_add,Finset.smul_sum]
  unfold nextOutside
  rw [actual_next_tail]
  simp only [smul_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  ring

/-- One actual full R* event generates the complete Pa+Q+outside successor. -/
theorem actual_next_whole : J.sourceStep c current=nextWhole observation nontrivial half := by
  have split:=burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_add_starProjection_orthogonal
    (burnolEvenAmbientProjection (J.sourceStep c current))
  have typed:=congrArg (fun value : BurnolPaAmbientCarrier=>(value : BurnolL2)) split
  change (E (J.sourceStep c current) : BurnolL2)+(Q (J.sourceStep c current) : BurnolL2)=P (J.sourceStep c current) at typed
  have whole : O (J.sourceStep c current)=J.sourceStep c current-P (J.sourceStep c current) :=
    Submodule.starProjection_orthogonal_val _
  rw [actual_next_Pa,actual_next_Q] at typed
  rw [actual_next_outside] at whole
  unfold nextWhole
  linear_combination (norm:=module) -whole-typed

/-- The next input's full original Pa qualification is generated by the two actual source pieces. -/
theorem nextPa_mem : nextPa observation nontrivial half∈burnolCompactCoPoissonClosedRange :=
  burnolCompactCoPoissonClosedRange.toSubmodule.add_mem (Submodule.starProjection_apply_mem _ _)
    (burnolCompactCoPoissonClosedRange.toSubmodule.smul_mem _ (paCoefficientSource_mem c))

def nextFeedback : ℂ:=burnolPaResolventSourceCoefficient c (nextPa observation nontrivial half)

def nextPaR : BurnolL2:=burnolDirectRightResolventCLM c (nextPa observation nontrivial half : BurnolL2)

/-- The new Pa source's own literal R action immediately consumes the generated qualification. -/
theorem actual_newPa_R_update : nextPaR observation nontrivial half=
    (burnolPaSourceCorrection c ⟨nextPa observation nontrivial half,nextPa_mem observation nontrivial half⟩ : BurnolL2)+
      nextFeedback observation nontrivial half • burnolUnitTailResponse c 4 := by
  change burnolDirectRightResolvent ((c).value/2) (nextPa observation nontrivial half : BurnolL2)=
    (burnolDirectRightResolvent ((c).value/2) (nextPa observation nontrivial half : BurnolL2)-
      nextFeedback observation nontrivial half • burnolUnitTailResponse c 4)+_
  module

/-- The arithmetic remainder consumes this new Pa event, retaining its actual recovered L2 source. -/
theorem actual_newPa_remainder_action (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (burnolMobiusSourceL2 (nextPa observation nontrivial half)) test=
      ∫ x : ℝ,test x*(nextPa observation nontrivial half : BurnolL2) x :=
  burnolRemainderSourceRead_Pa _ (nextPa_mem observation nontrivial half) test

/-- The source feedback includes the actual Q unit moment and the whole existing Pa covector norm. -/
theorem actual_next_feedback : nextFeedback observation nontrivial half=
    burnolPaResolventSourceCoefficient c (E (J.sourceStep c (pi : BurnolL2)))+
      unitMoment observation nontrivial half*((‖paCoefficientSource c‖^2 : ℝ) : ℂ) := by
  unfold nextFeedback nextPa
  rw [map_add,map_smul,←paCoefficientSource_read c _ (paCoefficientSource_mem c),inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

/-- The generated Q and outside fields retain their original orthogonal carriers. -/
theorem nextQ_mem : nextQ observation nontrivial half∈burnolCompactCoPoissonClosedRange.toSubmoduleᗮ := by
  rw [←actual_next_Q]
  exact Submodule.starProjection_apply_mem _ _

theorem nextOutside_orthogonal : nextOutside observation nontrivial half∈
    (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmoduleᗮ := by
  rw [←actual_next_outside]
  exact Submodule.starProjection_apply_mem _ _

/-- This is the literal next full jet value; no old actor/cofinal occurrence is asserted. -/
theorem actual_next_literal_jet : nextWhole observation nontrivial half=A.jet observation nontrivial half (m+1) := by
  rw [←actual_next_whole,A.actual_jet_next,J.sourceStep_actual]

end OriginalWholeDebtRJointMobiusJetFeedbackSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
