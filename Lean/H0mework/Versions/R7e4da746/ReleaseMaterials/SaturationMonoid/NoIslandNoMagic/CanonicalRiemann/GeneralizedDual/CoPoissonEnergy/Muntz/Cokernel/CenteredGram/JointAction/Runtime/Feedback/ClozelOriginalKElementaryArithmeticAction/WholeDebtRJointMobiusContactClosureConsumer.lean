import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusContactClosureSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusWholeLoopRSource

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRJointMobiusContactClosureConsumer
open Complex MeasureTheory BurnolPhysicalState
open OriginalWholeDebtRJointMobiusContactClosureSource OriginalWholeDebtRAdjointContactSource
open OriginalKPairedBEulerJunctionSource OriginalKPairedBEulerJunctionSource.BandFullStockEuler
open OriginalKCrossParameterRAdjointSource.CayleyIntertwiningSource
open OriginalKCrossParameterRAdjointSource.UnweightedCayleySource
open OriginalKSourceResolventReconstruction OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
open OriginalWholeDebtRJointMobiusCoupledCayleySource OriginalWholeDebtRPowerWaveDilationSource
open scoped InnerProductSpace
open private full_source_balance correction_physical_price sigma_ne_zero from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRAdjointContactSource
namespace L
export OriginalWholeDebtRJointMobiusWholeLoopRSource
  (wholeLoop next actualLoop actual_whole_next outsideCoefficient)
end L
namespace J
export OriginalWholeDebtRJointMobiusReturnJordanSource
  (paJet actual_pa_member feedback actual_feedback_ne_zero actual_exact_order_Fourier)
end J
local notation "F" => fourierL2
local notation "P" => burnolEvenAmbientProjectionEndomorphism
local notation "C" => correctionRaw
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "E" => OriginalKCombCofinalPaAction.E
local notation "Q" => OriginalKCombCofinalPaAction.Q
local instance : CompleteSpace BurnolPaAmbientCarrier :=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

/-- This is the original full forcing block, with the actual regular/contact coefficient reduced to its finite second-B source. -/
theorem actual_coupled_contact_face (c : BurnolCompletedMellinCoordinate) :
    P (contactForcing c)=coupling c • P (dualKernelBoundary c)+
      (damping c : ℂ) • P (pairedSource c junctionShift)+
        (1/2 : ℂ) • (coefficient c (barC c) • F (generatedK (barC c))) := by
  change P (coupling c • dualKernelBoundary c+(damping c : ℂ) • pairedSource c junctionShift+
    (1/2 : ℂ) • sourceEffect c (barC c))=_
  rw [map_add,map_add,map_smul,map_smul,map_smul]
  change _+(1/2 : ℂ) • (closureInput c (barC c) : BurnolL2)=_
  rw [actual_input]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "b" => L.outsideCoefficient observation nontrivial half
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "e" => burnolAnalyticComplementExpectedPhysicalFourierRead ActualAnalyticOwner observation
local notation "Rpow" => CombSource.Division.rawIterate observation half.down
local notation "p" => J.paJet observation nontrivial half m

/-- Actual R(wholeLoop), its complete B column and the actual regular/contact cotest consume the same finite source price. -/
theorem actual_loop_whole_cotest :
    inner ℂ (sourceEffect c c) (L.wholeLoop c)=star (sigma c c)*b*star (finitePrice c c) := by
  have killed : inner ℂ (C c) (L.wholeLoop c)=0 :=
    correction_physical_price c _ (L.actualLoop observation nontrivial half).property
  have reverse : inner ℂ (C c) (physicalOutsideColumn c)=star (finitePrice c c) := by
    rw [←actual_finite_price]
    exact (inner_conj_symm _ _).symm
  have price : inner ℂ (C c) (burnolDirectRightResolventCLM c (L.wholeLoop c))=b*star (finitePrice c c) := by
    change inner ℂ (C c) (L.next c)=_
    rw [L.actual_whole_next observation nontrivial half,inner_add_right,
      correction_physical_price c _ (burnolEvenAmbientProjection (L.next c)).property,
      zero_add,inner_smul_right,reverse]
  rw [full_source_balance,actual_source_action,inner_add_left,inner_smul_left,inner_smul_left,
    ←actual_R_cotest c c (L.wholeLoop c),killed,mul_zero,add_zero,price]
  simp only [starRingEnd_apply]
  ring

/-- The independent nonzero exact-m Pa return supplies its own actual physical test; no old delta or occurrence is borrowed. -/
theorem actual_newPa_finite_effect :
    inner ℂ (sourceEffect c c) (Rpow m (p : BurnolL2))=
      star (coefficient c c)*J.feedback observation nontrivial half*e := by
  let physical : BurnolPaAmbientCarrier:=⟨Rpow m (p : BurnolL2),
    CombSource.Division.whole_pa_physical observation nontrivial half.down m le_rfl p
      (J.actual_pa_member observation nontrivial half m)⟩
  have projected := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_right
    physical (sourceEffect c c)
  change inner ℂ (closureInput c c : BurnolL2) (Rpow m (p : BurnolL2))=
    inner ℂ (sourceEffect c c) (Rpow m (p : BurnolL2)) at projected
  rw [←projected,actual_input,inner_smul_left,generatedK_eq_original,
    J.actual_exact_order_Fourier observation nontrivial half]
  simp only [starRingEnd_apply]
  ring

/-- The full source effect's first Pa release is decided by the actual finite B source, without a supplied sign or vanishing premise. -/
theorem actual_newPa_effect_zero_iff :
    inner ℂ (sourceEffect c c) (Rpow m (p : BurnolL2))=0 ↔ finitePrice c c=0 := by
  rw [actual_newPa_finite_effect observation nontrivial half]
  have feedbackNe:=J.actual_feedback_ne_zero observation nontrivial half
  have eNe:=burnolAnalyticComplementExpectedPhysicalFourierRead_ne_zero observation nontrivial
  constructor
  · intro zero
    have pairZero:star (coefficient c c)*J.feedback observation nontrivial half=0 :=
      (mul_eq_zero.mp zero).resolve_right eNe
    have starredZero:star (coefficient c c)=0 := (mul_eq_zero.mp pairZero).resolve_right feedbackNe
    have nativeZero:coefficient c c=0 := by simpa only [star_eq_zero] using starredZero
    exact (mul_eq_zero.mp nativeZero).resolve_left (mul_ne_zero (by norm_num) (sigma_ne_zero c c))
  · intro zero
    simp only [coefficient,zero,mul_zero,star_zero,zero_mul]

/-- This new closed source update has zero Pa component, while its complete Q and B vectors remain explicit. -/
theorem actual_closed_next_Pa_zero : E (OriginalWholeDebtRJointMobiusContactClosureSource.next c c)=0 := by
  change burnolCompactCoPoissonClosedRange.toSubmodule.starProjection
    (burnolEvenAmbientProjection (OriginalWholeDebtRJointMobiusContactClosureSource.next c c))=0
  have member : burnolEvenAmbientProjection (OriginalWholeDebtRJointMobiusContactClosureSource.next c c) ∈
      burnolCompactCoPoissonClosedRange.toSubmoduleᗮ := by
    intro test testPa
    have projected := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_left
      test (OriginalWholeDebtRJointMobiusContactClosureSource.next c c)
    change inner ℂ test (burnolEvenAmbientProjection (OriginalWholeDebtRJointMobiusContactClosureSource.next c c))=
      inner ℂ (test : BurnolL2) (OriginalWholeDebtRJointMobiusContactClosureSource.next c c) at projected
    rw [projected,actual_whole_next,inner_smul_right,inner_sub_right,inner_sub_right,
      inner_smul_right,inner_smul_right,inner_smul_right,generatedK_eq_original,generatedK_eq_original]
    have kbar:=riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal (barC c)
      (show riemannZeta (barC c).value=0 from observation.conjugate_mathlibZero)
    let k : BurnolPaOrthogonalCarrier:=⟨burnolCompletedMellinRieszVector c,
      riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal c observation.mathlibZero⟩
    have fk:=(burnolCompactCoPoissonActionSquare.orthogonalAction k).property
    have fzero : inner ℂ (test : BurnolL2) (F (burnolCompletedMellinRieszVector c : BurnolL2))=0 :=
      fk test testPa
    have kzero : inner ℂ (test : BurnolL2) (burnolCompletedMellinRieszVector (barC c) : BurnolL2)=0 :=
      kbar test testPa
    rw [kzero,fzero,outsideColumn_orthogonal c (test : BurnolL2) test.property]
    simp only [mul_zero,sub_zero]
  rw [Submodule.starProjection_apply,
    Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal member,Submodule.coe_zero]

/-- Pa+Q+outside inventory is on this literal new update, independently of every cofinal history. -/
theorem actual_closed_next_whole : OriginalWholeDebtRJointMobiusContactClosureSource.next c c=
    (Q (OriginalWholeDebtRJointMobiusContactClosureSource.next c c) : BurnolL2)+
      (-2*inner ℂ (F (generatedK c)) (closureInput c c : BurnolL2)) • physicalOutsideColumn c := by
  have split:=burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_add_starProjection_orthogonal
    (burnolEvenAmbientProjection (OriginalWholeDebtRJointMobiusContactClosureSource.next c c))
  change E (OriginalWholeDebtRJointMobiusContactClosureSource.next c c)+Q (OriginalWholeDebtRJointMobiusContactClosureSource.next c c)=_ at split
  rw [actual_closed_next_Pa_zero observation nontrivial half,zero_add] at split
  have whole : OriginalKCombPhysicalAction.physicalRemainder (OriginalWholeDebtRJointMobiusContactClosureSource.next c c)=
      OriginalWholeDebtRJointMobiusContactClosureSource.next c c-P (OriginalWholeDebtRJointMobiusContactClosureSource.next c c) :=
    Submodule.starProjection_orthogonal_val _
  have physical:=congrArg (fun v : BurnolPaAmbientCarrier=>(v : BurnolL2)) split
  change (Q (OriginalWholeDebtRJointMobiusContactClosureSource.next c c) : BurnolL2)=P (OriginalWholeDebtRJointMobiusContactClosureSource.next c c) at physical
  rw [actual_B_effect,←physical] at whole
  linear_combination (norm:=module) -whole

end OriginalWholeDebtRJointMobiusContactClosureConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
