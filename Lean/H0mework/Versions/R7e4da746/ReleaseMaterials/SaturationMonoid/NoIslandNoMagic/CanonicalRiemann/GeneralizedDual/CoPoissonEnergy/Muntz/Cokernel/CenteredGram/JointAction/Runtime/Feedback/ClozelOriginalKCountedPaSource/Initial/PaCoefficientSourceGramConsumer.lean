import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.PaCoefficientSourceGram
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.PaPowerWholeSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundaryGamma.TerminalConsumer

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace PaCoefficientSourceGramConsumer
open Complex Filter Set
open SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open scoped BigOperators InnerProductSpace Topology
open PaCoefficientSourceGram
local instance : DecidableEq Index := Classical.decEq _
open CenteredGram.IntegralGraphJointAction
namespace H
export SourceGeneratedComplexFeaturePerfectification
  (canonicalHilbertMap canonicalHilbertMap_ker hilbertAmbientRealization hilbertAmbientRealization_source_readback
   hilbertAmbientClosedRangeEquiv hilbertAmbientClosedRangeEquiv_symm_realization)
end H
namespace Port
export OriginalKCrossParameterRAdjointSource.PaNativePortSource (loop port)
end Port
open private paCoefficientSource_mem from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalOutsideVolterraSource.PaAdjointSource
open OriginalKDirectRCofinalOutsideVolterraSource
local instance : CompleteSpace BurnolPaAmbientCarrier :=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def featureGenerator (i : Index) : SourceSpace :=
  H.canonicalHilbertMap burnolCompactCoPoissonLanding (Finsupp.single i 1)
def finiteSpan (F : Finset Index) : Submodule ℂ SourceSpace :=
  Submodule.span ℂ (featureGenerator '' (F:Set Index))
local instance finite_span_dim (F : Finset Index) : FiniteDimensional ℂ (finiteSpan F) :=
  FiniteDimensional.span_of_finite ℂ (F.finite_toSet.image featureGenerator)

private def originalLift (c : BurnolCompletedMellinCoordinate) : SourceSpace :=
  (H.hilbertAmbientClosedRangeEquiv burnolCompactCoPoissonLanding).symm
    ⟨paCoefficientSource c,paCoefficientSource_mem c⟩

private theorem original_lift_read (c : BurnolCompletedMellinCoordinate) :
    H.hilbertAmbientRealization burnolCompactCoPoissonLanding (originalLift c)=paCoefficientSource c :=
  H.hilbertAmbientClosedRangeEquiv_symm_realization burnolCompactCoPoissonLanding _

theorem hilbert_finite_read (c : BurnolCompletedMellinCoordinate) (F : Finset Index) :
    finiteHilbert c F=∑i:↥F,finiteCoefficients c F i • featureGenerator i.1 := by
  rw [finiteHilbert,FG.source_effect_eq]
  change H.canonicalHilbertMap burnolCompactCoPoissonLanding
    (∑i:↥F,Finsupp.single i.1 (finiteCoefficients c F i))=_
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [←Finsupp.smul_single_one,map_smul]
  rfl

private theorem feature_read (i : Index) :
    H.hilbertAmbientRealization burnolCompactCoPoissonLanding (featureGenerator i)=
      burnolCompactCoPoissonGenerator i := by
  rw [featureGenerator,H.hilbertAmbientRealization_source_readback,burnolCompactCoPoissonLanding_single,one_smul]

private theorem original_lift_bill (c : BurnolCompletedMellinCoordinate) (i : Index) :
    inner ℂ (originalLift c) (featureGenerator i)=scalarBill c i := by
  calc
    _=inner ℂ (H.hilbertAmbientRealization burnolCompactCoPoissonLanding (originalLift c))
        (H.hilbertAmbientRealization burnolCompactCoPoissonLanding (featureGenerator i)) :=
      ((H.hilbertAmbientRealization burnolCompactCoPoissonLanding).inner_map_map
        (originalLift c) (featureGenerator i)).symm
    _=scalarBill c i := by
      rw [original_lift_read,feature_read,paCoefficientSource_read c _
        (burnolCompactCoPoissonGenerator_mem_closedRange i),bill_read]

private theorem finite_hilbert_bill (c : BurnolCompletedMellinCoordinate) (F : Finset Index) (i : ↥F) :
    inner ℂ (finiteHilbert c F) (featureGenerator i.1)=scalarBill c i.1 := by
  have equation:=congrArg (fun a:FG.Coordinates ↥F=>a i) (finite_equation c F)
  rw [action_read] at equation
  have realized : H.hilbertAmbientRealization burnolCompactCoPoissonLanding (finiteHilbert c F)=
      physicalSynthesis F (finiteCoefficients c F) := by
    rw [finiteHilbert,FG.source_effect_eq]
    exact H.hilbertAmbientRealization_source_readback burnolCompactCoPoissonLanding _
  have pairing:inner ℂ (featureGenerator i.1) (finiteHilbert c F)=star (scalarBill c i.1) := by
    calc
      _=inner ℂ (H.hilbertAmbientRealization burnolCompactCoPoissonLanding (featureGenerator i.1))
          (H.hilbertAmbientRealization burnolCompactCoPoissonLanding (finiteHilbert c F)) :=
        ((H.hilbertAmbientRealization burnolCompactCoPoissonLanding).inner_map_map
          (featureGenerator i.1) (finiteHilbert c F)).symm
      _=star (scalarBill c i.1) := by
        rw [feature_read,realized]
        exact equation
  calc
    _=star (inner ℂ (featureGenerator i.1) (finiteHilbert c F)) :=
      (_root_.inner_conj_symm (𝕜:=ℂ) (finiteHilbert c F) (featureGenerator i.1)).symm
    _=scalarBill c i.1 := by rw [pairing,star_star]

private theorem finite_hilbert_mem (c : BurnolCompletedMellinCoordinate) (F : Finset Index) :
    finiteHilbert c F∈finiteSpan F := by
  rw [hilbert_finite_read]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i.1,i.2,rfl⟩)

private theorem finite_projection (c : BurnolCompletedMellinCoordinate) (F : Finset Index) :
    finiteHilbert c F=(finiteSpan F).starProjection (originalLift c) := by
  apply Eq.symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (finite_hilbert_mem c F)
  have killed : finiteSpan F≤(innerSL ℂ (originalLift c-finiteHilbert c F)).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,inside,rfl⟩
    change inner ℂ (originalLift c-finiteHilbert c F) (featureGenerator i)=0
    rw [inner_sub_left,original_lift_bill,finite_hilbert_bill c F ⟨i,inside⟩,sub_self]
  exact fun w member=>killed member

private theorem finite_span_mono : Monotone finiteSpan := by
  intro F G included
  apply Submodule.span_mono
  rintro _ ⟨i,inside,rfl⟩
  exact ⟨i,included inside,rfl⟩

theorem refinement_source_law (c : BurnolCompletedMellinCoordinate) (F G : Finset Index)
    (included : F⊆G) (i : ↥F) :
    inner ℂ (finiteHilbert c G-finiteHilbert c F) (featureGenerator i.1)=0 := by
  rw [inner_sub_left,finite_hilbert_bill c G ⟨i.1,included i.2⟩,finite_hilbert_bill c F i,sub_self]

theorem refinement_writer (c : BurnolCompletedMellinCoordinate) (F G : Finset Index) :
    sourceWriter (finiteHilbert c G-finiteHilbert c F)=finiteSource c G-finiteSource c F := by
  rw [map_sub,finite_writer_read,finite_writer_read]

private theorem feature_dense : DenseRange (H.canonicalHilbertMap burnolCompactCoPoissonLanding) := by
  have ranges : Set.range (H.canonicalHilbertMap burnolCompactCoPoissonLanding)=
      Set.range (fun x:LinearMap.range burnolCompactCoPoissonLanding=>(x:SourceSpace)) := by
    ext x
    constructor
    · rintro ⟨u,rfl⟩
      exact ⟨burnolCompactCoPoissonLanding.rangeRestrict u,rfl⟩
    · rintro ⟨⟨_,⟨u,rfl⟩⟩,rfl⟩
      exact ⟨u,rfl⟩
  rw [DenseRange,ranges]
  exact UniformSpace.Completion.denseRange_coe

private theorem finite_spans_dense : ⊤≤(⨆F:Finset Index,finiteSpan F).topologicalClosure := by
  have includes (u : BurnolCompactCoPoissonLinearSource) :
      H.canonicalHilbertMap burnolCompactCoPoissonLanding u∈⨆F:Finset Index,finiteSpan F := by
    induction u using Finsupp.induction_linear with
    | zero=>simp only [map_zero,Submodule.zero_mem]
    | add u v hu hv=>simpa only [map_add] using Submodule.add_mem _ hu hv
    | single i z=>
      have member : featureGenerator i∈finiteSpan {i}:=Submodule.subset_span ⟨i,by simp,rfl⟩
      have scaled:=Submodule.smul_mem (⨆F:Finset Index,finiteSpan F) z ((le_iSup finiteSpan {i}) member)
      simpa only [featureGenerator,←map_smul,Finsupp.smul_single,smul_eq_mul,mul_one] using scaled
  intro x _
  rw [←SetLike.mem_coe,Submodule.topologicalClosure_coe]
  exact closure_mono (by rintro _ ⟨u,rfl⟩;exact includes u) (feature_dense x)

theorem finite_hilbert_tendsto (c : BurnolCompletedMellinCoordinate) :
    Tendsto (finiteHilbert c) atTop (𝓝 (originalLift c)) := by
  have paid:=Submodule.starProjection_tendsto_self finiteSpan finite_span_mono (originalLift c) finite_spans_dense
  exact paid.congr' (Eventually.of_forall (fun F=>(finite_projection c F).symm))

theorem actual_pa_coefficient_source (c : BurnolCompletedMellinCoordinate) :
    (generatedPa c:BurnolPaAmbientCarrier)=paCoefficientSource c := by
  have limit:completedSource c=originalLift c:=(finite_hilbert_tendsto c).limUnder_eq
  change H.hilbertAmbientRealization burnolCompactCoPoissonLanding (completedSource c)=_
  rw [limit,original_lift_read]

theorem actual_source_value (c : BurnolCompletedMellinCoordinate) :
    sourceValue c=burnolTateReciprocalL2 (burnolMobiusSourceL2 (paCoefficientSource c)) := by
  rw [←generated_pa_source]
  change burnolTateReciprocalL2 (burnolMobiusSourceL2 (generatedPa c:BurnolPaAmbientCarrier))=_
  rw [actual_pa_coefficient_source]

theorem finite_source_tendsto (c : BurnolCompletedMellinCoordinate) :
    Tendsto (finiteSource c) atTop (𝓝 (sourceValue c)) := by
  have net : Tendsto (finiteHilbert c) atTop (𝓝 (completedSource c)) := by
    have limit : completedSource c=originalLift c := (finite_hilbert_tendsto c).limUnder_eq
    rw [limit]
    exact finite_hilbert_tendsto c
  have paid: Tendsto (fun F=>sourceWriter (finiteHilbert c F)) atTop
      (𝓝 (sourceWriter (completedSource c))) :=
    (sourceWriter.continuous.tendsto (completedSource c)).comp net
  exact paid.congr' (Eventually.of_forall (finite_writer_read c))

/-- Complete original R inventory, with all finite unit feet generated by the source moments. -/
def wholeProgramme (c : BurnolCompletedMellinCoordinate) (k : Nat) : BurnolL2 :=
  (Port.loop c k (generatedPa c):BurnolL2)+
    ∑i∈Finset.range k,sourceMoment c i •
      ((burnolDirectRightResolventCLM c)^(k-1-i)) (burnolUnitTailResponse c 4)

open private whole_zero_shift from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.PaPowerWholeSource
theorem whole_programme_actual (c : BurnolCompletedMellinCoordinate) (k : Nat) :
    wholeProgramme c k=((burnolDirectRightResolventCLM c)^k) (generatedPa c:BurnolL2) := by
  rw [whole_zero_shift]
  simp only [wholeProgramme,source_moment_actual]

section OriginalReceipt
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
namespace RJ
export OriginalWholeDebtRJointMobiusReturnJordanSource (paJet actual_exact_order_Pa)
end RJ
namespace W
export OriginalKReturnJordanSourceWriteback (actualPrefixInput actualValue actual_prefix_value actual_next_value)
end W
namespace Terminal
export OriginalBoundaryGammaTerminalConsumer
  (currentPrefix currentPrefixReceipt currentPrefixTrace current_prefix_read current_original_prefix current_original_R originalWholeNext)
end Terminal
def returnCoefficient : ℂ :=
  OriginalWholeDebtRJointMobiusReturnAction.returnAmplitude observation nontrivial half*
    OriginalKFiniteOrderRelease.UnitPowerSource.paPowerCoefficient observation half
def piSource : BurnolPaAmbientCarrier := returnCoefficient observation nontrivial half • (generatedPa c:BurnolPaAmbientCarrier)
def prefixProgramme (k : Nat) : BurnolL2 := returnCoefficient observation nontrivial half • wholeProgramme c k

/-- The finite mathematical calculation is read at the existing original R receipt. -/
def calculationAtOriginalReceipt (depth ordinal : Nat) (t : ℝ) (N : Nat) (F G : Finset Index)
    (included : F⊆G) :=
  (Terminal.currentPrefixReceipt observation nontrivial half depth ordinal t N,
   Terminal.currentPrefixTrace observation nontrivial half depth ordinal t N,
   finiteRefinement c F G,PLift.up (refinement_source_law c F G included),
   PLift.up (refinement_writer c F G))

theorem original_pi_read : RJ.paJet observation nontrivial half m=piSource observation nontrivial half := by
  rw [RJ.actual_exact_order_Pa]
  unfold piSource returnCoefficient OriginalKFiniteOrderRelease.UnitPowerSource.paPowerField
  rw [actual_pa_coefficient_source,smul_smul]

theorem prefix_programme_actual (k : Nat) : prefixProgramme observation nontrivial half k=
    CombSource.Division.rawIterate observation half.down k
      (RJ.paJet observation nontrivial half m:BurnolL2) := by
  rw [prefixProgramme,whole_programme_actual,original_pi_read]
  change returnCoefficient observation nontrivial half •
      ((burnolDirectRightResolventCLM c)^k) (generatedPa c:BurnolL2)=
    ((burnolDirectRightResolventCLM c)^k)
      (returnCoefficient observation nontrivial half • (generatedPa c:BurnolL2))
  rw [map_smul]

theorem actual_original_prefix (depth ordinal : Nat) (t : ℝ) (N : Nat) :
    Terminal.currentPrefix observation nontrivial half depth ordinal t N=
      prefixProgramme observation nontrivial half m := by
  rw [Terminal.current_original_prefix,W.actual_prefix_value]
  exact (prefix_programme_actual observation nontrivial half m).symm

theorem actual_original_next (depth : Nat) :
    W.actualValue observation nontrivial half depth 1=prefixProgramme observation nontrivial half (m+1) := by
  rw [W.actual_next_value]
  exact (prefix_programme_actual observation nontrivial half (m+1)).symm

theorem actual_original_R (depth ordinal : Nat) (t : ℝ) (N : Nat) :
    burnolDirectRightResolventCLM c (prefixProgramme observation nontrivial half m)=
      W.actualValue observation nontrivial half depth 1 := by
  rw [←actual_original_prefix observation nontrivial half depth ordinal t N]
  exact Terminal.current_original_R observation nontrivial half depth ordinal t N

theorem actual_receipt_value (depth ordinal : Nat) (t : ℝ) (N : Nat) :
    (Terminal.currentPrefixReceipt observation nontrivial half depth ordinal t N).value=
      prefixProgramme observation nontrivial half m :=
  (Terminal.current_prefix_read observation nontrivial half depth ordinal t N).trans
    (actual_original_prefix observation nontrivial half depth ordinal t N)

def actual_source_trace (depth ordinal : Nat) (t : ℝ) (N : Nat) :
    Trace (OriginalKCombReceiptFeedback.receipt observation nontrivial depth half).1.environment
      (OriginalKCombReceiptFeedback.returnJordanPrefixCode observation nontrivial depth half)
      (.const (prefixProgramme observation nontrivial half m)) := by
  rw [←actual_original_prefix observation nontrivial half depth ordinal t N]
  exact Terminal.currentPrefixTrace observation nontrivial half depth ordinal t N

theorem actual_original_terminal_source (depth ordinal : Nat) (t : ℝ) (N : Nat) :
    inner ℂ (OriginalWholeDebtRAdjointContactSource.sourceEffect c c)
      (prefixProgramme observation nontrivial half m)=
      star (OriginalBoundaryGammaTerminalConsumer.targetGamma observation nontrivial half depth ordinal t N)*
        OriginalWholeDebtRJointMobiusReturnJordanSource.feedback observation nontrivial half*
        burnolAnalyticComplementExpectedPhysicalFourierRead ActualAnalyticOwner observation := by
  rw [←actual_original_prefix observation nontrivial half depth ordinal t N]
  exact OriginalBoundaryGammaTerminalConsumer.actual_terminal_price observation nontrivial half depth ordinal t N

set_option maxHeartbeats 250000 in
/-- The original receipt, its trace and the original whole/next are consumed together. -/
def actual_original_receipt_consumer (depth ordinal : Nat) (t : ℝ) (N : Nat) (F G : Finset Index)
    (included : F⊆G) :
    Σ' whole : type_of% (Terminal.originalWholeNext observation nontrivial half depth ordinal),
      PProd (whole=Terminal.originalWholeNext observation nontrivial half depth ordinal) (
      PProd (type_of% (calculationAtOriginalReceipt observation nontrivial half depth ordinal t N F G included)) (
      PProd (type_of% (actual_source_trace observation nontrivial half depth ordinal t N)) (
      PProd (type_of% (actual_receipt_value observation nontrivial half depth ordinal t N)) (
      PProd (type_of% (actual_original_prefix observation nontrivial half depth ordinal t N)) (
      PProd (type_of% (actual_original_R observation nontrivial half depth ordinal t N)) (
      PProd (type_of% (actual_original_next observation nontrivial half depth))
        (type_of% (actual_original_terminal_source observation nontrivial half depth ordinal t N)))))))) := by
  exact ⟨Terminal.originalWholeNext observation nontrivial half depth ordinal,rfl,
    calculationAtOriginalReceipt observation nontrivial half depth ordinal t N F G included,
    actual_source_trace observation nontrivial half depth ordinal t N,
    actual_receipt_value observation nontrivial half depth ordinal t N,
    actual_original_prefix observation nontrivial half depth ordinal t N,
    actual_original_R observation nontrivial half depth ordinal t N,
    actual_original_next observation nontrivial half depth,
    actual_original_terminal_source observation nontrivial half depth ordinal t N⟩
end OriginalReceipt
end PaCoefficientSourceGramConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
