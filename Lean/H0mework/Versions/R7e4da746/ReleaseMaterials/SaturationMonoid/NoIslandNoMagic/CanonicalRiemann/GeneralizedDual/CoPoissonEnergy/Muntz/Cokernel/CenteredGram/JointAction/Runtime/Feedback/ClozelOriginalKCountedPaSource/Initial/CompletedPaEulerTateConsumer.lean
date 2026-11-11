import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource.WeakWard.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option maxErrors 1
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.CompletedPaEulerTateBoundary
open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Topology BigOperators
open CenteredGram.IntegralGraphJointAction
namespace C
export CountedPaInitial.CompletedSourceRCalculation
 (sourceFace prefixCode environment prefix_source actual_completed_original_R same_original_child
  value physical_R_source same_original_next)
end C
namespace Q
export PaCoefficientSourceGram (generatedPa)
end Q
namespace P
export PaCoefficientSourceGramConsumer (wholeProgramme whole_programme_actual prefixProgramme returnCoefficient)
end P
namespace Port
export OriginalKCrossParameterRAdjointSource.PaNativePortSource (loop)
end Port
namespace G
export OriginalKFiniteOrderRelease.GenericSourceStepBAction
 (currentAmplitude firstNext secondNext gapSecondNext actual_forward_R_B actual_forward_R_gap_B)
end G
namespace RJ
export OriginalWholeDebtRJointMobiusReturnJordanSource (paJet actual_pa_member)
end RJ
namespace W
export OriginalKPairedWeakWardSource
 (nativeField first second drive correction effect sourceCharge nativeCharge lambda sigma
  power powerResponse forcing annulusForcing jumpForcing source_charge_read native_weak_system)
end W
namespace Actual
export OriginalKPairedWeakWardSource.Actual
 (sourceGamma actual_Gamma actual_receiver actual_weak_ward_source_consumer)
end Actual
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "q" => (1/4:ℝ)
local notation "h0" => OriginalKPairedBEulerJunctionSource.junctionShift
local notation "B" => burnolRieszSingleFourierSource
local notation "Eq" => burnolQuarterZeroExtension
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "b" => burnolAmbientMeanZeroFirstCorrection
local notation "d" => burnolAmbientMeanZeroSecondCorrection
local notation "X" => burnolAmbientMeanZeroPosition
local notation "Y" => burnolAmbientMeanZeroFourier
local notation "Rq" => burnolQuarterRestriction
local instance : CompleteSpace M :=
 IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete
local notation "U" => OriginalRieszSource.Response.wholeU
local notation "V" => OriginalRieszSource.Response.wholeV
local notation "Unit" => OriginalRieszFinitePairing.CoPoisson.Ward.ConstantDual.seed
local notation "A" => OriginalRieszSource.Kernel.A
local notation "beta" => OriginalRieszSource.Kernel.beta
local notation "R" => burnolDirectRightResolventCLM
variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (depth ordinal:Nat) (t:ℝ) (N:Nat)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "alpha" => P.returnCoefficient observation nontrivial half

def currentSource:BurnolL2:=
 (C.prefixCode observation nontrivial half).eval (C.environment observation nontrivial half depth)
/-- The Pa and Unit bodies come from the original generated arithmetic source. -/
def paStock (k:Nat):BurnolL2:=(Port.loop c k (Q.generatedPa c):BurnolL2)
def unitStock (k:Nat):BurnolL2:=
 ∑i∈Finset.range k,PaCoefficientSourceGram.sourceMoment c i •
  ((R c)^(k-1-i)) (burnolUnitTailResponse c 4)
def wholeStock (k:Nat):BurnolL2:=paStock observation half k+unitStock observation half k

theorem current_source_inventory :currentSource observation nontrivial half depth=
 alpha • wholeStock observation half m := by
 exact C.prefix_source observation nontrivial half depth

theorem next_source_inventory :R c (currentSource observation nontrivial half depth)=
 alpha • wholeStock observation half (m+1) := by
 rw [current_source_inventory]
 change R c (alpha • P.wholeProgramme c m)=alpha • P.wholeProgramme c (m+1)
 rw [map_smul,P.whole_programme_actual,P.whole_programme_actual,pow_succ']
 rfl

/-- Exact-order Division consumes this original prefix including its complete Unit convolution. -/
theorem current_source_physical : currentSource observation nontrivial half depth ∈
 evenBurnolClosedFace burnolUnscaledCommonGapRadius := by
 change (C.prefixCode observation nontrivial half).eval
  (C.environment observation nontrivial half depth) ∈ _
 rw [C.prefix_source observation nontrivial half depth,
  PaCoefficientSourceGramConsumer.prefix_programme_actual observation nontrivial half m]
 exact CombSource.Division.whole_pa_physical observation nontrivial half.down m le_rfl
  (RJ.paJet observation nontrivial half m) (RJ.actual_pa_member observation nontrivial half m)

theorem current_source_even : reflectL2 (currentSource observation nontrivial half depth)=
 currentSource observation nontrivial half depth :=
 mem_evenL2ClosedFace_iff.mp (current_source_physical observation nontrivial half depth).2

/-- These are both actual B columns of the next physical value on this source occurrence. -/
theorem actual_next_B_columns :
 burnolAmbientMeanZeroFirstCorrection (R c (currentSource observation nontrivial half depth))=
  G.secondNext (barC c) (fourierL2 (currentSource observation nontrivial half depth)) ∧
 burnolAmbientMeanZeroSecondCorrection (R c (currentSource observation nontrivial half depth))=
  G.firstNext (barC c) (fourierL2 (currentSource observation nontrivial half depth)) :=
 G.actual_forward_R_B c (currentSource observation nontrivial half depth)
  (current_source_even observation nontrivial half depth)

theorem actual_next_B_gap :
 burnolAmbientMeanZeroFirstCorrection (R c (currentSource observation nontrivial half depth))=
  -burnolMeanZeroTruncatedFourier (G.gapSecondNext c (currentSource observation nontrivial half depth)) ∧
 burnolAmbientMeanZeroSecondCorrection (R c (currentSource observation nontrivial half depth))=
  G.gapSecondNext c (currentSource observation nontrivial half depth) :=
 G.actual_forward_R_gap_B c (currentSource observation nontrivial half depth)
  (current_source_even observation nontrivial half depth)
  (current_source_physical observation nontrivial half depth).1.1

theorem current_source_drives :
 X (currentSource observation nontrivial half depth)=0 ∧
 Y (currentSource observation nontrivial half depth)=0 := by
 have fixed : burnolAmbientEvenPart (currentSource observation nontrivial half depth)=
  currentSource observation nontrivial half depth := by
  unfold burnolAmbientEvenPart
  rw [current_source_even]
  module
 constructor
 · apply Subtype.ext
   change burnolQuarterMeanZeroProjection (Rq (burnolAmbientEvenPart
    (currentSource observation nontrivial half depth)))=0
   rw [fixed]
   exact (burnolQuarterMeanZeroProjection_eq_zero_iff _).mpr
    (current_source_physical observation nontrivial half depth).1.1
 · apply Subtype.ext
   change burnolQuarterMeanZeroProjection (Rq (fourierL2 (burnolAmbientEvenPart
    (currentSource observation nontrivial half depth))))=0
   rw [fixed]
   exact (burnolQuarterMeanZeroProjection_eq_zero_iff _).mpr
    (current_source_physical observation nontrivial half depth).1.2

theorem current_source_B : b (currentSource observation nontrivial half depth)=0 ∧
 d (currentSource observation nontrivial half depth)=0 := by
 have drivers:=current_source_drives observation nontrivial half depth
 have first : b (currentSource observation nontrivial half depth)=0 := by
  change burnolMeanZeroBlockInverse (X (currentSource observation nontrivial half depth)-
   S (Y (currentSource observation nontrivial half depth)))=0
  rw [drivers.1,drivers.2,map_zero,sub_zero,map_zero]
 refine ⟨first,?_⟩
 change Y (currentSource observation nontrivial half depth)-S (b (currentSource observation nontrivial half depth))=0
 rw [drivers.2,first,map_zero,sub_zero]

/-- The new coefficient reads the current input's full Fourier mean and exterior tail. -/
def responseAmplitude : ℂ :=
 G.currentAmplitude (barC c) (fourierL2 (currentSource observation nontrivial half depth))

private theorem contact_zero (coordinate:BurnolCompletedMellinCoordinate) :
 OriginalKFiniteOrderRelease.QuarterSourceCommutator.contactAction coordinate 0=0 := by
 simp [OriginalKFiniteOrderRelease.QuarterSourceCommutator.contactAction,
  OriginalKFiniteOrderRelease.QuarterSourceCommutator.contactCoefficients,
  burnolQuarterMeanCoefficient,Fin.sum_univ_succ]

/-- The actual source update generates the fixed dual power columns, retaining its full coefficient. -/
theorem actual_next_B_source :
 b (R c (currentSource observation nontrivial half depth))=
  (-responseAmplitude observation nontrivial half depth) • S (W.powerResponse c) ∧
 d (R c (currentSource observation nontrivial half depth))=
  responseAmplitude observation nontrivial half depth • W.powerResponse c := by
 have second : G.gapSecondNext c (currentSource observation nontrivial half depth)=
  responseAmplitude observation nontrivial half depth • W.powerResponse c := by
  unfold G.gapSecondNext
  rw [(current_source_B observation nontrivial half depth).2,map_zero,zero_add,ZeroMemClass.coe_zero,contact_zero,map_zero,sub_zero]
  rfl
 have paid:=actual_next_B_gap observation nontrivial half depth
 rw [second,map_smul,←neg_smul] at paid
 exact paid

open private inward_even from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.QuarterSourceCommutator

theorem next_source_even : reflectL2 (R c (currentSource observation nontrivial half depth))=
 R c (currentSource observation nontrivial half depth) :=
 inward_even c (currentSource observation nontrivial half depth)
  (current_source_even observation nontrivial half depth)

theorem actual_next_drives : X (R c (currentSource observation nontrivial half depth))=0 ∧
 Y (R c (currentSource observation nontrivial half depth))=
  responseAmplitude observation nontrivial half depth • W.power c := by
 have first:=burnolMeanZeroBlock_first_equation
  (burnolAmbientMeanZeroBlockRhs (R c (currentSource observation nontrivial half depth)))
 have second:=burnolMeanZeroBlock_second_equation
  (burnolAmbientMeanZeroBlockRhs (R c (currentSource observation nontrivial half depth)))
 change b (R c (currentSource observation nontrivial half depth))+
  S (d (R c (currentSource observation nontrivial half depth)))=X (R c (currentSource observation nontrivial half depth)) at first
 change S (b (R c (currentSource observation nontrivial half depth)))+
  d (R c (currentSource observation nontrivial half depth))=Y (R c (currentSource observation nontrivial half depth)) at second
 rw [(actual_next_B_source observation nontrivial half depth).1,
  (actual_next_B_source observation nontrivial half depth).2,map_smul] at first second
 have power : W.powerResponse c-S (S (W.powerResponse c))=W.power c := by
  change (burnolMeanZeroOneMinusSquare*burnolMeanZeroBlockInverse) (W.power c)=_
  rw [burnolMeanZeroBlockInverse_right,one_apply_eq_self]
 constructor
 · linear_combination (norm:=module) -first
 · calc
    Y (R c (currentSource observation nontrivial half depth))=
     (-responseAmplitude observation nontrivial half depth) • S (S (W.powerResponse c))+
      responseAmplitude observation nontrivial half depth • W.powerResponse c := second.symm
    _=responseAmplitude observation nontrivial half depth •
     (W.powerResponse c-S (S (W.powerResponse c))) := by module
    _=responseAmplitude observation nontrivial half depth • W.power c := by rw [power]

private theorem extension_pair (state:Hq) (test:BurnolL2) :
 inner ℂ (Eq state) test=inner ℂ state (Rq test) :=
 ContinuousLinearMap.adjoint_inner_left Rq test state

private theorem zero_mean_pair (state:M) (test:Hq) :
 inner ℂ (state:Hq) test=inner ℂ state
  (OriginalRieszSource.Constructor.zeroMean test) :=
 (burnolQuarterMeanZeroClosedFace.toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_left state test).symm

/-- The actual paired actor consumes both newly generated R columns. -/
theorem actual_paired_R_query (odd:Bool) (h:ℝ) :
 inner ℂ (W.correction c odd h) (R c (currentSource observation nontrivial half depth))=
 responseAmplitude observation nontrivial half depth *
  star (inner ℂ (W.power c) (W.second c odd h)) := by
 let r:=R c (currentSource observation nontrivial half depth)
 have even : reflectL2 r=r:=next_source_even observation nontrivial half depth
 have fixed : burnolAmbientEvenPart r=r := by
  unfold burnolAmbientEvenPart
  rw [even]
  module
 have inverse : fourierL2.symm r=fourierL2 r := by
  apply fourierL2.injective
  rw [fourierL2.apply_symm_apply,fourierL2_fourierL2,even]
 have query : inner ℂ (W.correction c odd h) r=
  inner ℂ (W.first c odd h) (X r)+inner ℂ (W.second c odd h) (Y r) := by
  rw [W.correction,inner_add_left,fourierL2.inner_map_eq_flip,inverse,
   extension_pair,extension_pair,zero_mean_pair,zero_mean_pair]
  unfold burnolAmbientMeanZeroPosition burnolAmbientMeanZeroFourier
  rw [fixed]
  rfl
 change inner ℂ (W.correction c odd h) r=_
 rw [query,(actual_next_drives observation nontrivial half depth).1,
  (actual_next_drives observation nontrivial half depth).2,inner_zero_right,zero_add]
 exact (inner_smul_right (W.second c odd h) (W.power c)
  (responseAmplitude observation nontrivial half depth)).trans
  (congrArg (fun z:ℂ=>responseAmplitude observation nontrivial half depth*z)
   (inner_conj_symm (𝕜:=ℂ) (W.second c odd h) (W.power c)).symm)

private theorem actual_correction_current_zero (odd:Bool) (h:ℝ) :
 inner ℂ (W.correction c odd h) (currentSource observation nontrivial half depth)=0 :=
 burnolAmbientRawMeanZeroCorrection_inner_physical_eq_zero (W.nativeField c odd h)
  ⟨currentSource observation nontrivial half depth,current_source_physical observation nontrivial half depth⟩

/-- This value is computed from the actual paired action and the original source input. -/
def responseFunctional (odd:Bool) (h:ℝ) : ℂ :=
 inner ℂ (W.effect c odd h) (currentSource observation nontrivial half depth)

theorem actual_response_native (odd:Bool) (h:ℝ) :
 responseFunctional observation nontrivial half depth odd h=
 (-responseAmplitude observation nontrivial half depth/2)*star (W.nativeCharge c odd h) := by
 rw [responseFunctional,W.effect,inner_add_left,inner_smul_left,inner_smul_left,
  ContinuousLinearMap.adjoint_inner_left,actual_paired_R_query,actual_correction_current_zero]
 simp only [W.nativeCharge,star_mul,star_neg,star_ofNat,map_ofNat,starRingEnd_apply,mul_zero,add_zero]
 ring

theorem actual_response_source (odd:Bool) (h:ℝ) (inside:h∈Icc 0 h0) :
 responseFunctional observation nontrivial half depth odd h=
 (-responseAmplitude observation nontrivial half depth/2)*star (W.sourceCharge c odd h) := by
 rw [W.source_charge_read c odd h inside]
 exact actual_response_native observation nontrivial half depth odd h

theorem actual_response_forcing (odd:Bool) (h:ℝ) (inside:h∈Ioo 0 h0) :
 HasDerivAt (responseFunctional observation nontrivial half depth odd)
  (-star (W.lambda c)*responseFunctional observation nontrivial half depth (!odd) h-
   (responseAmplitude observation nontrivial half depth/2)*star (W.forcing c odd h)) h := by
 have paid:=(W.native_weak_system c h inside odd).star.const_mul
  (-responseAmplitude observation nontrivial half depth/2)
 have same : responseFunctional observation nontrivial half depth odd=
  fun s:ℝ=>(-responseAmplitude observation nontrivial half depth/2)*star (W.nativeCharge c odd s) :=
  funext (fun s=>actual_response_native observation nontrivial half depth odd s)
 rw [same]
 apply paid.congr_deriv
 rw [actual_response_native]
 simp only [star_add,star_mul,star_neg]
 ring

theorem actual_value_source : (C.value observation nontrivial half depth ordinal).1.1=
 R c (currentSource observation nontrivial half depth) :=
 (C.physical_R_source observation nontrivial half depth ordinal).trans
  (congrArg (R c) (C.prefix_source observation nontrivial half depth).symm)

theorem actual_value_B_source :
 b ((C.value observation nontrivial half depth ordinal).1.1)=
  (-responseAmplitude observation nontrivial half depth) • S (W.powerResponse c) ∧
 d ((C.value observation nontrivial half depth ordinal).1.1)=
  responseAmplitude observation nontrivial half depth • W.powerResponse c := by
 rw [actual_value_source]
 exact actual_next_B_source observation nontrivial half depth

theorem actual_value_paired_source (odd:Bool) (h:ℝ) (inside:h∈Icc 0 h0) :
 star (W.sigma c)*inner ℂ (W.correction c odd h) ((C.value observation nontrivial half depth ordinal).1.1)+
  2*inner ℂ (W.correction c odd h) (currentSource observation nontrivial half depth)=
 (-responseAmplitude observation nontrivial half depth/2)*star (W.sourceCharge c odd h) := by
 rw [actual_value_source]
 have same:=actual_response_source observation nontrivial half depth odd h inside
 unfold responseFunctional W.effect at same
 rw [inner_add_left,inner_smul_left,inner_smul_left,ContinuousLinearMap.adjoint_inner_left] at same
 simpa only [map_ofNat,starRingEnd_apply] using same

open private full_source_balance from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRAdjointContactSource

theorem actual_endpoint_effect : W.effect c false h0=
 OriginalWholeDebtRAdjointContactSource.sourceEffect c c := by
 rw [full_source_balance]
 rfl

include ordinal t N in
theorem actual_endpoint_receiver :
 responseFunctional observation nontrivial half depth false h0=
 star (Actual.sourceGamma observation half)*OriginalWholeDebtRJointMobiusReturnJordanSource.feedback observation nontrivial half*
 burnolAnalyticComplementExpectedPhysicalFourierRead ActualAnalyticOwner observation := by
 rw [responseFunctional,actual_endpoint_effect observation half]
 exact Actual.actual_receiver observation nontrivial half depth ordinal t N

/-- The new R columns, all paired windows and source forcing read the same whole-ledger next. -/
def actual_completed_euler_tate_consumer :=
 PProd.mk (C.sourceFace observation nontrivial half depth ordinal).rootRead <|
 PProd.mk (current_source_inventory observation nontrivial half depth) <|
 PProd.mk (next_source_inventory observation nontrivial half depth) <|
 PProd.mk (current_source_physical observation nontrivial half depth) <|
 PProd.mk (actual_next_B_columns observation nontrivial half depth) <|
 PProd.mk (actual_value_B_source observation nontrivial half depth ordinal) <|
 PProd.mk (fun odd h inside=>actual_value_paired_source observation nontrivial half depth ordinal odd h inside) <|
 PProd.mk (fun odd h inside=>actual_response_forcing observation nontrivial half depth odd h inside) <|
 PProd.mk (actual_endpoint_receiver observation nontrivial half depth ordinal t N) <|
 PProd.mk (C.same_original_next observation nontrivial half depth ordinal t N)
 (C.actual_completed_original_R observation nontrivial half depth ordinal t N)
end CountedPaInitial.CompletedPaEulerTateBoundary
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
