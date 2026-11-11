import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRNativeForcingSource
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRGapStateActionSource
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKFiniteOrderRelease.UnitPowerJordanSource OriginalKPairedBEulerJunctionSource
open OriginalWholeDebtRCorrectionActionSource OriginalWholeDebtRMixedGreenSource
open OriginalWholeDebtRNativeForcingSource
open scoped InnerProductSpace Topology
attribute [local instance 1100] NormedSpace.complexToReal
open private even_read face from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRContactSource
open private actual_outside_source nativeQuarter actual_quarters acted_even correction_outside from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRCorrectionActionSource
open private native_quarter_drive native_even quarter_pairing from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRNativeForcingSource
local notation "q" => (1/4 : ℝ)
local notation "p" => junctionPoint
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "R" => burnolDirectRightResolventCLM
local notation "C" => BandFullStockEuler.correctionRaw
local notation "G" => gapState
local notation "K" => burnolCompletedMellinRieszVector
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "Rq" => burnolQuarterRestriction
local notation "Eq" => burnolQuarterZeroExtension
local notation "Cq" => intervalConstant q
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
private def rate (c : BurnolCompletedMellinCoordinate) : ℂ := 2*c.value-1

def outerRate (c : BurnolCompletedMellinCoordinate) : ℂ := -2/(2*star c.value-1)
def gapPower (c : BurnolCompletedMellinCoordinate) : ℂ :=
  -2*(GapEuler.gapMean q c*(q : ℂ)^(1-star c.value)/(1-star c.value)+
    (1/2 : ℂ)*(q : ℂ)^(1-2*star c.value)/(2*star c.value-1))
def gapConstant (c : BurnolCompletedMellinCoordinate) : ℂ :=
  2*GapEuler.gapMean q c/(1-star c.value)-outerRate c*GapEuler.gapMean q c

/-- Complete source field: tail, quarter constant and actual power all remain in L2. -/
def adjointGapSource (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  outerRate c • G c+gapConstant c • Eq Cq+gapPower c • Eq (SingularCounting.powerL2 c)

private theorem gap_tail (c : BurnolCompletedMellinCoordinate) :
    sourceTail c (G c)=(1/2 : ℂ)*(q : ℂ)^(1-2*star c.value)/(2*star c.value-1) := by
  have paid := gapState_tail_pair (barC c) c
  change sourceTail c (G c)=(1/2 : ℂ)*(q : ℂ)^(-(star c.value+star c.value-1))/
    (star c.value+star c.value-1) at paid
  rw [show -(star c.value+star c.value-1)=1-2*star c.value by ring,
    show star c.value+star c.value-1=2*star c.value-1 by ring] at paid
  exact paid

private theorem actual_quarter (c : BurnolCompletedMellinCoordinate) :
    Rq ((R c).adjoint (G c))=Rq (adjointGapSource c) := by
  rw [sourceStep_actual]
  have source := source_quarter_step c (G c) (burnolAmbientEvenPart_even _)
  rw [gapState_restriction,map_smul,quarterStep_constant,gap_tail] at source
  unfold adjointGapSource
  rw [map_add,map_add,map_smul,map_smul,map_smul,gapState_restriction,
    burnolQuarterRestriction_zeroExtension,burnolQuarterRestriction_zeroExtension]
  rw [source]
  unfold gapConstant gapPower
  module

private theorem tail_at (c : BurnolCompletedMellinCoordinate) (x : ℝ) (outside : q<x) :
    burnolRadiusMellinTailEvaluator x (lt_trans (by norm_num) outside)
      (star c.value) (by simpa only [Complex.star_def,Complex.conj_re] using c.rightHalf) (G c)=
      (1/2 : ℂ)*(x : ℂ)^(1-2*star c.value)/(2*star c.value-1) := by
  rw [burnolRadiusMellinTailEvaluator_eq_integral]
  have source : (∫ t : ℝ in Ioi x,(t : ℂ)^(-star c.value)*G c t)=
      (1/2 : ℂ)*(∫ t : ℝ in Ioi x,(t : ℂ)^(-star c.value-star c.value)) := by
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (s := Ioi x) (gapState_read c),ae_restrict_mem measurableSet_Ioi]
      with t raw after
    rw [raw,gapState_raw_tail c (outside.trans after)]
    have tn : (t : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (lt_trans (by norm_num) (outside.trans after)).ne'
    rw [show -star c.value-star c.value=(-star c.value)+(-star c.value) by ring,
      Complex.cpow_add _ _ tn]
    ring
  rw [source,integral_Ioi_cpow_of_lt (by
    simp only [sub_re,neg_re,Complex.star_def,Complex.conj_re]
    linarith [c.rightHalf]) (lt_trans (by norm_num) outside)]
  rw [show -star c.value-star c.value+1=1-2*star c.value by ring]
  have denominator : 1-2*star c.value= -(2*star c.value-1) := by ring
  rw [denominator,neg_div_neg_eq]
  ring

private theorem actual_outer (c : BurnolCompletedMellinCoordinate) :
    ∀ᵐ x : ℝ ∂volume,q<x → ((R c).adjoint (G c)) x=adjointGapSource c x := by
  have paid := sourceVolterraResolvent_positive_profile (barC c) (G c)
  change ∀ᵐ x : ℝ ∂volume,∀ positive : 0<x, sourceStep c (G c) x=
    -2*(x : ℂ)^(star c.value-1)*burnolRadiusMellinTailEvaluator x positive (star c.value)
      (by simpa only [Complex.star_def,Complex.conj_re] using c.rightHalf) (G c) at paid
  rw [←sourceStep_actual c (G c)] at paid
  filter_upwards [paid,gapState_read c,
    Lp.coeFn_add (outerRate c • G c+gapConstant c • Eq Cq) (gapPower c • Eq (SingularCounting.powerL2 c)),
    Lp.coeFn_add (outerRate c • G c) (gapConstant c • Eq Cq),
    Lp.coeFn_smul (outerRate c) (G c),Lp.coeFn_smul (gapConstant c) (Eq Cq),
    Lp.coeFn_smul (gapPower c) (Eq (SingularCounting.powerL2 c)),
    burnolQuarterZeroExtension_coe Cq,burnolQuarterZeroExtension_coe (SingularCounting.powerL2 c)]
    with x profile raw whole sum a b t one power outside
  have pos : 0<x := lt_trans (by norm_num) outside
  have xn : (x : ℂ)≠0 := Complex.ofReal_ne_zero.mpr pos.ne'
  have notmem : x∉symmetricInterval q := fun member => outside.not_ge member.2
  rw [profile pos]
  change -2*(x : ℂ)^(star c.value-1)*burnolRadiusMellinTailEvaluator x pos
    (star c.value) (by simpa only [Complex.star_def,Complex.conj_re] using c.rightHalf) (G c)=_
  rw [tail_at c x outside]
  change _=(outerRate c • G c+gapConstant c • Eq Cq+gapPower c • Eq (SingularCounting.powerL2 c)) x
  rw [whole]
  change _=(outerRate c • G c+gapConstant c • Eq Cq) x+(gapPower c • Eq (SingularCounting.powerL2 c)) x
  rw [sum]
  change _=(outerRate c • G c) x+(gapConstant c • Eq Cq) x+(gapPower c • Eq (SingularCounting.powerL2 c)) x
  rw [a,b,t,Pi.smul_apply,Pi.smul_apply,Pi.smul_apply,smul_eq_mul,one,power,
    indicator_of_notMem notmem,indicator_of_notMem notmem,raw,gapState_raw_tail c outside]
  have product : (x : ℂ)^(star c.value-1)*(x : ℂ)^(1-2*star c.value)=(x : ℂ)^(-star c.value) := by
    rw [←Complex.cpow_add _ _ xn]
    congr 1
    ring
  rw [←mul_assoc,show (-2 : ℂ)*(x : ℂ)^(star c.value-1)*
    ((1/2 : ℂ)*(x : ℂ)^(1-2*star c.value)/(2*star c.value-1))=
      -1*((x : ℂ)^(star c.value-1)*(x : ℂ)^(1-2*star c.value))/(2*star c.value-1) by ring,product]
  unfold outerRate
  ring

/-- The final source calculation must identify the complete actual adjoint, not a supplied price. -/
theorem actual_adjoint_gap (c : BurnolCompletedMellinCoordinate) :
    (R c).adjoint (G c)=adjointGapSource c := by
  have innerSource := actual_quarter c
  have outerSource := actual_outer c
  have gapEven : reflectL2 (G c)=G c := burnolAmbientEvenPart_even _
  have leftEven : reflectL2 ((R c).adjoint (G c))=(R c).adjoint (G c) := by
    rw [sourceStep_actual]
    change reflectL2 (sourceVolterraResolvent (barC c) (G c))=sourceVolterraResolvent (barC c) (G c)
    rw [sourceVolterraResolvent_reflect,gapEven]
  have unitEven : reflectL2 (Eq Cq)=Eq Cq := by
    change reflectL2 (burnolRadiusZeroExtension q Cq)=burnolRadiusZeroExtension q Cq
    rw [burnolRadiusZeroExtension_reflect,reflectRestricted_intervalConstant]
  have powerEven : reflectL2 (Eq (SingularCounting.powerL2 c))=Eq (SingularCounting.powerL2 c) := by
    change reflectL2 (burnolRadiusZeroExtension q (SingularCounting.powerL2 c))=_
    rw [burnolRadiusZeroExtension_reflect]
    have paid := dividedLogColumn_even c 0
    change reflectRestricted q (SingularCounting.powerL2 c)=SingularCounting.powerL2 c at paid
    rw [paid]
    rfl
  have rightEven : reflectL2 (adjointGapSource c)=adjointGapSource c := by
    unfold adjointGapSource
    rw [map_add,map_add,map_smul,map_smul,map_smul,gapEven,unitEven,powerEven]
  have leftRead := LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) ((R c).adjoint (G c))
  have rightRead := LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) (adjointGapSource c)
  change (Rq ((R c).adjoint (G c)) : ℝ → ℂ)=ᵐ[volume.restrict (symmetricInterval q)] _ at leftRead
  change (Rq (adjointGapSource c) : ℝ → ℂ)=ᵐ[volume.restrict (symmetricInterval q)] _ at rightRead
  rw [innerSource] at leftRead
  have inside := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp (leftRead.symm.trans rightRead)
  have positive : ∀ᵐ x : ℝ ∂volume,0<x → ((R c).adjoint (G c)) x=adjointGapSource c x := by
    filter_upwards [inside,outerSource] with x inner outer pos
    by_cases small : x≤q
    · exact inner ⟨by linarith,small⟩
    · exact outer (lt_of_not_ge small)
  have evenDifference : reflectL2 ((R c).adjoint (G c)-adjointGapSource c)=
      (R c).adjoint (G c)-adjointGapSource c := by rw [map_sub,leftEven,rightEven]
  have difference := even_read ((R c).adjoint (G c)-adjointGapSource c) (fun _ => 0)
    evenDifference (fun _ => rfl) (by
      filter_upwards [positive,Lp.coeFn_sub ((R c).adjoint (G c)) (adjointGapSource c)] with x same diff pos
      rw [diff,Pi.sub_apply,same pos,sub_self])
  apply Lp.ext
  filter_upwards [difference,Lp.coeFn_sub ((R c).adjoint (G c)) (adjointGapSource c)] with x zero diff
  rw [diff,Pi.sub_apply] at zero
  exact sub_eq_zero.mp zero

theorem actual_physical_pair (c : BurnolCompletedMellinCoordinate) :
    inner ℂ (K c : BurnolL2) (R c (C c))=(-2*nativeAlpha c)*inner ℂ (K c : BurnolL2) (K (barC c) : BurnolL2) := by
  have orthogonal : inner ℂ (K c : BurnolL2) (nativeOutside c)=0 := by
    rw [←actual_outside_source]
    have mem : OriginalKCombPhysicalAction.physicalRemainder (R c (C c))∈
        (evenBurnolClosedFace q).toSubmoduleᗮ := Submodule.starProjection_apply_mem _ _
    exact (Submodule.mem_orthogonal _ _).mp mem _ (K c).property
  rw [actual_correction_action,inner_add_right,inner_smul_right,orthogonal,add_zero]

private def forcingB (c : BurnolCompletedMellinCoordinate) : M :=
  burnolRieszSingleFourierSource c-S (S (burnolRieszSingleFourierSource c))

private theorem source_correction_C (c : BurnolCompletedMellinCoordinate) :
    inner ℂ (OriginalRieszSourceGreen.sourceCorrection c) (C c)=inner ℂ (forcingB c) (sourceSecond c) := by
  have crossed : inner ℂ (fourierL2 (Eq (burnolRieszSingleFourierSource c : Hq)))
      (Eq (sourceFirst c : Hq))=inner ℂ (S (burnolRieszSingleFourierSource c)) (sourceFirst c) := by
    rw [←inner_conj_symm,extension_fourier_pairing,inner_conj_symm]
  have moved := meanZero_fourier_pairing_of_reflection (S (burnolRieszSingleFourierSource c))
    (sourceSecond c) (source_correction_even c 1)
  unfold OriginalRieszSourceGreen.sourceCorrection BandFullStockEuler.correctionRaw
  rw [inner_sub_left,inner_add_right,inner_add_right,crossed,fourierL2.inner_map_map,
    quarter_extension_inner,quarter_extension_inner,extension_fourier_pairing]
  change inner ℂ (S (burnolRieszSingleFourierSource c)) (sourceFirst c)+
    inner ℂ (burnolRieszSingleFourierSource c) (sourceSecond c)-
    (inner ℂ (S (burnolRieszSingleFourierSource c)) (sourceFirst c)+
      inner ℂ (S (burnolRieszSingleFourierSource c)) (S (sourceSecond c)))=_
  unfold forcingB
  rw [inner_sub_left]
  linear_combination moved

private theorem kernel_C_zero (c : BurnolCompletedMellinCoordinate) :
    inner ℂ (K c : BurnolL2) (C c)=0 := by
  have mem : C c∈(evenBurnolClosedFace q).toSubmoduleᗮ := by
    rw [←correction_outside]
    exact Submodule.starProjection_apply_mem _ _
  exact (Submodule.mem_orthogonal _ _).mp mem _ (K c).property

private theorem gap_C_price (c : BurnolCompletedMellinCoordinate) :
    inner ℂ (G c) (C c)=inner ℂ (forcingB c) (sourceSecond c) := by
  rw [gapState_eq_kernel_add_correction,inner_add_left,kernel_C_zero,zero_add,source_correction_C]

private theorem extension_C_price (c : BurnolCompletedMellinCoordinate) (value : Hq) :
    inner ℂ (Eq value) (C c)=inner ℂ value (sourceFirst c : Hq)+
      inner ℂ (burnolTruncatedFourier value) (sourceSecond c : Hq) := by
  unfold BandFullStockEuler.correctionRaw
  rw [inner_add_right,quarter_extension_inner]
  have paid := ContinuousLinearMap.adjoint_inner_left Rq
    (fourierL2 (Eq (sourceSecond c : Hq))) value
  change inner ℂ (Eq value) (fourierL2 (Eq (sourceSecond c : Hq)))=
    inner ℂ value (burnolTruncatedFourier (sourceSecond c : Hq)) at paid
  rw [paid,←OriginalRieszSourceGreen.quarter_fourier_pairing_of_reflection value
    (sourceSecond c : Hq) (source_correction_even c 1)]

private theorem constant_first (c : BurnolCompletedMellinCoordinate) :
    inner ℂ Cq (sourceFirst c : Hq)=0 :=
  (Submodule.mem_orthogonal _ _).mp (sourceFirst c).property _ (Submodule.mem_span_singleton_self _)

private theorem power_first (c : BurnolCompletedMellinCoordinate) :
    inner ℂ (SingularCounting.powerL2 c) (sourceFirst c : Hq)=nativeAlpha c := by
  change _=inner ℂ (Constructor.zeroMean (SingularCounting.powerL2 c)) (sourceFirst c)
  unfold Constructor.zeroMean
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]

def gapActionPrice (c : BurnolCompletedMellinCoordinate) : ℂ :=
  star (outerRate c)*inner ℂ (forcingB c) (sourceSecond c)+
    star (gapConstant c)*inner ℂ (burnolTruncatedFourier Cq) (sourceSecond c : Hq)+
      star (gapPower c)*(nativeAlpha c+
        inner ℂ (burnolTruncatedFourier (SingularCounting.powerL2 c)) (sourceSecond c : Hq))

/-- The complete adjoint field is consumed on both actual C legs, including the Fourier-unit fee. -/
theorem actual_gap_action (c : BurnolCompletedMellinCoordinate) :
    inner ℂ (G c) (R c (C c))=gapActionPrice c := by
  rw [←ContinuousLinearMap.adjoint_inner_left,actual_adjoint_gap]
  unfold adjointGapSource
  rw [inner_add_left,inner_add_left,inner_smul_left,inner_smul_left,inner_smul_left,
    gap_C_price,extension_C_price,extension_C_price,constant_first,power_first,zero_add]
  rfl

private theorem source_correction_H (c : BurnolCompletedMellinCoordinate) :
    inner ℂ (OriginalRieszSourceGreen.sourceCorrection c) (R c (C c))=
      inner ℂ (forcingB c) (nativeFoot c 1) := by
  have even := acted_even c 0
  change reflectL2 (R c (C c))=R c (C c) at even
  have twice : fourierL2 (fourierL2 (R c (C c)))=R c (C c) := by
    rw [fourierL2_fourierL2,even]
  have pairing := fourierL2.inner_map_map (Eq (burnolRieszSingleFourierSource c : Hq))
    (fourierL2 (R c (C c)))
  rw [twice] at pairing
  have quarter (value : M) (i : Fin 2) :
      inner ℂ (Eq (value : Hq)) (face i (R c (C c)))=
        inner ℂ value (nativeDrive c i) := by
    calc
      _=inner ℂ (value : Hq) (Rq (face i (R c (C c)))) :=
        ContinuousLinearMap.adjoint_inner_left Rq (face i (R c (C c))) (value : Hq)
      _=_ := by rw [actual_quarters,quarter_pairing]
  unfold OriginalRieszSourceGreen.sourceCorrection
  rw [inner_sub_left,pairing]
  change inner ℂ (Eq (burnolRieszSingleFourierSource c : Hq)) (face 1 (R c (C c)))-
    inner ℂ (Eq (S (burnolRieszSingleFourierSource c) : Hq)) (face 0 (R c (C c)))=_
  rw [quarter _ 1,quarter _ 0]
  change inner ℂ (burnolRieszSingleFourierSource c) (nativeFoot c 1+S (nativeFoot c 0))-
    inner ℂ (S (burnolRieszSingleFourierSource c)) (nativeFoot c 0+S (nativeFoot c 1))=_
  simp only [inner_add_right]
  have first := meanZero_fourier_pairing_of_reflection (burnolRieszSingleFourierSource c)
    (nativeFoot c 0) (native_even c 0)
  have second := meanZero_fourier_pairing_of_reflection (S (burnolRieszSingleFourierSource c))
    (nativeFoot c 1) (native_even c 1)
  unfold forcingB
  rw [inner_sub_left]
  linear_combination -first+second

def sourceMass (c : BurnolCompletedMellinCoordinate) : ℂ :=
  (∫ x : ℝ in p..q,mixedMass c x)+(1/2 : ℂ)*
    (gapActionPrice c-inner ℂ (forcingB c) (nativeFoot c 1))

/-- The actual old finite price consumes the full native adjoint action and its source correction. -/
theorem actual_finite_price_source (c : BurnolCompletedMellinCoordinate) :
    finitePrice c=2*(nativePFlux c-(∫ x : ℝ in 0..p,innerForcing c x)-rate c*sourceMass c)-
      4*(meanCharge c 0*(∫ x : ℝ in p..q,star (sourceProfile c 0 x))+
        meanCharge c 1*(∫ x : ℝ in p..q,star (sourceProfile c 1 x))) := by
  have gram := original_kernel_gram c (barC c)
  have physical := actual_physical_pair c
  have action := actual_gap_action c
  have source := gapState_eq_kernel_add_correction c
  change (c.value+star (star c.value)-1)*inner ℂ (K c : BurnolL2) (K (barC c) : BurnolL2)=
    (1/2 : ℂ)*(star (Kernel.A c)*Kernel.A (barC c)-star (Kernel.beta c)*Kernel.beta (barC c)) at gram
  rw [star_star] at gram
  have generated : star (Kernel.A c)*Kernel.A (barC c)-star (Kernel.beta c)*Kernel.beta (barC c)=
      2*(2*c.value-1)*inner ℂ (K c : BurnolL2) (K (barC c) : BurnolL2) := by
    linear_combination -2*gram
  unfold finitePrice sourceMass rate
  rw [←action,←source_correction_H,source,inner_add_left,physical]
  rw [generated]
  ring

theorem actual_fixed_residual_source (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value=0) :
    -burnolPaFixedShiftResidual c zero=
      (pairedMellinTranslationCharacter c.value junctionShift-
        pairedMellinTranslationCharacter (star c.value) junctionShift)*OriginalRieszFinitePairing.kernelSelfSource c+
      (1/2 : ℂ)*star (2*(nativePFlux c-(∫ x : ℝ in 0..p,innerForcing c x)-rate c*sourceMass c)-
        4*(meanCharge c 0*(∫ x : ℝ in p..q,star (sourceProfile c 0 x))+
          meanCharge c 1*(∫ x : ℝ in p..q,star (sourceProfile c 1 x)))) := by
  rw [OriginalWholeDebtRNativeForcingSource.actual_fixed_residual,actual_finite_price_source]

end OriginalWholeDebtRGapStateActionSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
