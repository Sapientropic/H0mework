import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.PaSpectralSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.UnweightedCayleySource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPhysicalPricing
import H0mework.Versions.R7e4da746.Arithmetic.RiemannBandResponse.Source.Division.Whole

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease
open Complex MeasureTheory Set Filter Function BurnolPhysicalState
open NoIslandNoMagic.CanonicalRiemann
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open OriginalKCrossParameterRAdjointSource.PaSpectralSource
open OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
open OriginalKCrossParameterRAdjointSource.UnweightedCayleySource
open OriginalKDirectRCofinalOutsideVolterraSource
open OriginalKSourceResolventReconstruction
open scoped InnerProductSpace Topology
local notation "q" => burnolUnscaledCommonGapRadius
local notation "F" => evenFaceFourierEquiv q
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder
local instance releasePhysicalComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace q).isClosed.isComplete

-- The paid pulse keeps the original source and its wave in the same annulus.
elab "paidStepPulse" : term => do
  let head := ("_private.H0mework.Versions.R7e4da746.Arithmetic.RiemannUnitShell.StepClosedRange".splitOn ".").foldl Lean.Name.str Lean.Name.anonymous
  let tail := ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.burnolReciprocalStepAnnulus_pulse_exists".splitOn ".").foldl Lean.Name.str (Lean.Name.num head 0)
  return Lean.mkConst tail

private theorem step_source_recovery (lower upper : ℝ) (lowerStrict : (1/4:ℝ)<lower)
    (ordered : lower≤upper) (upperStrict : upper<4) :
    burnolMobiusSourceL2 (burnolReciprocalStepPhysicalState lower upper lowerStrict ordered upperStrict.le)=
      burnolReciprocalStepSourceL2 lower upper (lt_trans (by norm_num) lowerStrict) ordered := by
  let wave := burnolReciprocalStepPhysicalState lower upper lowerStrict ordered upperStrict.le
  let seed := burnolReciprocalStepSourceL2 lower upper (lt_trans (by norm_num) lowerStrict) ordered
  let recover := burnolMobiusSourceL2.comp burnolEvenAmbientProjection
  have dilationZero (v : BurnolL2) : burnolMultiplicativeDilation 0 v=v := by
    simp only [burnolMultiplicativeDilation_zero]
  apply eq_of_dist_eq_zero
  apply le_antisymm _ dist_nonneg
  apply le_of_forall_pos_le_add
  intro ε εpos
  let tolerance := ε/(2*(‖recover‖+1))
  have tolpos : 0<tolerance := by dsimp [tolerance]; positivity
  obtain ⟨δ₁,δ₁pos,closeWave⟩ := Metric.continuousAt_iff.mp
    (burnolMultiplicativeDilation_stronglyContinuous (wave:BurnolL2)).continuousAt tolerance tolpos
  obtain ⟨δ₂,δ₂pos,closeSeed⟩ := Metric.continuousAt_iff.mp
    (burnolMultiplicativeDilation_stronglyContinuous seed).continuousAt (ε/2) (by positivity)
  obtain ⟨pulse,small,innerMargin,outerMargin⟩ := paidStepPulse lower upper (min δ₁ δ₂)
    lowerStrict ordered upperStrict (lt_min δ₁pos δ₂pos)
  have waveClose : dist (burnolReciprocalStepSmoothedValue pulse (wave:BurnolL2)) (wave:BurnolL2)≤tolerance := by
    have generated := pulse.dist_normed_convolution_le (μ := (volume:Measure ℝ))
      (burnolMultiplicativeDilation_stronglyContinuous (wave:BurnolL2)).aestronglyMeasurable
      (x₀ := (0:ℝ)) (ε := tolerance) (fun h inside =>
        (closeWave ((Metric.mem_ball.mp inside).trans (small.trans_le (min_le_left _ _)))).le)
    simpa only [burnolReciprocalStepSmoothedValue,dilationZero] using generated
  have seedClose : dist (burnolReciprocalStepSmoothedValue pulse seed) seed≤ε/2 := by
    have generated := pulse.dist_normed_convolution_le (μ := (volume:Measure ℝ))
      (burnolMultiplicativeDilation_stronglyContinuous seed).aestronglyMeasurable
      (x₀ := (0:ℝ)) (ε := ε/2) (fun h inside =>
        (closeSeed ((Metric.mem_ball.mp inside).trans (small.trans_le (min_le_right _ _)))).le)
    simpa only [burnolReciprocalStepSmoothedValue,dilationZero] using generated
  let smooth := burnolReciprocalStepAnnulusSmoothedSource pulse lower upper innerMargin outerMargin
  let compact := burnolCompactTateReciprocalSource smooth
  have seedRead : burnolMobiusSourceL2 (burnolCompactAdditivePhysicalState compact)=
      (burnolReciprocalStepSmoothedSource pulse lower upper).toLp 2 volume := by
    apply Lp.ext
    filter_upwards [burnolMobiusSourceExtension_compact_coeFn compact,
      (burnolReciprocalStepSmoothedSource pulse lower upper).coeFn_toLp 2 volume] with x hx hs
    change burnolMobiusSourceL2 (burnolCompactAdditivePhysicalState compact) x=burnolCompactAdditiveSource compact x at hx
    rw [hx,hs]
    exact burnolCompactTateReciprocalSource_additiveSource smooth x
  have smoothRecovery : recover (burnolReciprocalStepSmoothedValue pulse (wave:BurnolL2))=
      burnolReciprocalStepSmoothedValue pulse seed := by
    have generated := burnolReciprocalStepSmoothedValue_generator pulse lower upper
      (lt_trans (by norm_num) lowerStrict) ordered upperStrict.le innerMargin outerMargin
    change recover (burnolReciprocalStepSmoothedValue pulse (burnolReciprocalStepWaveL2 lower upper (lt_trans (by norm_num) lowerStrict) ordered))=_
    rw [generated]
    change burnolMobiusSourceL2 (burnolEvenAmbientProjection (burnolCompactAdditivePhysicalState compact:BurnolL2))=_
    have fixed : burnolEvenAmbientProjection (burnolCompactAdditivePhysicalState compact:BurnolL2)=
        burnolCompactAdditivePhysicalState compact :=
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
    rw [fixed,seedRead,burnolReciprocalStepSmoothedSource_toLp]
  have recoveryRead : recover (wave:BurnolL2)=burnolMobiusSourceL2 wave := by
    change burnolMobiusSourceL2 (burnolEvenAmbientProjection (wave:BurnolL2))=_
    have fixed : burnolEvenAmbientProjection (wave:BurnolL2)=wave :=
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self wave
    rw [fixed]
  have firstBound : dist (recover (wave:BurnolL2))
      (recover (burnolReciprocalStepSmoothedValue pulse (wave:BurnolL2)))≤‖recover‖*tolerance := by
    have native : dist (recover (wave:BurnolL2))
        (recover (burnolReciprocalStepSmoothedValue pulse (wave:BurnolL2)))≤
        ‖recover‖*dist (wave:BurnolL2) (burnolReciprocalStepSmoothedValue pulse (wave:BurnolL2)) :=
      recover.lipschitz.dist_le_mul _ _
    exact native.trans (mul_le_mul_of_nonneg_left (by simpa only [dist_comm] using waveClose) (norm_nonneg _))
  calc
    dist (burnolMobiusSourceL2 wave) seed = dist (recover (wave:BurnolL2)) seed := by rw [recoveryRead]
    _ ≤ dist (recover (wave:BurnolL2)) (recover (burnolReciprocalStepSmoothedValue pulse (wave:BurnolL2)))+
        dist (recover (burnolReciprocalStepSmoothedValue pulse (wave:BurnolL2))) seed := dist_triangle _ _ _
    _ ≤ ‖recover‖*tolerance+ε/2 := by
      exact add_le_add firstBound (by rw [smoothRecovery];exact seedClose)
    _ ≤ 0+ε := by
      have positive : 0<2*(‖recover‖+1) := by positivity
      have paid : 2*(‖recover‖+1)*tolerance=ε := by
        dsimp only [tolerance]
        exact mul_div_cancel₀ ε (ne_of_gt positive)
      nlinarith

private theorem step_source_coefficient (coordinate : BurnolCompletedMellinCoordinate)
    (lower upper : ℝ) (lowerStrict : (1/4:ℝ)<lower) (ordered : lower≤upper) (upperStrict : upper<4) :
    burnolPaResolventSourceCoefficient coordinate
      (burnolReciprocalStepPhysicalState lower upper lowerStrict ordered upperStrict.le)=
      2*∫x:ℝ in lower..upper,(x:ℂ)^(-coordinate.value) := by
  change 2*burnolMellinTailEvaluator coordinate.value coordinate.rightHalf
    (burnolTateReciprocalL2 (burnolMobiusSourceL2 _))=_
  rw [step_source_recovery lower upper lowerStrict ordered upperStrict, burnolMellinTailEvaluator_eq_integral]
  congr 1
  rw [intervalIntegral.integral_of_le ordered, ←integral_Ico_eq_integral_Ioc]
  rw [←integral_indicator measurableSet_Ioi,←integral_indicator measurableSet_Ico]
  apply integral_congr_ae
  filter_upwards [burnolReciprocalStepSource_tate_raw lower upper (lt_trans (by norm_num) lowerStrict) ordered] with x hx
  by_cases gap : q<x
  · rw [indicator_of_mem (show x∈Ioi q from gap),hx]
    have positive : 0<x := lt_trans (by norm_num [burnolUnscaledCommonGapRadius]) gap
    simp only [abs_of_pos positive,mem_Ico,indicator_apply]
    split_ifs <;> simp
  · have outside : x∉Ico lower upper := by
      intro active
      exact gap (lt_of_lt_of_le (by simpa only [burnolUnscaledCommonGapRadius] using lowerStrict) active.1)
    rw [indicator_of_notMem (show x∉Ioi q from gap),indicator_of_notMem outside]

def actor {owner : GlobalGermOwner} (observation : GeneratedRiemannZeroObservationAt owner)
    (rightHalf : 1/2<observation.coordinate.re) (n k:Nat) : BurnolL2 :=
  CombSource.Division.rawIterate observation rightHalf k (burnolPaCombApproximation n:BurnolL2)

theorem actor_physical {owner : GlobalGermOwner} (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬∃n:Nat,observation.coordinate=-2*(n+1))
    (rightHalf : 1/2<observation.coordinate.re) (n k:Nat)
    (atMost : k≤generatedRiemannXiZeroOrder owner observation.coordinate) :
    actor observation rightHalf n k∈evenBurnolClosedFace q :=
  CombSource.Division.actual_comb_physical observation nontrivial rightHalf n k atMost

theorem actor_succ {owner : GlobalGermOwner} (observation : GeneratedRiemannZeroObservationAt owner)
    (rightHalf : 1/2<observation.coordinate.re) (n k:Nat) :
    actor observation rightHalf n (k+1)=burnolDirectRightResolvent (observation.coordinate/2) (actor observation rightHalf n k) := by
  simp only [actor,CombSource.Division.rawIterate,pow_succ',mul_apply_eq_comp,CombSource.Division.rawAction]
  rfl

private theorem actual_comb_heat_factor (n:Nat) (w:ℂ) (right:1/4<w.re) (below:w.re<1/2) :
    burnolDivisionNormalizedPhysicalHeatMellin (burnolPaCombApproximation n) w=
      2*riemannZeta (2*w)*burnolPaCombResponseCoefficient (1-2*w) n := by
  let coordinate := burnolDivisionCompletedMellinCoordinate w right below
  let upper := 1+burnolPaCombSourceWidth n
  let wave := burnolReciprocalStepPhysicalState 1 upper (by norm_num)
    (by dsimp [upper]; linarith [(burnolPaCombSourceWidth_bounds n).1])
    (by dsimp [upper]; linarith [(burnolPaCombSourceWidth_bounds n).2])
  have source := allPa_fourier_source_read coordinate wave (burnolReciprocalStepWave_memPa 1 upper (by norm_num) _ (by
    dsimp [upper]; linarith [(burnolPaCombSourceWidth_bounds n).2]))
  rw [step_source_coefficient coordinate 1 upper (by norm_num)
    (by dsimp [upper];linarith [(burnolPaCombSourceWidth_bounds n).1])
    (by dsimp [upper];linarith [(burnolPaCombSourceWidth_bounds n).2])] at source
  have actual : (burnolPaCombApproximation n)=((n:ℂ)+2) • F wave := by rfl
  have gamma := burnolGenericHomogeneousGammaMellinBridge (burnolPaCombApproximation n) coordinate
  have gammaNe : Gammaℝ (2*w)≠0 := Gammaℝ_ne_zero_of_re_pos (by simp only [mul_re];norm_num;linarith)
  have heat : burnolDivisionNormalizedPhysicalHeatMellin (burnolPaCombApproximation n) w=
      2*burnolCompletedMellinEvaluator coordinate (burnolPaCombApproximation n) := by
    unfold burnolDivisionNormalizedPhysicalHeatMellin
    rw [burnolDivisionCompletedMellinCoordinate_value,show (2*w)/2=w by ring] at gamma
    change Gammaℝ (2*w)*burnolCompletedMellinEvaluator coordinate (burnolPaCombApproximation n)=
      (1/2:ℂ)*mellin (burnolGenericGaussianHeatPairTotal (burnolPaCombApproximation n:BurnolL2)) w at gamma
    field_simp [gammaNe]
    linear_combination -2*gamma
  rw [heat,actual,map_smul,smul_eq_mul,←burnolCompletedMellinRieszVector_readback]
  have moved := (evenFaceFourierEquiv q).inner_map_map (burnolCompletedMellinRieszVector coordinate) (F wave)
  have invol : F (F wave)=wave := evenFaceFourier_involutive q wave
  rw [invol] at moved
  rw [←moved,source]
  have integralPower := integral_cpow (a:=(1:ℝ)) (b:=upper) (r:=-coordinate.value)
    (Or.inr ⟨by intro zero;have same:=congrArg Complex.re zero;dsimp [coordinate] at same;norm_num at same;linarith,
      by rw [uIcc_of_le (by dsimp [upper];linarith [(burnolPaCombSourceWidth_bounds n).1])];norm_num⟩)
  rw [integralPower]
  dsimp only [coordinate,burnolDivisionCompletedMellinCoordinate,upper]
  unfold burnolPaCombResponseCoefficient
  simp only [Complex.ofReal_one,Complex.one_cpow]
  have expPower : ((1+burnolPaCombSourceWidth n:ℝ):ℂ)^(1-2*w)=
      Complex.exp ((1-2*w)*(Real.log (1+burnolPaCombSourceWidth n):ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (by linarith [(burnolPaCombSourceWidth_bounds n).1])),
      ←Complex.ofReal_log (by linarith [(burnolPaCombSourceWidth_bounds n).1])]
    congr 1;ring
  rw [show -(2*w)+1=1-2*w by ring,expPower]
  ring


private theorem coefficient_analytic (n:Nat) :
    AnalyticOnNhd ℂ (fun w:ℂ => burnolPaCombResponseCoefficient (1-2*w) n)
      burnolPhysicalHeatMellinStrip := by
  apply DifferentiableOn.analyticOnNhd
  · intro w hw
    have nonzero : 1-2*w≠0 := by
      apply ne_of_apply_ne Complex.re
      simp only [sub_re,one_re,mul_re,zero_re]
      norm_num
      linarith [hw.2]
    apply DifferentiableAt.differentiableWithinAt
    unfold burnolPaCombResponseCoefficient
    fun_prop (disch := exact nonzero)
  · exact burnolPhysicalHeatMellinStrip_isOpen

private theorem heat_factor_analytic (n:Nat) :
    AnalyticOnNhd ℂ (fun w:ℂ => 2*riemannZeta (2*w)*burnolPaCombResponseCoefficient (1-2*w) n)
      burnolPhysicalHeatMellinStrip := by
  apply DifferentiableOn.analyticOnNhd
  · intro w hw
    have nonone : 2*w≠1 := by
      apply ne_of_apply_ne Complex.re
      simp only [mul_re,one_re]
      norm_num
      linarith [hw.2]
    have zeta := (differentiableAt_riemannZeta nonone).comp w
      ((differentiableAt_const (2:ℂ)).mul differentiableAt_id)
    exact ((differentiableAt_const (2:ℂ)).mul zeta |>.mul
      (coefficient_analytic n w hw).differentiableAt).differentiableWithinAt
  · exact burnolPhysicalHeatMellinStrip_isOpen

/-- Equality of the original actor germ; bounded tail was used only on the right substrip. -/
theorem actual_comb_heat_germ (n:Nat) :
    EqOn (burnolDivisionNormalizedPhysicalHeatMellin (burnolPaCombApproximation n))
      (fun w:ℂ => 2*riemannZeta (2*w)*burnolPaCombResponseCoefficient (1-2*w) n)
      burnolPhysicalHeatMellinStrip := by
  have eventuallyEqual : burnolDivisionNormalizedPhysicalHeatMellin (burnolPaCombApproximation n)=ᶠ[𝓝 (3/8:ℂ)]
      (fun w:ℂ => 2*riemannZeta (2*w)*burnolPaCombResponseCoefficient (1-2*w) n) := by
    have rightNhd : {w:ℂ | 1/4<w.re}∈𝓝 (3/8:ℂ) :=
      (isOpen_Ioi.preimage Complex.continuous_re).mem_nhds (by norm_num)
    have belowNhd : {w:ℂ | w.re<1/2}∈𝓝 (3/8:ℂ) :=
      (isOpen_Iio.preimage Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [rightNhd,belowNhd] with w wr wb
    exact actual_comb_heat_factor n w wr wb
  exact (burnolDivisionNormalizedPhysicalHeatMellin_analyticOn _).eqOn_of_preconnected_of_eventuallyEq
    (heat_factor_analytic n) burnolPhysicalHeatMellinStrip_isConnected.isPreconnected
    (by constructor <;> norm_num) eventuallyEqual

elab "paidBareDifferentiable" : term => do
  let head := ("_private.H0mework.Versions.R7e4da746.Arithmetic.RiemannDivision.AnalyticComplementDivisionJet".splitOn ".").foldl Lean.Name.str Lean.Name.anonymous
  let tail := ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.divisionJet_differentiableAt_generatedRiemannBareZeroLocalizedSpectrum".splitOn ".").foldl Lean.Name.str (Lean.Name.num head 0)
  return Lean.mkConst tail

private def actorQuotient {owner : GlobalGermOwner} (observation : GeneratedRiemannZeroObservationAt owner)
    (n:Nat) (w:ℂ) :ℂ :=
  2*(2:ℂ)^generatedRiemannXiZeroOrder owner observation.coordinate*
    generatedRiemannBareZeroLocalizedSpectrum owner (1-observation.coordinate) (2*w)*
      burnolPaCombResponseCoefficient (1-2*w) n

private theorem actor_quotient_analytic {owner : GlobalGermOwner} (observation : GeneratedRiemannZeroObservationAt owner) (n:Nat) :
    AnalyticOnNhd ℂ (actorQuotient observation n) burnolPhysicalHeatMellinStrip := by
  apply DifferentiableOn.analyticOnNhd
  · intro w hw
    have positive : 0<(2*w).re := by simp only [mul_re];norm_num;linarith [hw.1]
    have below : (2*w).re<1 := by simp only [mul_re];norm_num;linarith [hw.2]
    have bare := (paidBareDifferentiable owner (1-observation.coordinate) (2*w) positive below).comp w
      ((differentiableAt_const (2:ℂ)).mul differentiableAt_id)
    unfold actorQuotient
    exact (((differentiableAt_const _).mul bare).mul
      (coefficient_analytic n w hw).differentiableAt).differentiableWithinAt
  · exact burnolPhysicalHeatMellinStrip_isOpen

private theorem actor_heat_Xi_factor {owner : GlobalGermOwner} (observation : GeneratedRiemannZeroObservationAt owner)
    (n:Nat) (w:ℂ) (inside:w∈burnolPhysicalHeatMellinStrip) :
    burnolDivisionNormalizedPhysicalHeatMellin (burnolPaCombApproximation n) w=
      (w-burnolAnalyticComplementDivisionCenter observation)^generatedRiemannXiZeroOrder owner observation.coordinate*
        actorQuotient observation n w := by
  have positive : 0<(2*w).re := by simp only [mul_re];norm_num;linarith [inside.1]
  have below : (2*w).re<1 := by simp only [mul_re];norm_num;linarith [inside.2]
  have zero : 2*w≠0 := ne_of_apply_ne Complex.re (by simpa only [zero_re] using positive.ne')
  have one : 2*w≠1 := ne_of_apply_ne Complex.re (by simpa only [one_re] using below.ne)
  rw [actual_comb_heat_germ n inside]
  change 2*riemannZeta (2*w)*burnolPaCombResponseCoefficient (1-2*w) n=_
  rw [←generatedRiemannZeta_eq_mathlib owner,
    generatedRiemannZeta_zero_factorization owner (1-observation.coordinate) (2*w)
      zero one (Gammaℝ_ne_zero_of_re_pos positive),generatedRiemannXiZeroOrder_one_sub]
  have base : 2*w-(1-observation.coordinate)=2*(w-burnolAnalyticComplementDivisionCenter observation) := by
    unfold burnolAnalyticComplementDivisionCenter;ring
  rw [base,mul_pow]
  unfold actorQuotient
  ring

private def actorPhysical {owner : GlobalGermOwner} (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬∃n:Nat,observation.coordinate=-2*(n+1))
    (rightHalf : 1/2<observation.coordinate.re) (n k:Nat)
    (atMost:k≤generatedRiemannXiZeroOrder owner observation.coordinate) :BurnolPaAmbientCarrier :=
  ⟨actor observation rightHalf n k,actor_physical observation nontrivial rightHalf n k atMost⟩

private theorem actor_heat_scalar {owner : GlobalGermOwner} (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬∃n:Nat,observation.coordinate=-2*(n+1))
    (rightHalf : 1/2<observation.coordinate.re) (n k:Nat)
    (atMost:k≤generatedRiemannXiZeroOrder owner observation.coordinate)
    (w:ℂ) (right:1/4<w.re) (below:w.re<1/2) :
    burnolDivisionNormalizedPhysicalHeatMellin (actorPhysical observation nontrivial rightHalf n k atMost) w=
      (-(1/(observation.coordinate/2+w-(1/2:ℂ))))^k*
        burnolDivisionNormalizedPhysicalHeatMellin (burnolPaCombApproximation n) w := by
  induction k with
  | zero =>
    have same : actorPhysical observation nontrivial rightHalf n 0 atMost=burnolPaCombApproximation n := by
      apply Subtype.ext
      simp only [actorPhysical,actor,CombSource.Division.rawIterate,pow_zero,one_apply_eq_self]
    rw [same,pow_zero,one_mul]
  | succ k ih =>
    let previous := actorPhysical observation nontrivial rightHalf n k (by omega)
    let next := actorPhysical observation nontrivial rightHalf n (k+1) atMost
    have rq : 1/4<(observation.coordinate/2).re := by rw [Complex.div_re];norm_num;linarith
    have source := CombSource.Pricing.original_R_scalar_action (observation.coordinate/2) rq previous w right below
    change burnolDivisionNormalizedPhysicalHeatMellin
      (burnolEvenAmbientProjection (burnolDirectRightResolvent (observation.coordinate/2) (previous:BurnolL2))) w+
      2*burnolAmbientCompletedMellinEvaluator (burnolDivisionCompletedMellinCoordinate w right below)
        ((evenBurnolClosedFace q).toSubmoduleᗮ.starProjection (burnolDirectRightResolvent (observation.coordinate/2) (previous:BurnolL2)))=
      _ at source
    have raw : burnolDirectRightResolvent (observation.coordinate/2) (previous:BurnolL2)=(next:BurnolL2) :=
      (actor_succ observation rightHalf n k).symm
    rw [raw,Submodule.starProjection_orthogonal_apply_eq_zero next.property,map_zero,mul_zero,add_zero] at source
    have fixed : burnolEvenAmbientProjection (next:BurnolL2)=next :=
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self next
    rw [fixed] at source
    exact source.trans (by rw [ih (by omega)];ring)

private theorem actor_exact_heat {owner : GlobalGermOwner} (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬∃n:Nat,observation.coordinate=-2*(n+1))
    (rightHalf : 1/2<observation.coordinate.re) (n:Nat) :
    burnolDivisionNormalizedPhysicalHeatMellin
      (actorPhysical observation nontrivial rightHalf n (generatedRiemannXiZeroOrder owner observation.coordinate) (le_refl _))
      (burnolAnalyticComplementDivisionCenter observation)=
      2*burnolPaCombResponseCoefficient observation.coordinate n*
        burnolAnalyticComplementIteratedResolventFinitePart owner observation
          (burnolAnalyticComplementDivisionCenter observation) := by
  let m := generatedRiemannXiZeroOrder owner observation.coordinate
  let center := burnolAnalyticComplementDivisionCenter observation
  let value := actorPhysical observation nontrivial rightHalf n m (le_refl _)
  have complete : EqOn (burnolDivisionNormalizedPhysicalHeatMellin value)
      (fun w:ℂ => (-1:ℂ)^m*actorQuotient observation n w) burnolPhysicalHeatMellinStrip := by
    have eventuallyEqual : burnolDivisionNormalizedPhysicalHeatMellin value=ᶠ[𝓝 (3/8:ℂ)]
        (fun w:ℂ => (-1:ℂ)^m*actorQuotient observation n w) := by
      have rightNhd : {w:ℂ | 1/4<w.re}∈𝓝 (3/8:ℂ) :=
        (isOpen_Ioi.preimage Complex.continuous_re).mem_nhds (by norm_num)
      have belowNhd : {w:ℂ | w.re<1/2}∈𝓝 (3/8:ℂ) :=
        (isOpen_Iio.preimage Complex.continuous_re).mem_nhds (by norm_num)
      filter_upwards [rightNhd,belowNhd] with w wr wb
      rw [actor_heat_scalar observation nontrivial rightHalf n m (le_refl _) w wr wb,
        actor_heat_Xi_factor observation n w ⟨by linarith,wb⟩]
      have denominator : observation.coordinate/2+w-(1/2:ℂ)=w-center := by dsimp [center,burnolAnalyticComplementDivisionCenter];ring
      have nonzero : w-center≠0 := by
        apply ne_of_apply_ne Complex.re
        dsimp [center,burnolAnalyticComplementDivisionCenter]
        simp only [div_re,one_re]
        norm_num
        linarith
      rw [denominator,show -(1/(w-center))=(-1:ℂ)*(w-center)⁻¹ by ring,mul_pow,inv_pow]
      rw [←mul_assoc,mul_assoc ((-1:ℂ)^m),inv_mul_cancel₀ (pow_ne_zero _ nonzero),mul_one]
    have rhs : AnalyticOnNhd ℂ (fun w:ℂ => (-1:ℂ)^m*actorQuotient observation n w) burnolPhysicalHeatMellinStrip :=
      (analyticOnNhd_const.mul (actor_quotient_analytic observation n))
    exact (burnolDivisionNormalizedPhysicalHeatMellin_analyticOn value).eqOn_of_preconnected_of_eventuallyEq
      rhs burnolPhysicalHeatMellinStrip_isConnected.isPreconnected (by constructor <;> norm_num) eventuallyEqual
  have centerInside : center∈burnolPhysicalHeatMellinStrip := by
    dsimp [center,burnolAnalyticComplementDivisionCenter,burnolPhysicalHeatMellinStrip]
    simp only [div_re,one_re]
    norm_num
    constructor <;> linarith [observation.coordinate_re_lt_one]
  have source := complete centerInside
  change burnolDivisionNormalizedPhysicalHeatMellin value center=_
  rw [source]
  change (-1:ℂ)^m*actorQuotient observation n center=_
  unfold actorQuotient burnolAnalyticComplementIteratedResolventFinitePart burnolAnalyticComplementQuarterQuotient
  rw [show 1-2*center=observation.coordinate by dsimp [center,burnolAnalyticComplementDivisionCenter];ring,
    show 2*center=1-observation.coordinate by dsimp [center,burnolAnalyticComplementDivisionCenter];ring,
    burnolCoordinateMatchedLocalizedSpectrum_at_eq_bare]
  ring

private theorem fourier_heat_read {owner : GlobalGermOwner} (observation : GeneratedRiemannZeroObservationAt owner)
    (rightHalf : 1/2<observation.coordinate.re) (value:BurnolPaAmbientCarrier) :
    burnolCompletedMellinEvaluator (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf) (evenFaceFourier q value)=
      (Gammaℝ (1-observation.coordinate)/Gammaℝ observation.coordinate)*(1/2:ℂ)*
        burnolDivisionNormalizedPhysicalHeatMellin value (burnolAnalyticComplementDivisionCenter observation) := by
  let coordinate := burnolDivisionZeroCompletedMellinCoordinate observation rightHalf
  let center := burnolAnalyticComplementDivisionCenter observation
  have bridge := burnolGenericHomogeneousGammaMellinBridge (evenFaceFourier q value) coordinate
  have square := burnolGenericGaussianFourierHomogeneousIdentity value observation.coordinate
  have gammaNe : Gammaℝ observation.coordinate≠0 := Gammaℝ_ne_zero_of_re_pos (lt_trans (by norm_num) rightHalf)
  have complementNe : Gammaℝ (1-observation.coordinate)≠0 := Gammaℝ_ne_zero_of_re_pos (by
    simp only [sub_re,one_re];linarith [observation.coordinate_re_lt_one])
  change Gammaℝ observation.coordinate*burnolCompletedMellinEvaluator coordinate (evenFaceFourier q value)=
    (1/2:ℂ)*mellin (burnolGenericGaussianHeatPairTotal (fourierL2 (value:BurnolL2))) (observation.coordinate/2) at bridge
  rw [square] at bridge
  rw [show (1-observation.coordinate)/2=center by dsimp [center,burnolAnalyticComplementDivisionCenter];ring] at bridge
  unfold burnolDivisionNormalizedPhysicalHeatMellin
  rw [show 2*center=1-observation.coordinate by dsimp [center,burnolAnalyticComplementDivisionCenter];ring]
  apply mul_left_cancel₀ gammaNe
  field_simp [gammaNe,complementNe]
  linear_combination 2*bridge

/-- The original A_n actor itself releases its first nonzero Fourier read at the exact Xi order. -/
theorem actor_exact_order_fourier {owner : GlobalGermOwner} (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬∃n:Nat,observation.coordinate=-2*(n+1))
    (rightHalf : 1/2<observation.coordinate.re) (n:Nat) :
    CombSource.Division.fourierRead observation rightHalf
      (actor observation rightHalf n (generatedRiemannXiZeroOrder owner observation.coordinate))=
      2*burnolPaCombResponseCoefficient observation.coordinate n*
        burnolAnalyticComplementExpectedPhysicalFourierRead owner observation := by
  let value := actorPhysical observation nontrivial rightHalf n
    (generatedRiemannXiZeroOrder owner observation.coordinate) (le_refl _)
  have fixed : burnolEvenAmbientProjection (value:BurnolL2)=value :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self value
  change burnolCompletedMellinEvaluator (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf)
    (evenFaceFourier q (burnolEvenAmbientProjection (value:BurnolL2)))=_
  rw [fixed,fourier_heat_read observation rightHalf value,actor_exact_heat observation nontrivial rightHalf n]
  unfold burnolAnalyticComplementExpectedPhysicalFourierRead burnolAnalyticComplementDivisionCenter
  ring

def releaseRead {owner : GlobalGermOwner} (observation : GeneratedRiemannZeroObservationAt owner) (n:Nat) :ℂ :=
  2*burnolPaCombResponseCoefficient observation.coordinate n*burnolAnalyticComplementExpectedPhysicalFourierRead owner observation

theorem releaseRead_ne_zero {owner : GlobalGermOwner} (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬∃n:Nat,observation.coordinate=-2*(n+1))
    (rightHalf : 1/2<observation.coordinate.re) (n:Nat) : releaseRead observation n≠0 := by
  exact mul_ne_zero (mul_ne_zero (by norm_num)
    (burnolPaCombResponseCoefficient_ne_zero observation.coordinate (lt_trans (by norm_num) rightHalf) n))
      (burnolAnalyticComplementExpectedPhysicalFourierRead_ne_zero observation nontrivial)

/-- The next original R action exits the physical carrier in its complete, source-generated outside vector. -/
theorem actor_first_outside_source {owner : GlobalGermOwner} (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬∃n:Nat,observation.coordinate=-2*(n+1))
    (rightHalf : 1/2<observation.coordinate.re) (n:Nat) :
    O (actor observation rightHalf n (generatedRiemannXiZeroOrder owner observation.coordinate+1))=
      (-2*releaseRead observation n) • physicalOutsideColumn (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf) := by
  let coordinate := burnolDivisionZeroCompletedMellinCoordinate observation rightHalf
  let value := actorPhysical observation nontrivial rightHalf n
    (generatedRiemannXiZeroOrder owner observation.coordinate) (le_refl _)
  have source := original_R_physical_outside_source coordinate value
  have sameRead : inner ℂ (fourierL2 (generatedK coordinate)) (value:BurnolL2)=releaseRead observation n := by
    rw [generatedK_eq_original]
    change inner ℂ (F (burnolCompletedMellinRieszVector coordinate)) value=_
    have moved := (evenFaceFourierEquiv q).inner_map_map (burnolCompletedMellinRieszVector coordinate) (F value)
    have invol : F (F value)=value := evenFaceFourier_involutive q value
    rw [invol] at moved
    rw [moved,burnolCompletedMellinRieszVector_readback]
    have actual := actor_exact_order_fourier observation nontrivial rightHalf n
    change burnolCompletedMellinEvaluator coordinate (evenFaceFourier q (burnolEvenAmbientProjection (value:BurnolL2)))=_ at actual
    have fixed : burnolEvenAmbientProjection (value:BurnolL2)=value :=
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self value
    rw [fixed] at actual
    exact actual
  rw [sameRead] at source
  rw [actor_succ]
  exact source

theorem actor_first_outside_ne_zero {owner : GlobalGermOwner} (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬∃n:Nat,observation.coordinate=-2*(n+1))
    (rightHalf : 1/2<observation.coordinate.re) (n:Nat) :
    O (actor observation rightHalf n (generatedRiemannXiZeroOrder owner observation.coordinate+1))≠0 := by
  rw [actor_first_outside_source observation nontrivial rightHalf n]
  apply smul_ne_zero (mul_ne_zero (by norm_num) (releaseRead_ne_zero observation nontrivial rightHalf n))
  intro zero
  have reflected := congrArg fourierL2 zero
  change fourierL2 (fourierL2.symm (hPowerPhysicalCorrection (OriginalPrimitiveRankBalance.conjugateCoordinate
    (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf))))=fourierL2 0 at reflected
  rw [fourierL2.apply_symm_apply,map_zero] at reflected
  exact powerCorrection_ne_zero _ reflected

end OriginalKFiniteOrderRelease
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
