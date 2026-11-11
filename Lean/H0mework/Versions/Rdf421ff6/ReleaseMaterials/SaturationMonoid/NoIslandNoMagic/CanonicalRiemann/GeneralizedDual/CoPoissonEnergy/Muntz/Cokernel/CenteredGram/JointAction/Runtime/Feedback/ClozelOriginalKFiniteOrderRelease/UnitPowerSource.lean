import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitJetSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.UnitPowerSource
open Complex MeasureTheory Set BurnolPhysicalState
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open OriginalKSourceResolventReconstruction OriginalKFullAdjointSource OriginalRieszSource
open OriginalKDirectRCofinalOutsideVolterraSource
open OriginalKCrossParameterRAdjointSource.SharedOutsideSource
open OriginalKCrossParameterRAdjointSource.PaFeedbackSource
open OriginalKCrossParameterRAdjointSource.PaSpectralSource
open scoped InnerProductSpace
local notation "q" => burnolUnscaledCommonGapRadius
local notation "F" => evenFaceFourierEquiv q
local instance powerPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace q).isClosed.isComplete

private theorem source_norm_strict (c : BurnolCompletedMellinCoordinate)
    (native : (burnolCompletedMellinRieszVector c : BurnolL2) ≠ 0) : ‖Kernel.beta c‖ < ‖Kernel.A c‖ := by
  have green := OriginalRieszSourceGreen.original_kernel_gram c c
  have product (z : ℂ) : star z*z=((‖z‖^2:ℝ):ℂ) := by
    simpa only [Complex.star_def,Complex.normSq_eq_norm_sq] using
      (Complex.normSq_eq_conj_mul_self (z:=z)).symm
  rw [inner_self_eq_norm_sq_to_K,product,product] at green
  have realGreen := congrArg Complex.re green
  simp [Complex.mul_re,pow_two] at realGreen
  norm_num at realGreen
  have rate : 0 < 2*c.value.re-1 := by linarith [c.rightHalf]
  have mass : 0 < ‖(burnolCompletedMellinRieszVector c : BurnolL2)‖^2 := sq_pos_of_pos (norm_pos_iff.mpr native)
  have positive := mul_pos rate mass
  nlinarith [norm_nonneg (Kernel.A c),norm_nonneg (Kernel.beta c)]

private theorem mixed_kernel_source_nonzero (left right : BurnolCompletedMellinCoordinate)
    (leftNative : (burnolCompletedMellinRieszVector left : BurnolL2) ≠ 0) (rightNative : (burnolCompletedMellinRieszVector right : BurnolL2) ≠ 0) :
    inner ℂ (burnolCompletedMellinRieszVector left : BurnolL2) (burnolCompletedMellinRieszVector right : BurnolL2) ≠ 0 := by
  have L := source_norm_strict left leftNative
  have R := source_norm_strict right rightNative
  intro zero
  have green := OriginalRieszSourceGreen.original_kernel_gram left right
  rw [zero, mul_zero] at green
  have difference : star (Kernel.A left)*Kernel.A right =
      star (Kernel.beta left)*Kernel.beta right := by
    have vanished : star (Kernel.A left)*Kernel.A right-
        star (Kernel.beta left)*Kernel.beta right=0 :=
      (mul_eq_zero.mp green.symm).resolve_left (by norm_num)
    exact sub_eq_zero.mp vanished
  have normRead := congrArg norm difference
  simp only [norm_mul,norm_star] at normRead
  have first := mul_le_mul_of_nonneg_right L.le (norm_nonneg (Kernel.beta right))
  have second := mul_lt_mul_of_pos_left R (lt_of_le_of_lt (norm_nonneg (Kernel.beta left)) L)
  exact (ne_of_lt (lt_of_le_of_lt first second)) normRead.symm

private theorem observation_kernel_source_nonzero {owner:GlobalGermOwner}
    (observation:GeneratedRiemannZeroObservationAt owner)
    (nontrivial:¬∃n:Nat,observation.coordinate=-2*(n+1))
    (rightHalf:1/2<observation.coordinate.re) :
    (burnolCompletedMellinRieszVector (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf):BurnolL2)≠0 := by
  have native := (OriginalRieszSource.Kernel.zero_owned_response observation nontrivial rightHalf).1
  intro zero
  apply native
  apply Subtype.ext
  apply Subtype.ext
  exact zero

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "e" => burnolAnalyticComplementExpectedPhysicalFourierRead ActualAnalyticOwner observation
local notation "bc" => burnolPaResolventSourceCoefficient c
local notation "K" => (burnolCompletedMellinRieszVector c : BurnolL2)
local notation "FK" => fourierL2 K
local notation "Rpow" => CombSource.Division.rawIterate observation half.down

/-- These are the original full L2 powers of the actual unit response. -/
def unitPower (j:Nat) : BurnolL2 := Rpow j (burnolUnitTailResponse c 4)

/-- The coefficient is generated from the original Xi-order source, with the actual first-slot convention. -/
def feedbackCoefficient : ℂ := -star (hQuarterAmplitude c)*e

def paPowerCoefficient : ℂ := -hQuarterAmplitude c*star e

def fulladjointPowerZ : BurnolL2 :=
  (((burnolDirectRightResolventCLM c)^m).adjoint) (sourceKernelCombo c)

def paPowerField : BurnolPaAmbientCarrier := paPowerCoefficient observation half • paCoefficientSource c

private theorem power_succ (j:Nat) (value:BurnolL2) :
    Rpow (j+1) value=Rpow j (burnolDirectRightResolvent ((c).value/2) value) := by
  simp only [CombSource.Division.rawIterate,pow_succ,mul_apply_eq_comp,CombSource.Division.rawAction]
  rfl

/-- One actual source split suffices at every power; its corrected branch remains the whole original Pa. -/
theorem actual_Pa_power_split (p:BurnolPaAmbientCarrier) (inside:p∈burnolCompactCoPoissonClosedRange) (j:Nat) :
    Rpow (j+1) (p:BurnolL2)=
      Rpow j (burnolPaSourceCorrection c ⟨p,inside⟩:BurnolL2)+bc p • unitPower observation half j := by
  have split : burnolDirectRightResolvent ((c).value/2) (p:BurnolL2)=
      (burnolPaSourceCorrection c ⟨p,inside⟩:BurnolL2)+bc p • burnolUnitTailResponse c 4 := by
    change burnolDirectRightResolvent ((c).value/2) (p:BurnolL2)=
      (burnolDirectRightResolvent ((c).value/2) (p:BurnolL2)-bc p • burnolUnitTailResponse c 4)+_
    abel
  rw [power_succ observation half j _,split,map_add,map_smul]
  rfl

include nontrivial

/-- The two actual Q source laws determine the original comb coefficient. -/
theorem actual_comb_source_coefficient :
    bc (burnolPaCombApproximation 0)=2*burnolPaCombResponseCoefficient observation.coordinate 0 := by
  let Q := burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
  let one := burnolZeroOwnedUnitOneState observation nontrivial half.down
  let tail := burnolZeroOwnedUnitTailState observation nontrivial half.down
  obtain ⟨wave,wavePa,waveRead⟩ := Submodule.mem_map.mp
    (burnolUnitPowerShellWave_originalPa c 1 (by norm_num) (by norm_num))
  have shell := burnolUnitTailResponse_shell c 1 (by norm_num) (by norm_num)
  rw [←waveRead] at shell
  have physicalShell : one-tail=wave := Subtype.ext shell
  have shellRead := congrArg Q physicalShell
  rw [map_sub,Submodule.starProjection_orthogonal_apply_eq_zero wavePa] at shellRead
  have sameQ : Q one=Q tail := sub_eq_zero.mp shellRead
  have tailNe : Q tail≠0 := by
    intro zero
    apply burnolZeroOwnedUnitTailState_notInPa observation nontrivial half.down
    have inventory := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_add_starProjection_orthogonal tail
    change burnolCompactCoPoissonClosedRange.toSubmodule.starProjection tail+Q tail=tail at inventory
    rw [zero,add_zero] at inventory
    change tail∈burnolCompactCoPoissonClosedRange
    rw [←inventory]
    exact Submodule.starProjection_apply_mem _ _
  have generated := burnolPaResolventPhysicalResponse_Q observation nontrivial half.down
    (burnolPaCombApproximation 0) (burnolPaCombApproximation_mem 0)
  have sameResponse : burnolPaResolventPhysicalResponse observation nontrivial half.down
      (burnolPaCombApproximation 0) (burnolPaCombApproximation_mem 0)=
      burnolPaCombPhysicalResponse observation nontrivial half.down 0 := rfl
  rw [sameResponse] at generated
  change Q (burnolPaCombPhysicalResponse observation nontrivial half.down 0)=bc (burnolPaCombApproximation 0) • Q tail at generated
  have scaled := burnolPaCombPhysicalResponse_scaledQ observation nontrivial half.down 0
  simp only [Nat.cast_zero] at scaled
  change (observation.coordinate/2) • Q (burnolPaCombPhysicalResponse observation nontrivial half.down 0)=
    (((0:ℂ)+2)*(Complex.exp (observation.coordinate*(Real.log (1+burnolPaCombSourceWidth 0):ℂ))-1)) • Q one at scaled
  rw [generated,sameQ,smul_smul] at scaled
  have parameterNe : observation.coordinate≠0 :=
    ne_of_apply_ne Complex.re (by simpa only [zero_re] using (lt_trans (by norm_num) half.down).ne')
  have factor : ((0:ℂ)+2)*(Complex.exp (observation.coordinate*(Real.log (1+burnolPaCombSourceWidth 0):ℂ))-1)=
      (observation.coordinate/2)*(2*burnolPaCombResponseCoefficient observation.coordinate 0) := by
    unfold burnolPaCombResponseCoefficient
    simp only [Nat.cast_zero]
    field_simp [parameterNe]
  rw [factor] at scaled
  have coefficients := (smul_left_injective ℂ tailNe) scaled
  exact mul_left_cancel₀ (div_ne_zero parameterNe (by norm_num : (2:ℂ)≠0)) coefficients

private theorem comb_coefficient_ne : bc (burnolPaCombApproximation 0)≠0 := by
  rw [actual_comb_source_coefficient observation nontrivial half]
  exact mul_ne_zero (by norm_num)
    (burnolPaCombResponseCoefficient_ne_zero observation.coordinate (by linarith [half.down]) 0)

/-- The physical qualification comes from the same original comb and corrected full-Pa branch. -/
theorem unitPower_physical (j:Nat) (before:j<m) :
    unitPower observation half j∈evenBurnolClosedFace q := by
  have split := actual_Pa_power_split observation half (burnolPaCombApproximation 0) (burnolPaCombApproximation_mem 0) j
  have lhs := CombSource.Division.whole_pa_physical observation nontrivial half.down (j+1) (by omega)
    (burnolPaCombApproximation 0) (burnolPaCombApproximation_mem 0)
  have rhs := CombSource.Division.whole_pa_physical observation nontrivial half.down j (by omega)
    (burnolPaSourceCorrection c ⟨burnolPaCombApproximation 0,burnolPaCombApproximation_mem 0⟩)
    (burnolPaSourceCorrection_mem c _)
  have difference := (evenBurnolClosedFace q).toSubmodule.sub_mem lhs rhs
  rw [split,add_sub_cancel_left] at difference
  exact ((evenBurnolClosedFace q).toSubmodule.smul_mem_iff (comb_coefficient_ne observation nontrivial half)).mp difference

omit nontrivial in
private theorem physical_fourier_read (value:BurnolL2) (physical:value∈evenBurnolClosedFace q) :
    CombSource.Division.fourierRead observation half.down value=inner ℂ FK value := by
  let p : BurnolPaAmbientCarrier := ⟨value,physical⟩
  have fixed : burnolEvenAmbientProjection value=p := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self p
  change burnolCompletedMellinEvaluator c (evenFaceFourier q (burnolEvenAmbientProjection value))=_
  rw [fixed,←burnolCompletedMellinRieszVector_readback]
  have moved := (evenFaceFourierEquiv q).inner_map_map (burnolCompletedMellinRieszVector c) (F p)
  have invol : F (F p)=p := evenFaceFourier_involutive q p
  rw [invol] at moved
  exact moved.symm

private theorem allPa_fourier_power_zero (p:BurnolPaAmbientCarrier) (inside:p∈burnolCompactCoPoissonClosedRange)
    (j:Nat) (before:j<m) : inner ℂ FK (Rpow j (p:BurnolL2))=0 := by
  rw [←physical_fourier_read observation half _
    (CombSource.Division.whole_pa_physical observation nontrivial half.down j before.le p inside)]
  exact CombSource.Division.whole_pa_fourier_zero observation nontrivial half.down j before p inside

theorem unitPower_fourier_low (j:Nat) (before:j+1<m) : inner ℂ FK (unitPower observation half j)=0 := by
  have split := congrArg (inner ℂ FK)
    (actual_Pa_power_split observation half (burnolPaCombApproximation 0) (burnolPaCombApproximation_mem 0) j)
  rw [inner_add_right,inner_smul_right,
    allPa_fourier_power_zero observation nontrivial half _ (burnolPaCombApproximation_mem 0) (j+1) before,
    allPa_fourier_power_zero observation nontrivial half _ (burnolPaSourceCorrection_mem c _) j (by omega),zero_add] at split
  exact (mul_eq_zero.mp split.symm).resolve_left (comb_coefficient_ne observation nontrivial half)

theorem unitPower_fourier_top : inner ℂ FK (unitPower observation half (m-1))=e := by
  have positive := generatedRiemannXiZeroOrder_pos observation nontrivial
  have split := congrArg (inner ℂ FK)
    (actual_Pa_power_split observation half (burnolPaCombApproximation 0) (burnolPaCombApproximation_mem 0) (m-1))
  have actorRead := actor_exact_order_fourier observation nontrivial half.down 0
  change CombSource.Division.fourierRead observation half.down (Rpow m (burnolPaCombApproximation 0:BurnolL2))=_ at actorRead
  rw [physical_fourier_read observation half _
    (CombSource.Division.whole_pa_physical observation nontrivial half.down m le_rfl _ (burnolPaCombApproximation_mem 0))] at actorRead
  rw [show m-1+1=m by omega,inner_add_right,inner_smul_right,actorRead,
    allPa_fourier_power_zero observation nontrivial half _ (burnolPaSourceCorrection_mem c _) (m-1) (by omega),zero_add,
    actual_comb_source_coefficient observation nontrivial half] at split
  exact mul_left_cancel₀ (mul_ne_zero (by norm_num)
    (burnolPaCombResponseCoefficient_ne_zero observation.coordinate (by linarith [half.down]) 0)) split.symm

omit nontrivial in
private theorem ambient_physical_read (d:BurnolCompletedMellinCoordinate) (value:BurnolPaAmbientCarrier) :
    burnolAmbientCompletedMellinEvaluator d (value:BurnolL2)=
      inner ℂ (burnolCompletedMellinRieszVector d:BurnolL2) (value:BurnolL2) := by
  have restrict := congrArg (fun f:BurnolPaAmbientCarrier →L[ℂ] ℂ => f value)
    (burnolAmbientCompletedMellinEvaluator_restrict d)
  change burnolAmbientCompletedMellinEvaluator d (value:BurnolL2)=burnolCompletedMellinEvaluator d value at restrict
  exact restrict.trans (burnolCompletedMellinRieszVector_readback d value).symm

omit nontrivial in
private theorem power_succ_left (j:Nat) (value:BurnolL2) :
    Rpow (j+1) value=burnolDirectRightResolvent ((c).value/2) (Rpow j value) := by
  simp only [CombSource.Division.rawIterate,pow_succ',mul_apply_eq_comp,CombSource.Division.rawAction]
  rfl

omit nontrivial in
private theorem coordinate_eq {left right:BurnolCompletedMellinCoordinate} (same:left.value=right.value) : left=right := by
  cases left
  cases right
  cases same
  rfl

private theorem allPa_K_power_zero (p:BurnolPaAmbientCarrier) (inside:p∈burnolCompactCoPoissonClosedRange)
    (j:Nat) (atMost:j≤m) : inner ℂ K (Rpow j (p:BurnolL2))=0 := by
  induction j with
  | zero =>
    simp only [CombSource.Division.rawIterate,pow_zero,one_apply_eq_self]
    have orthogonal := riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal c observation.mathlibZero
    exact inner_eq_zero_symm.mp (orthogonal p inside)
  | succ j ih =>
    have previous := ih (by omega)
    let input : BurnolPaAmbientCarrier := ⟨Rpow j (p:BurnolL2),
      CombSource.Division.whole_pa_physical observation nontrivial half.down j (by omega) p inside⟩
    let output : BurnolPaAmbientCarrier := ⟨Rpow (j+1) (p:BurnolL2),
      CombSource.Division.whole_pa_physical observation nontrivial half.down (j+1) atMost p inside⟩
    have right : 1/4<((c).value/2).re := by rw [Complex.div_re];norm_num;linarith [(c).rightHalf]
    have below : ((c).value/2).re<1/2 := by rw [Complex.div_re];norm_num;linarith [(c).belowOne]
    have same : burnolDivisionCompletedMellinCoordinate ((c).value/2) right below=c := by
      apply coordinate_eq
      change 2*((c).value/2)=(c).value
      ring
    have scalar := CombSource.Pricing.ambient_R_scalar_action ((c).value/2) right (input:BurnolL2)
      input.property.1.1 ((c).value/2) right below
    rw [same,ambient_physical_read c input,previous,mul_zero] at scalar
    have outputRead : burnolDirectRightResolvent ((c).value/2) (input:BurnolL2)=(output:BurnolL2) :=
      (power_succ_left observation half j (p:BurnolL2)).symm
    rw [outputRead,ambient_physical_read c output] at scalar
    exact scalar

theorem unitPower_K_low (j:Nat) (before:j<m) : inner ℂ K (unitPower observation half j)=0 := by
  have split := congrArg (inner ℂ K)
    (actual_Pa_power_split observation half (burnolPaCombApproximation 0) (burnolPaCombApproximation_mem 0) j)
  rw [inner_add_right,inner_smul_right,
    allPa_K_power_zero observation nontrivial half _ (burnolPaCombApproximation_mem 0) (j+1) (by omega),
    allPa_K_power_zero observation nontrivial half _ (burnolPaSourceCorrection_mem c _) j (by omega),zero_add] at split
  exact (mul_eq_zero.mp split.symm).resolve_left (comb_coefficient_ne observation nontrivial half)

private theorem allPa_combo_power_low (p:BurnolPaAmbientCarrier) (inside:p∈burnolCompactCoPoissonClosedRange)
    (j:Nat) (before:j<m) : inner ℂ (sourceKernelCombo c) (Rpow j (p:BurnolL2))=0 := by
  rw [sourceKernelCombo_actual,inner_sub_left,inner_smul_left,inner_smul_left,
    allPa_K_power_zero observation nontrivial half p inside j before.le,
    allPa_fourier_power_zero observation nontrivial half p inside j before,mul_zero,mul_zero,sub_zero]

/-- At the exact generated order, every original full Pa test has the same generated unit coefficient. -/
theorem actual_Pa_power_source (p:BurnolPaAmbientCarrier) (inside:p∈burnolCompactCoPoissonClosedRange) :
    inner ℂ (sourceKernelCombo c) (Rpow m (p:BurnolL2))=
      feedbackCoefficient observation half*bc p := by
  have positive := generatedRiemannXiZeroOrder_pos observation nontrivial
  have split := congrArg (inner ℂ (sourceKernelCombo c))
    (actual_Pa_power_split observation half p inside (m-1))
  rw [show m-1+1=m by omega,inner_add_right,inner_smul_right,
    allPa_combo_power_low observation nontrivial half _ (burnolPaSourceCorrection_mem c _) (m-1) (by omega),zero_add] at split
  have top : inner ℂ (sourceKernelCombo c) (unitPower observation half (m-1))=
      feedbackCoefficient observation half := by
    rw [sourceKernelCombo_actual,inner_sub_left,inner_smul_left,inner_smul_left,
      unitPower_K_low observation nontrivial half (m-1) (by omega),
      unitPower_fourier_top observation nontrivial half,mul_zero,zero_sub]
    unfold feedbackCoefficient
    simp only [starRingEnd_apply]
    ring
  rw [top] at split
  exact split.trans (mul_comm _ _)

omit nontrivial in
/-- The adjoint is the full original L2 adjoint of the same power; no physical projection enters its construction. -/
theorem actual_full_power_read (value:BurnolL2) :
    inner ℂ (sourceKernelCombo c) (Rpow m value)=inner ℂ (fulladjointPowerZ observation half) value := by
  rw [fulladjointPowerZ,ContinuousLinearMap.adjoint_inner_left]
  rfl

omit nontrivial in
private theorem paPowerField_price (p:BurnolPaAmbientCarrier) (inside:p∈burnolCompactCoPoissonClosedRange) :
    inner ℂ (paPowerField observation half) p=feedbackCoefficient observation half*bc p := by
  rw [paPowerField,inner_smul_left]
  change star (paPowerCoefficient observation half)*inner ℂ (paCoefficientSource c) p=_
  rw [paCoefficientSource_read c p inside]
  unfold paPowerCoefficient feedbackCoefficient
  simp only [star_mul,star_neg,star_star]
  ring

theorem actual_adjoint_power_Pa_tests (p:BurnolPaAmbientCarrier) (inside:p∈burnolCompactCoPoissonClosedRange) :
    inner ℂ (fulladjointPowerZ observation half) (p:BurnolL2)=feedbackCoefficient observation half*bc p := by
  rw [←actual_full_power_read observation half]
  exact actual_Pa_power_source observation nontrivial half p inside

/-- Full-Pa Riesz uniqueness identifies the actual E field, while the complete adjoint retains every Q/outside component. -/
theorem actual_adjoint_power_Pa_source :
    PA.E (fulladjointPowerZ observation half)=paPowerField observation half := by
  have normal (p:BurnolPaAmbientCarrier) (inside:p∈burnolCompactCoPoissonClosedRange) :
      inner ℂ p (PA.E (fulladjointPowerZ observation half))=inner ℂ p (paPowerField observation half) := by
    rw [PA.wholePa_normal_read _ p inside]
    calc
      inner ℂ (p:BurnolL2) (fulladjointPowerZ observation half)=
          star (inner ℂ (fulladjointPowerZ observation half) (p:BurnolL2)) := (inner_conj_symm _ _).symm
      _ = star (inner ℂ (paPowerField observation half) p) := by
        rw [actual_adjoint_power_Pa_tests observation nontrivial half p inside,
          paPowerField_price observation half p inside]
      _ = inner ℂ p (paPowerField observation half) := inner_conj_symm _ _
  have fieldPa : paPowerField observation half∈burnolCompactCoPoissonClosedRange := by
    apply burnolCompactCoPoissonClosedRange.toSubmodule.smul_mem
    exact burnolCompactCoPoissonActionSquare.toIsometricSquare.target_mem_closedRange
      (OriginalKDirectRCofinalReentrySourceAction.sourceReentryVector
        (OriginalPrimitiveRankBalance.conjugateCoordinate c)).property
  have differencePa : PA.E (fulladjointPowerZ observation half)-paPowerField observation half∈burnolCompactCoPoissonClosedRange :=
    burnolCompactCoPoissonClosedRange.toSubmodule.sub_mem (Submodule.starProjection_apply_mem _ _) fieldPa
  have killed : inner ℂ (PA.E (fulladjointPowerZ observation half)-paPowerField observation half)
      (PA.E (fulladjointPowerZ observation half)-paPowerField observation half)=0 := by
    rw [inner_sub_right,normal _ differencePa,sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp killed)

omit nontrivial in
/-- At simple order the complete adjoint is precisely the already paid first-order source L. -/
theorem simple_order_source (simple:m=1) :
    fulladjointPowerZ observation half=sourceL c ∧
    paPowerCoefficient observation half=UnitJetSource.unitJetPaCoefficient observation half ∧
    feedbackCoefficient observation half=UnitJetSource.unitJetFeedbackCoefficient observation half := by
  constructor
  · apply ext_inner_right ℂ
    intro test
    rw [fulladjointPowerZ,simple,pow_one,ContinuousLinearMap.adjoint_inner_left]
    exact original_R_sourceL_read c test
  · constructor
    · simp only [UnitJetSource.unitJetPaCoefficient,simple,ite_true]
      rfl
    · simp only [UnitJetSource.unitJetFeedbackCoefficient,simple,ite_true]
      rfl

omit nontrivial in
/-- The quarter amplitude reads the same full original K through the conjugate Mellin source. -/
theorem hQuarterAmplitude_source_gram :
    hQuarterAmplitude c=-2*inner ℂ
      (burnolCompletedMellinRieszVector (OriginalPrimitiveRankBalance.conjugateCoordinate c):BurnolL2) K := by
  have gap : hQuarterGap c=burnolConstantGapCoefficient q (burnolCompletedMellinRieszVector c) := by
    unfold hQuarterGap
    rw [generatedK_eq_original]
    simp only [burnolQuarterMeanCoefficient,burnolConstantGapCoefficient,
      smul_apply,ContinuousLinearMap.comp_apply,Submodule.subtypeL_apply,
      innerSL_apply_apply,smul_eq_mul,Complex.ofReal_pow]
    change inner ℂ (intervalConstant q) (burnolQuarterRestriction K)/
      (‖intervalConstant q‖:ℂ)^2=
      ((‖intervalConstant q‖:ℂ)^2)⁻¹*inner ℂ (intervalConstant q) (burnolQuarterRestriction K)
    ring
  change hQuarterAmplitude c=-2*inner ℂ
    (burnolCompletedMellinRieszVector (OriginalPrimitiveRankBalance.conjugateCoordinate c))
    (burnolCompletedMellinRieszVector c)
  rw [burnolCompletedMellinRieszVector_readback,burnolCompletedMellinEvaluator_apply]
  unfold hQuarterAmplitude
  rw [generatedK_eq_original,gap]
  dsimp only [burnolMellinTailEvaluator,OriginalPrimitiveRankBalance.conjugateCoordinate,
    burnolMellinGapMoment,burnolRadiusMellinGapMoment,burnolUnscaledCommonGapRadius]
  ring

/-- The same finite comb source proves that its Pa Riesz covector is nonzero. -/
theorem actual_pa_covector_ne_zero : paCoefficientSource c≠0 := by
  intro zero
  have read := paCoefficientSource_read c (burnolPaCombApproximation 0) (burnolPaCombApproximation_mem 0)
  rw [zero,inner_zero_left] at read
  exact comb_coefficient_ne observation nontrivial half read.symm

/-- All lower full adjoint powers have zero whole-Pa field at the original exact order. -/
theorem actual_adjoint_lower_Pa_zero (j:Nat) (before:j<m) :
    PA.E ((((burnolDirectRightResolventCLM c)^j).adjoint) (sourceKernelCombo c))=0 := by
  let H := (((burnolDirectRightResolventCLM c)^j).adjoint) (sourceKernelCombo c)
  have tests (p:BurnolPaAmbientCarrier) (inside:p∈burnolCompactCoPoissonClosedRange) :
      inner ℂ H (p:BurnolL2)=0 := by
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact allPa_combo_power_low observation nontrivial half p inside j before
  have self : inner ℂ (PA.E H) (PA.E H)=0 := by
    rw [PA.wholePa_normal_read H (PA.E H) (Submodule.starProjection_apply_mem _ _)]
    exact inner_eq_zero_symm.mp (tests _ (Submodule.starProjection_apply_mem _ _))
  exact inner_self_eq_zero.mp self

/-- Full original source Green forms make the actual quarter amplitude a nonzero source unit. -/
theorem hQuarterAmplitude_source_ne_zero : hQuarterAmplitude c≠0 := by
  rw [hQuarterAmplitude_source_gram observation half]
  apply mul_ne_zero (by norm_num)
  have rightNative := observation_kernel_source_nonzero observation nontrivial half.down
  let reflected := conjugateZeroObservation observation
  have reflectedHalf : 1/2<reflected.coordinate.re := by
    change 1/2<(starRingEnd ℂ observation.coordinate).re
    simpa only [Complex.conj_re] using half.down
  have leftNative := observation_kernel_source_nonzero reflected
    (observation.conjugate_nontrivial nontrivial) reflectedHalf
  have same : burnolDivisionZeroCompletedMellinCoordinate reflected reflectedHalf=
      OriginalPrimitiveRankBalance.conjugateCoordinate c := by rfl
  rw [same] at leftNative
  exact mixed_kernel_source_nonzero _ _ leftNative rightNative

theorem feedbackCoefficient_ne_zero : feedbackCoefficient observation half≠0 := by
  unfold feedbackCoefficient
  exact mul_ne_zero (neg_ne_zero.mpr (star_ne_zero.mpr (hQuarterAmplitude_source_ne_zero observation nontrivial half)))
    (burnolAnalyticComplementExpectedPhysicalFourierRead_ne_zero observation nontrivial)

theorem paPowerCoefficient_ne_zero : paPowerCoefficient observation half≠0 := by
  unfold paPowerCoefficient
  exact mul_ne_zero (neg_ne_zero.mpr (hQuarterAmplitude_source_ne_zero observation nontrivial half))
    (star_ne_zero.mpr (burnolAnalyticComplementExpectedPhysicalFourierRead_ne_zero observation nontrivial))

theorem paPowerField_ne_zero : paPowerField observation half≠0 := by
  exact smul_ne_zero (paPowerCoefficient_ne_zero observation nontrivial half)
    (actual_pa_covector_ne_zero observation nontrivial half)

/-- The first nonzero whole-Pa adjoint return is generated at the original exact natural order. -/
theorem actual_adjoint_power_Pa_ne_zero : PA.E (fulladjointPowerZ observation half)≠0 := by
  rw [actual_adjoint_power_Pa_source observation nontrivial half]
  exact paPowerField_ne_zero observation nontrivial half

end OriginalKFiniteOrderRelease.UnitPowerSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
