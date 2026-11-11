import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRPrimitiveMobiusReturnSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.PrimitiveRank.Box

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRPrimitiveMobiusNativeIncidenceSource
open Complex MeasureTheory Set FourierTransform BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalWholeDebtRPowerWaveDilationSource
open OriginalWholeDebtRPrimitiveMobiusSource
open scoped InnerProductSpace BigOperators FourierTransform
namespace N
export FiniteMobiusResolventFlux
  (interiorBase interior_base_read reverseRankSource source_reverse_flux_three_base
   lower_full_source fullS sigma exteriorMoment actualFlux outerCut source_forward_flux_outer)
end N
open private tate_pair from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRPrimitiveMobiusReturnSource
open private spread_radius from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRPrimitiveMobiusWindowSource
open private mean_add mean_smul mean_constant from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKForcingGapAction.Source
open private meanPrice from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRReciprocalCotestReturnSource
local notation "FL" => fourierL2
local notation "Tate" => burnolTateReciprocalL2
local notation "q" => (1/4 : ℝ)

private def cell (n : ℕ+) (value : BurnolL2) : BurnolL2 :=
  F.cutoff 4 (F.fullPullback n value)-Flux.actualMean value • F.box 4

private theorem cell_read (n : ℕ+) (value : BurnolL2) :
    (cell n value : ℝ → ℂ)=ᵐ[volume]
      (symmetricInterval 4).indicator (fun x => value (x/(n : ℕ))-Flux.actualMean value) := by
  have same : cell n value=burnolRadiusZeroExtension 4 (Flux.lowerPullback n value) := by
    unfold cell F.cutoff F.fullPullback F.box Flux.lowerPullback burnolWindowScalePullback
    simp only [sub_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply,map_sub,map_smul,smul_apply]
    rfl
  have raw:=(ae_restrict_iff' (measurableSet_symmetricInterval 4)).mp
    (FiniteMobiusResolventFlux.lower_pullback_read n value)
  rw [same]
  filter_upwards [burnolRadiusZeroExtension_coe (Flux.lowerPullback n value),raw]
    with x extended source
  rw [extended]
  by_cases inside : x∈symmetricInterval 4
  · rw [indicator_of_mem inside,indicator_of_mem inside,source inside]
  · rw [indicator_of_notMem inside,indicator_of_notMem inside]

private theorem sampled_half (value : BurnolL2)
    (supported : F.cutoff (1/2) value=value) :
    F.cutoff (1/2) (burnolAnnulusSamplingL2 value 0)=burnolAnnulusSamplingL2 value 0 := by
  have raw:=FiniteMobiusResolventFlux.cutoff_read (1/2) value
  rw [supported] at raw
  apply Lp.ext
  filter_upwards [FiniteMobiusResolventFlux.cutoff_read (1/2) (burnolAnnulusSamplingL2 value 0),
    burnolAnnulusSamplingL2_coeFn value 0,raw] with x cut sample source
  rw [cut]
  by_cases inside : x∈symmetricInterval (1/2)
  · rw [indicator_of_mem inside]
  · rw [indicator_of_notMem inside,sample]
    unfold burnolAnnulusSamplingRaw
    simp only [Nat.cast_zero,zero_add,one_mul]
    by_cases annulus : x∈burnolSamplingAnnulus
    · rw [indicator_of_mem annulus,source,indicator_of_notMem inside]
    · rw [indicator_of_notMem annulus]

private theorem tate_effect_supported (coordinate : BurnolCompletedMellinCoordinate) :
    F.cutoff (1/2) (Tate (A.effectCotest coordinate))=Tate (A.effectCotest coordinate) := by
  have sampleSupport:=sampled_half (A.fourierColumn coordinate)
    (OriginalWholeDebtRReciprocalCotestActionSource.fourier_supported coordinate)
  have rRead : Tate (A.reciprocalCotest coordinate)=
      burnolAnnulusSamplingL2 (A.fourierColumn coordinate) 0 := by
    unfold A.reciprocalCotest
    rw [burnolTateReciprocalL2_involutive]
  have right : 1/4<(coordinate.value/2).re := by
    rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]
  have actedRead : Tate (A.weightedField coordinate)=
      A.weight coordinate • Flux.Rplus (coordinate.value/2)
        (burnolAnnulusSamplingL2 (A.fourierColumn coordinate) 0) := by
    rw [A.weighted_field_action,map_smul]
    change A.weight coordinate • Tate (burnolDirectRightResolvent (coordinate.value/2)
      (A.reciprocalCotest coordinate))=_
    rw [FiniteMobiusResolventFlux.tate_R _ right,rRead]
  have contracted:=OriginalPrimitiveRankBalance.cutoff_Rplus_source (1/2) (by norm_num)
    (coordinate.value/2) right (burnolAnnulusSamplingL2 (A.fourierColumn coordinate) 0)
  rw [sampleSupport] at contracted
  unfold A.effectCotest
  simp only [map_add,map_smul,actedRead,rRead,sampleSupport,contracted]

/-- The complete addressed finite word, including its zero Moebius slots. -/
def dirichletCoefficient (coordinate : BurnolCompletedMellinCoordinate) : ℂ :=
  ∑ n ∈ burnolCenteredMobiusCutoffFinset 4,
    Flux.coefficient n*((n : ℕ) : ℂ)^(1-coordinate.value)

private theorem interior_quarter (coordinate : BurnolCompletedMellinCoordinate) :
    burnolQuarterRestriction (N.interiorBase coordinate)=
      -SingularCounting.powerL2 (OriginalPrimitiveRankBalance.conjugateCoordinate coordinate) := by
  apply Lp.ext
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) (N.interiorBase coordinate),
    ae_restrict_of_ae (N.interior_base_read coordinate),
    Lp.coeFn_neg (SingularCounting.powerL2 (OriginalPrimitiveRankBalance.conjugateCoordinate coordinate)),
    SingularCounting.power_coeFn (OriginalPrimitiveRankBalance.conjugateCoordinate coordinate),
    ae_restrict_mem (measurableSet_symmetricInterval q)] with x restricted raw negative power inside
  rw [show burnolQuarterRestriction (N.interiorBase coordinate) x=N.interiorBase coordinate x from restricted,
    raw,if_pos (show |x|<(4:ℝ) by have h:=abs_le.mpr inside;linarith),negative]
  simp only [Pi.neg_apply]
  rw [power]
  simp only [SingularCounting.powerRaw,OriginalPrimitiveRankBalance.conjugateCoordinate,star_star]

/-- Each actual pullback is evaluated before the finite word is summed. -/
private theorem interior_cell (coordinate : BurnolCompletedMellinCoordinate) (n : ℕ+) :
    cell n (N.interiorBase coordinate)=
      (((n : ℕ) : ℂ)^(1-coordinate.value)) • N.interiorBase coordinate-
        Flux.actualMean (N.interiorBase coordinate) • F.box 4 := by
  have np : 0<((n : ℕ) : ℝ) := by exact_mod_cast n.pos
  have one : (1:ℝ)≤((n : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr n.pos)
  have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ => x/((n : ℕ) : ℝ)) volume volume := by
    simpa only [smul_eq_mul,div_eq_mul_inv,mul_comm] using
      Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := (((n : ℕ) : ℝ))⁻¹) (inv_ne_zero np.ne')
  have moved:=qmp.ae_eq (N.interior_base_read coordinate)
  apply Lp.ext
  filter_upwards [cell_read n (N.interiorBase coordinate),moved,N.interior_base_read coordinate,
    Lp.coeFn_sub ((((n : ℕ) : ℂ)^(1-coordinate.value)) • N.interiorBase coordinate)
      (Flux.actualMean (N.interiorBase coordinate) • F.box 4),
    Lp.coeFn_smul (((n : ℕ) : ℂ)^(1-coordinate.value)) (N.interiorBase coordinate),
    Lp.coeFn_smul (Flux.actualMean (N.interiorBase coordinate)) (F.box 4),
    FiniteMobiusResolventFlux.box_read 4,volume.ae_ne (4:ℝ),volume.ae_ne (-4:ℝ)]
    with x source moved raw subtraction scalar mean box notFour notNegFour
  rw [source,subtraction,Pi.sub_apply,scalar,mean]
  change (symmetricInterval 4).indicator
    (fun x => N.interiorBase coordinate (x/(n:ℕ))-Flux.actualMean (N.interiorBase coordinate)) x=
    (((n : ℕ) : ℂ)^(1-coordinate.value))*N.interiorBase coordinate x-
      Flux.actualMean (N.interiorBase coordinate)*F.box 4 x
  rw [raw,box]
  simp only [Function.comp_def] at moved
  by_cases inside : |x|<(4:ℝ)
  · have small : |x/((n : ℕ) : ℝ)|<(4:ℝ) := by
      rw [abs_div,abs_of_pos np,div_lt_iff₀ np]
      nlinarith
    rw [indicator_of_mem (show x∈symmetricInterval 4 from abs_le.mp inside.le),
      indicator_of_mem (show x∈symmetricInterval 4 from abs_le.mp inside.le),
      if_pos inside,moved,if_pos small,abs_div,abs_of_pos np,Complex.ofReal_div,
      Complex.div_cpow_ofReal_nonneg (abs_nonneg x) np.le]
    rw [show 1-coordinate.value=-(coordinate.value-1) by ring,Complex.cpow_neg]
    push_cast
    ring
  · have outside : x∉symmetricInterval 4 := by
      intro bound
      have same : |x|=4 := le_antisymm (abs_le.mpr bound) (le_of_not_gt inside)
      rcases eq_or_eq_neg_of_abs_eq same with same | same
      · exact notFour same
      · exact notNegFour same
    rw [indicator_of_notMem outside,indicator_of_notMem outside,if_neg inside,mul_zero,mul_zero,sub_self]

/-- Actual M action on the original power carrier, with the complete mean wall. -/
theorem actual_unit_word (coordinate : BurnolCompletedMellinCoordinate) :
    Flux.M (N.interiorBase coordinate)=
      dirichletCoefficient coordinate • N.interiorBase coordinate-
        (N.sigma*Flux.actualMean (N.interiorBase coordinate)) • F.box 4 := by
  rw [Flux.lower_source_cutoff]
  change (∑ n ∈ burnolCenteredMobiusCutoffFinset 4,Flux.coefficient n • cell n (N.interiorBase coordinate))=_
  simp_rw [interior_cell,smul_sub,smul_smul]
  rw [Finset.sum_sub_distrib,←Finset.sum_smul,←Finset.sum_smul,←Finset.sum_mul]
  rfl

private theorem extension_power_read (coordinate : BurnolCompletedMellinCoordinate) :
    (burnolQuarterZeroExtension (SingularCounting.powerL2 coordinate) : ℝ→ℂ)=ᵐ[volume]
      (symmetricInterval q).indicator (SingularCounting.powerRaw coordinate) := by
  have source:=(ae_restrict_iff' (measurableSet_symmetricInterval q)).mp
    (SingularCounting.power_coeFn coordinate)
  filter_upwards [burnolRadiusZeroExtension_coe (SingularCounting.powerL2 coordinate),source]
    with x extended raw
  change (burnolQuarterZeroExtension (SingularCounting.powerL2 coordinate) : ℝ→ℂ) x=_ at extended
  rw [extended]
  by_cases inside : x∈symmetricInterval q
  · rw [indicator_of_mem inside,indicator_of_mem inside,raw inside]
  · rw [indicator_of_notMem inside,indicator_of_notMem inside]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "p" => Flux.primitiveSource observation nontrivial half
local notation "K" => OriginalKCombCofinalTwoDirection.originalK observation nontrivial half
local notation "aa" => Flux.sourceA observation

/-- The signed phase comes from the actual dilation, not an identified scalar readout. -/
theorem actual_unit_window : primitiveUnitWindow observation nontrivial half=
    -(fourierPrimitivePhase observation nontrivial half spread) • N.interiorBase c := by
  let scale : ℝ := Real.exp spread
  have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ => scale*x) volume volume := by
    simpa only [smul_eq_mul,scale] using
      Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := Real.exp spread) (Real.exp_ne_zero spread)
  have moved:=qmp.ae_eq
    (extension_power_read (OriginalPrimitiveRankBalance.conjugateCoordinate c))
  have radius : scale*4=q := by
    have original:=spread_radius
    rw [Real.exp_neg] at original
    dsimp [scale]
    field_simp at original ⊢
    nlinarith
  have phase : (Real.exp (spread/2):ℂ)*(Real.exp spread:ℂ)^
      ((OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).value-1)=
      fourierPrimitivePhase observation nontrivial half spread := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero spread)),
      ←Complex.ofReal_log (le_of_lt (Real.exp_pos spread)),Real.log_exp,Complex.ofReal_exp,
      ←Complex.exp_add]
    unfold fourierPrimitivePhase primitivePhase frequency
    congr 1
    push_cast
    ring
  apply Lp.ext
  filter_upwards [burnolMultiplicativeDilation_coeFn spread
      (burnolQuarterZeroExtension (SingularCounting.powerL2 (OriginalPrimitiveRankBalance.conjugateCoordinate c))),
    moved,Lp.coeFn_smul (-(fourierPrimitivePhase observation nontrivial half spread)) (N.interiorBase c),
    N.interior_base_read c,volume.ae_ne (4:ℝ),volume.ae_ne (-4:ℝ)]
    with x dilated source scalar target notFour notNegFour
  change burnolMultiplicativeDilation spread
    (burnolQuarterZeroExtension (SingularCounting.powerL2 (OriginalPrimitiveRankBalance.conjugateCoordinate c))) x=_
  rw [dilated,scalar]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [target]
  unfold burnolL2RawNormalizedDilation
  change (Real.exp (spread/2):ℂ)*
      (burnolQuarterZeroExtension (SingularCounting.powerL2 (OriginalPrimitiveRankBalance.conjugateCoordinate c))) (scale*x)=_
  simp only [Function.comp_def] at source
  rw [source]
  have membership : scale*x∈symmetricInterval q ↔ |x|≤4 := by
    change (-q≤scale*x ∧ scale*x≤q) ↔ |x|≤4
    rw [←abs_le,abs_mul,abs_of_pos (show 0<scale from Real.exp_pos spread),←radius]
    exact mul_le_mul_iff_right₀ (show 0<scale from Real.exp_pos spread)
  by_cases inside : |x|<4
  · rw [indicator_of_mem (membership.mpr inside.le),if_pos inside]
    simp only [SingularCounting.powerRaw,OriginalPrimitiveRankBalance.conjugateCoordinate,star_star,
      abs_mul,abs_of_pos (show 0<scale from Real.exp_pos spread)]
    rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (le_of_lt (show 0<scale from Real.exp_pos spread)) (abs_nonneg x),
      ←mul_assoc,phase]
    ring
  · have outside : ¬|x|≤4 := by
      intro bound
      have same : |x|=4 := le_antisymm bound (le_of_not_gt inside)
      rcases eq_or_eq_neg_of_abs_eq same with same | same
      · exact notFour same
      · exact notNegFour same
    rw [indicator_of_notMem (fun h=>outside (membership.mp h)),if_neg inside,mul_zero,mul_zero]

private theorem mean_quarter (value : BurnolL2) :
    Flux.actualMean value=burnolQuarterMeanCoefficient (burnolQuarterRestriction value) := by
  change (‖intervalConstant q‖^2 : ℂ)⁻¹*inner ℂ (intervalConstant q) (burnolQuarterRestriction value)=
    inner ℂ (intervalConstant q) (burnolQuarterRestriction value)/((‖intervalConstant q‖^2 : ℝ):ℂ)
  rw [Complex.ofReal_pow]
  ring

private theorem actual_mean_wall :
    aa*Flux.actualMean (Flux.Rplus (observation.coordinate/2) (FL K))=
      aa*(2*Flux.actualMean (FL K)/(1-observation.coordinate))-
        primitiveUnitCoefficient observation nontrivial half*Flux.actualMean (N.interiorBase c) := by
  have source:=Flux.original_return_source_equation observation nontrivial half
  rw [OriginalKCombCofinalRAction.original_R_direct] at source
  have transformed:=congrArg FL source
  simp only [map_smul,map_sub] at transformed
  rw [FiniteMobiusResolventFlux.fourier_R _
    (OriginalKCombCofinalRAction.parameter_rightQuarter observation half)] at transformed
  have actual:=congrArg Flux.actualMean transformed
  simp only [map_sub,map_smul,smul_eq_mul] at actual
  have quarter:=primitive_fourier_quarter observation nontrivial half
  have mean:=congrArg burnolQuarterMeanCoefficient quarter
  simp only [mean_add,mean_smul] at mean
  have innerUnit:=congrArg burnolQuarterMeanCoefficient (interior_quarter c)
  rw [show burnolQuarterMeanCoefficient
      (-SingularCounting.powerL2 (OriginalPrimitiveRankBalance.conjugateCoordinate c))=
      -burnolQuarterMeanCoefficient (SingularCounting.powerL2 (OriginalPrimitiveRankBalance.conjugateCoordinate c)) by
        simp only [burnolQuarterMeanCoefficient,inner_neg_right,neg_div]] at innerUnit
  rw [←mean_quarter] at innerUnit
  rw [←mean_quarter] at mean
  have parameter:=OriginalKCombCofinalTwoDirection.coordinate_value observation nontrivial half
  have kappa : primitiveQuarterConstant observation nontrivial half=
      aa*(2*Flux.actualMean (FL K)/(1-observation.coordinate))-Flux.actualMean (FL K) := by
    simp only [primitiveQuarterConstant,OriginalPrimitiveRankBalance.conjugateCoordinate,star_star,parameter]
  rw [kappa] at mean
  have unitMean : burnolQuarterMeanCoefficient (intervalConstant q)=1 :=
    mean_constant
  rw [unitMean,mul_one] at mean
  linear_combination actual+mean+
    (primitiveUnitCoefficient observation nontrivial half)*innerUnit

/-- No tail is discarded: this is the full same-FK finite coefficient and its unit wall. -/
def jointUnitCoefficient : ℂ :=
  -(primitiveUnitCoefficient observation nontrivial half*dirichletCoefficient c+
    aa*(2*N.exteriorMoment c (FL K)+N.sigma*Flux.actualMean (FL K)*
      (2*(4:ℂ)^(1-observation.coordinate)/(1-observation.coordinate))))

/-- The original power word and the complete same-source reverse mean wall settle together. -/
theorem actual_unit_wall_field :
    primitiveUnitCoefficient observation nontrivial half • Flux.M (primitiveUnitWindow observation nontrivial half)-
      (fourierPrimitivePhase observation nontrivial half spread*aa) •
        Flux.defectFlux (observation.coordinate/2) K=
      fourierPrimitivePhase observation nontrivial half spread •
        (jointUnitCoefficient observation nontrivial half • N.interiorBase c+
          aa • Tate (N.actualFlux (observation.coordinate/2) K)) := by
  let physical : BurnolPaAmbientCarrier :=
    evenFaceFourierEquiv burnolUnscaledCommonGapRadius (burnolCompletedMellinRieszVector c)
  have reverse:=N.source_reverse_flux_three_base c physical
  have parameter:=OriginalKCombCofinalTwoDirection.coordinate_value observation nontrivial half
  change FiniteMobiusResolventFlux.reverseFlux
    ((OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).value/2) (FL K)=
      N.reverseRankSource c (FL K) at reverse
  rw [parameter] at reverse
  rw [actual_unit_window,map_smul,actual_unit_word,FiniteMobiusResolventFlux.defectFlux,reverse]
  unfold N.reverseRankSource
  rw [OriginalPrimitiveRankBalance.box_Rplus_source]
  unfold OriginalPrimitiveRankBalance.boxSource
  simp only [parameter]
  have wall:=actual_mean_wall observation nontrivial half
  unfold jointUnitCoefficient
  linear_combination (norm := module)
    (fourierPrimitivePhase observation nontrivial half spread*N.sigma) •
      congrArg (fun scalar : ℂ => scalar • F.box 4) wall

private theorem outer_pair_zero (value test : BurnolL2)
    (support : F.cutoff (1/2) test=test) : inner ℂ (N.outerCut value) test=0 := by
  have testRead:=FiniteMobiusResolventFlux.cutoff_read (1/2) test
  rw [support] at testRead
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [Lp.coeFn_sub value (F.cutoff 4 value),
    FiniteMobiusResolventFlux.cutoff_read 4 value,testRead] with x subtraction cut source
  simp only [RCLike.inner_apply,starRingEnd_apply,Pi.zero_apply]
  change test x*star ((value-F.cutoff 4 value : BurnolL2) x)=0
  rw [subtraction,Pi.sub_apply,cut,source]
  by_cases inside : x∈symmetricInterval 4
  · rw [indicator_of_mem inside,sub_self,star_zero,mul_zero]
  · have outside : x∉symmetricInterval (1/2) := by
      intro small
      exact inside ⟨by linarith [small.1],by linarith [small.2]⟩
    rw [indicator_of_notMem outside,zero_mul]

private theorem forward_wall_fee_zero :
    inner ℂ (Tate (N.actualFlux (observation.coordinate/2) K)) (A.effectCotest c)=0 := by
  rw [tate_pair]
  have right:=OriginalKCombCofinalRAction.parameter_rightQuarter observation half
  have source:=N.source_forward_flux_outer (observation.coordinate/2) right
    (burnolCompletedMellinRieszVector c)
  change N.actualFlux (observation.coordinate/2) K=_ at source
  rw [source,inner_neg_left,outer_pair_zero _ _ (tate_effect_supported c),neg_zero]

/-- Full unit plus wall, read only after the actual common source field has been generated. -/
theorem actual_unit_wall_fee :
    inner ℂ (primitiveUnitCoefficient observation nontrivial half •
      Flux.M (primitiveUnitWindow observation nontrivial half)) (A.effectCotest c)-
      star (fourierPrimitivePhase observation nontrivial half spread*aa)*
        inner ℂ (Flux.defectFlux (observation.coordinate/2) K) (A.effectCotest c)=
      star (fourierPrimitivePhase observation nontrivial half spread*
        jointUnitCoefficient observation nontrivial half)*
          inner ℂ (N.interiorBase c) (A.effectCotest c) := by
  have field:=congrArg (fun field : BurnolL2 => inner ℂ field (A.effectCotest c))
    (actual_unit_wall_field observation nontrivial half)
  simp only [inner_sub_left,inner_add_left,inner_smul_left,starRingEnd_apply,
    forward_wall_fee_zero,mul_zero,add_zero] at field
  simp only [inner_smul_left,starRingEnd_apply,star_mul] at field ⊢
  linear_combination field

/-- Direct old-return consumer: all three Psi increments and both original means remain literal. -/
theorem actual_native_return :
    star (returnPhase observation nontrivial half)*Return.returnPrice observation nontrivial half=
      star (primitivePhase observation nontrivial half spread*
        fourierPrimitivePhase observation nontrivial half spread)*
        inner ℂ (kernelWindowSource observation nontrivial half)
          (A.weight c • (burnolAnnulusSamplingL2 (A.positionColumn c) 0+A.reciprocalCotest c))+
      star (returnPhase observation nontrivial half)*A.weight c*meanPrice c-
      star (primitivePhase observation nontrivial half spread*fourierKernelPhase observation spread)*
        inner ℂ (Flux.M (fourierPrimitiveIncrement observation nontrivial half spread)) (A.effectCotest c)-
      star (fourierKernelPhase observation spread*fourierPrimitivePhase observation nontrivial half spread)*
        inner ℂ (-Flux.M (primitiveIncrement observation nontrivial half spread)) (Tate (A.effectCotest c))+
      star (returnPhase observation nontrivial half)*star (jointUnitCoefficient observation nontrivial half)*
        inner ℂ (N.interiorBase c) (A.effectCotest c) := by
  have original:=OriginalWholeDebtRPrimitiveMobiusSource.actual_native_return observation nontrivial half
  have settled:=actual_unit_wall_fee observation nontrivial half
  unfold fourierPrimitiveWindowSource at original
  simp only [inner_sub_left] at original
  unfold returnPhase at original ⊢
  simp only [star_mul] at original settled ⊢
  linear_combination original+
    (star (primitivePhase observation nontrivial half spread)*star (fourierKernelPhase observation spread))*settled

end OriginalWholeDebtRPrimitiveMobiusNativeIncidenceSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
