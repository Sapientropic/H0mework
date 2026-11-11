import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKReturnJordanSourceData
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalOutsideVolterraSource.AdjointGapSource
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.SingularCounting
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.PrimitiveRank.Power

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalOutsideVolterraSource
open Complex MeasureTheory Set Filter BurnolPhysicalState
open OriginalKFullAdjointSource OriginalKSourceResolventReconstruction
open OriginalPaPhysicalGreen OriginalRieszFinitePairing.CoPoisson.Ward
open scoped InnerProductSpace
local notation "q" => (1/4:ℝ)
local notation "S" => burnolMeanZeroTruncatedFourier
local instance hQuarterComplete : CompleteSpace BurnolQuarterMeanZeroCarrier := by
  apply IsComplete.completeSpace_coe
  exact burnolQuarterMeanZeroClosedFace.isClosed.isComplete

/-- The whole mean-zero source is the paid L2 power column with its actual source coefficient. -/
def hQuarterField (coordinate : BurnolCompletedMellinCoordinate) : BurnolQuarterMeanZeroCarrier :=
  hQuarterAmplitude coordinate • SingularCounting.centeredPower coordinate

private theorem one_sub_star_ne_zero (coordinate : BurnolCompletedMellinCoordinate) :
    1-star coordinate.value≠0 := by
  intro zero
  have real := congrArg Complex.re zero
  simp only [Complex.sub_re,Complex.one_re,Complex.star_def,Complex.conj_re,Complex.zero_re] at real
  linarith [coordinate.belowOne]

private theorem constant_gap_raw (value : BurnolL2) (gamma : ℂ)
    (gap : burnolQuarterRestriction value=gamma • intervalConstant q) :
    ∀ᵐ x ∂volume, x∈symmetricInterval q → value x=gamma := by
  apply (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) value,
    Lp.coeFn_smul gamma (intervalConstant q),intervalConstant_coeFn q]
    with x restricted scaled constant
  change burnolQuarterRestriction value x=value x at restricted
  rw [gap,scaled] at restricted
  change gamma*intervalConstant q x=value x at restricted
  rw [constant,mul_one] at restricted
  exact restricted.symm

private theorem constant_gap_tail (coordinate : BurnolCompletedMellinCoordinate)
    (value : BurnolL2) (gamma : ℂ)
    (gap : burnolQuarterRestriction value=gamma • intervalConstant q)
    (x : ℝ) (positive : 0<x) (small : x≤q) :
    burnolRadiusMellinTailEvaluator x positive (star coordinate.value)
      (by simpa only [Complex.star_def,Complex.conj_re] using coordinate.rightHalf) value=
      gamma*((q:ℂ)^(1-star coordinate.value)-(x:ℂ)^(1-star coordinate.value))/(1-star coordinate.value)+
        burnolRadiusMellinTailEvaluator q (by norm_num) (star coordinate.value)
          (by simpa only [Complex.star_def,Complex.conj_re] using coordinate.rightHalf) value := by
  let f : ℝ→ℂ := fun t=>(t:ℂ)^(-star coordinate.value)*value t
  have full := burnolRadiusMellinWeight_integrableOn_tail x positive (star coordinate.value)
    (by simpa only [Complex.star_def,Complex.conj_re] using coordinate.rightHalf) value
  have upper := burnolRadiusMellinWeight_integrableOn_tail q (by norm_num) (star coordinate.value)
    (by simpa only [Complex.star_def,Complex.conj_re] using coordinate.rightHalf) value
  have union : Ioc x q ∪ Ioi q=Ioi x := by
    ext t
    simp only [mem_union,mem_Ioc,mem_Ioi]
    constructor
    · rintro (inside|after)
      · exact inside.1
      · exact small.trans_lt after
    · intro after
      by_cases below : t≤q
      · exact Or.inl ⟨after,below⟩
      · exact Or.inr (lt_of_not_ge below)
  have disjoint : Disjoint (Ioc x q) (Ioi q) := by
    apply Set.disjoint_left.mpr
    intro t first second
    exact not_lt_of_ge first.2 second
  have split : (∫ t in Ioi x,f t)=(∫ t in Ioc x q,f t)+∫ t in Ioi q,f t := by
    rw [←union]
    exact setIntegral_union disjoint measurableSet_Ioi
      (full.mono_set (fun _ inside=>inside.1)) upper
  have band : (∫ t in Ioc x q,f t)=gamma*(∫ t:ℝ in x..q,(t:ℂ)^(-star coordinate.value)) := by
    rw [intervalIntegral.integral_of_le small,←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (constant_gap_raw value gamma gap),ae_restrict_mem measurableSet_Ioc]
      with t raw inside
    dsimp only [f]
    rw [raw ⟨by linarith [inside.1],inside.2⟩]
    ring
  have primitive := OriginalPrimitiveRankBalance.source_power_difference (1-star coordinate.value) x q positive small
  rw [show 1-star coordinate.value-1= -star coordinate.value by ring] at primitive
  have powerIntegral : (∫ t:ℝ in x..q,(t:ℂ)^(-star coordinate.value))=
      ((q:ℂ)^(1-star coordinate.value)-(x:ℂ)^(1-star coordinate.value))/(1-star coordinate.value) := by
    apply (eq_div_iff (one_sub_star_ne_zero coordinate)).mpr
    simpa only [mul_comm] using primitive
  rw [burnolRadiusMellinTailEvaluator_eq_integral,burnolRadiusMellinTailEvaluator_eq_integral]
  change (∫ t in Ioi x,f t)=_
  rw [split,band,powerIntegral]
  ring

private theorem conjugate_volterra_quarter (coordinate : BurnolCompletedMellinCoordinate)
    (value : BurnolL2) (gamma : ℂ)
    (gap : burnolQuarterRestriction value=gamma • intervalConstant q)
    (even : reflectL2 value=value) :
    burnolQuarterRestriction (sourceVolterraResolvent (OriginalPrimitiveRankBalance.conjugateCoordinate coordinate) value)=
      (2*gamma/(1-star coordinate.value)) • intervalConstant q+
      (-2*(burnolRadiusMellinTailEvaluator q (by norm_num) (star coordinate.value)
        (by simpa only [Complex.star_def,Complex.conj_re] using coordinate.rightHalf) value+
        gamma*(q:ℂ)^(1-star coordinate.value)/(1-star coordinate.value))) • SingularCounting.powerL2 coordinate := by
  let parameter := OriginalPrimitiveRankBalance.conjugateCoordinate coordinate
  let field := sourceVolterraResolvent parameter value
  let amplitude := -2*(burnolRadiusMellinTailEvaluator q (by norm_num) (star coordinate.value)
    (by simpa only [Complex.star_def,Complex.conj_re] using coordinate.rightHalf) value+
    gamma*(q:ℂ)^(1-star coordinate.value)/(1-star coordinate.value))
  have positiveProfile : ∀ᵐ x:ℝ ∂volume, ∀ positive:0<x, ∀ small:x≤q,
      field x=2*gamma/(1-star coordinate.value)+amplitude*(x:ℂ)^(star coordinate.value-1) := by
    filter_upwards [sourceVolterraResolvent_positive_profile parameter value] with x profile positive small
    have response := profile positive
    change field x= -2*(x:ℂ)^(star coordinate.value-1)*
      burnolRadiusMellinTailEvaluator x positive (star coordinate.value)
        (by simpa only [Complex.star_def,Complex.conj_re] using coordinate.rightHalf) value at response
    rw [response,constant_gap_tail coordinate value gamma gap x positive small]
    have inverse : (x:ℂ)^(star coordinate.value-1)*(x:ℂ)^(1-star coordinate.value)=1 := by
      rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr positive.ne'),
        show (star coordinate.value-1)+(1-star coordinate.value)=0 by ring,Complex.cpow_zero]
    dsimp only [amplitude]
    calc
      _ = (2*gamma/(1-star coordinate.value))*
          ((x:ℂ)^(star coordinate.value-1)*(x:ℂ)^(1-star coordinate.value))+
          (-2*(burnolRadiusMellinTailEvaluator q (by norm_num) (star coordinate.value)
            (by simpa only [Complex.star_def,Complex.conj_re] using coordinate.rightHalf) value+
            gamma*(q:ℂ)^(1-star coordinate.value)/(1-star coordinate.value)))*
              (x:ℂ)^(star coordinate.value-1) := by ring
      _ = _ := by rw [inverse];ring
  have parity := Lp.coeFn_compMeasurePreserving field negMeasurePreserving
  change (reflectL2 field : ℝ→ℂ)=ᵐ[volume] (field : ℝ→ℂ) ∘ (fun x=>-x) at parity
  have fieldEven : reflectL2 field=field := by
    exact (sourceVolterraResolvent_reflect parameter value).trans (congrArg (sourceVolterraResolvent parameter) even)
  rw [fieldEven] at parity
  have negative := negMeasurePreserving.quasiMeasurePreserving.ae positiveProfile
  apply Lp.ext
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) field,
    Lp.coeFn_add ((2*gamma/(1-star coordinate.value)) • intervalConstant q) (amplitude • SingularCounting.powerL2 coordinate),
    Lp.coeFn_smul (2*gamma/(1-star coordinate.value)) (intervalConstant q),
    Lp.coeFn_smul amplitude (SingularCounting.powerL2 coordinate),intervalConstant_coeFn q,
    SingularCounting.power_coeFn coordinate,ae_restrict_of_ae positiveProfile,
    ae_restrict_of_ae negative,ae_restrict_of_ae parity,
    ae_restrict_mem (measurableSet_symmetricInterval q),ae_restrict_of_ae (volume.ae_ne (0:ℝ))]
    with x restricted sumRead constantScale powerScale constant power direct reverse reflected inside nonzero
  change burnolQuarterRestriction field x=field x at restricted
  change burnolQuarterRestriction field x=
    ((2*gamma/(1-star coordinate.value)) • intervalConstant q+amplitude • SingularCounting.powerL2 coordinate) x
  rw [restricted,sumRead]
  change field x=((2*gamma/(1-star coordinate.value)) • intervalConstant q) x+(amplitude • SingularCounting.powerL2 coordinate) x
  rw [constantScale,powerScale]
  change field x=(2*gamma/(1-star coordinate.value))*intervalConstant q x+amplitude*SingularCounting.powerL2 coordinate x
  rw [constant,power]
  rcases lt_or_gt_of_ne nonzero with neg|pos
  · rw [SingularCounting.powerRaw,abs_of_neg neg]
    have read : field x=field (-x) := reflected
    rw [read,reverse (by linarith) (by linarith [inside.1])]
    ring
  · rw [SingularCounting.powerRaw,abs_of_pos pos,direct pos inside.2]
    ring

private theorem generatedK_constant_gap (coordinate : BurnolCompletedMellinCoordinate) :
    burnolQuarterRestriction (generatedK coordinate)=hQuarterGap coordinate • intervalConstant q := by
  have qualified : burnolQuarterRestriction (generatedK coordinate)∈intervalConstantLine q := by
    rw [generatedK_eq_original]
    exact (burnolCompletedMellinRieszVector coordinate).property.1.1
  have centered := (burnolQuarterMeanZeroProjection_eq_zero_iff _).mpr qualified
  rw [burnolMeanZeroProjection_eq_sub_constant] at centered
  exact sub_eq_zero.mp centered

/-- The original adjoint and the source Volterra are identified on the generated two-column source. -/
theorem h_adjoint_full_volterra (coordinate : BurnolCompletedMellinCoordinate) :
    sourceAdjointField coordinate=
      sourceVolterraResolvent (OriginalPrimitiveRankBalance.conjugateCoordinate coordinate) (generatedK coordinate) := by
  rw [generatedK_eq_original,←sourceAdjoint_original]
  exact FiniteMobiusResolventFlux.Rplus_tate (star coordinate.value/2)
    (by rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]) _

/-- Full Volterra source action computes the entire remaining quarter cotest, including its mean subtraction. -/
theorem h_quarter_source (coordinate : BurnolCompletedMellinCoordinate) :
    quarterCotest (sourceAdjointField coordinate)=hQuarterField coordinate := by
  have even : reflectL2 (generatedK coordinate)=generatedK coordinate := by
    rw [generatedK_eq_original]
    exact mem_evenL2ClosedFace_iff.mp (burnolCompletedMellinRieszVector coordinate).property.2
  have source := conjugate_volterra_quarter coordinate (generatedK coordinate) (hQuarterGap coordinate)
    (generatedK_constant_gap coordinate) even
  apply Subtype.ext
  change burnolQuarterMeanZeroProjection (burnolQuarterRestriction (sourceAdjointField coordinate))=_
  rw [h_adjoint_full_volterra,source,map_add,map_smul,map_smul]
  have constantZero : burnolQuarterMeanZeroProjection (intervalConstant q)=0 :=
    (burnolQuarterMeanZeroProjection_eq_zero_iff _).mpr (Submodule.mem_span_singleton_self _)
  rw [constantZero,smul_zero,zero_add]
  rfl

/-- The complete outside price now uses a fixed generated power column and its actual source amplitude. -/
theorem outside_price_from_power_source (coordinate : BurnolCompletedMellinCoordinate)
    (state : BurnolQuarterMeanZeroCarrier) :
    inner ℂ (outsideCotest (sourceAdjointField coordinate)) state=
      -star (hQuarterAmplitude coordinate)*inner ℂ (SingularCounting.centeredPower coordinate) (S state) := by
  rw [outside_price_from_position_source,h_quarter_source,hQuarterField,inner_smul_left]
  simp only [starRingEnd_apply]
  ring

/-- The same original Q born at n+2 consumes the full power source and retains the Q/unit prices. -/
theorem actual_nextQ_power_source (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
    (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat) :
    let coordinate := OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
    let K := (burnolCompletedMellinRieszVector coordinate : BurnolL2)
    inner ℂ K (PA.Q (D.raw observation nontrivial half depth ((ordinal+1)+1)) : BurnolL2)=
      OriginalKDirectRCofinalDivision.sourceCoefficient observation nontrivial half depth (ordinal+1)*
        inner ℂ K (OriginalKDirectRCofinalDivision.sourceUnit observation nontrivial half : BurnolL2)+
      inner ℂ (qAdjointSource coordinate) (D.raw observation nontrivial half depth (ordinal+1))-
      star (hQuarterAmplitude coordinate)*inner ℂ (SingularCounting.centeredPower coordinate)
        (S (sourceOutsideColumn coordinate (D.raw observation nontrivial half depth ordinal))) := by
  dsimp only
  have actual := actual_nextQ_one_channel_source observation nontrivial half depth ordinal
  dsimp only at actual
  rw [h_quarter_source,hQuarterField,inner_smul_left] at actual
  exact actual

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalOutsideVolterraSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
