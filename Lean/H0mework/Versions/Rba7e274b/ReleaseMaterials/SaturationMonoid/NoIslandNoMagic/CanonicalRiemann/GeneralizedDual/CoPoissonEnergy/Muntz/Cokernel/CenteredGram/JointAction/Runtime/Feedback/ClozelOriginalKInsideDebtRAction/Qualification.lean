import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKInsideDebtRAction.Stock
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKInsideDebtRSource
open Complex MeasureTheory SourceGeneratedHilbertCokernel
open scoped InnerProductSpace
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalRieszFiniteSource OriginalRieszFiniteColumns OriginalRieszFinitePairing OriginalPaPhysicalGreen
local instance qualificationInsideDebtAmbientComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
namespace Full
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalCommonInverseForcing.SourceJoint.FullStock
 (meanDebt actual_inside_mean_debt)
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalCommonInverseForcing.SourceJoint
 (upperSeedFactor upperSourceWave upperSourceField upperSourceCorrection actual_upper_common_seed)
end Full
namespace Prior
export OriginalKFiniteForcingQSource (actualFinitePaStock actualFiniteOutsideStock actual_finite_source_character_price)
export OriginalKSourceScaledMaximalResponse (originalForcingPair)
end Prior
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

private theorem cutoff_idempotent (radius : ℝ) (value : BurnolL2) :
 originalPhysicalCutoff radius (originalPhysicalCutoff radius value)=originalPhysicalCutoff radius value := by
 unfold originalPhysicalCutoff
 rw [burnolRadiusRestriction_zeroExtension]

private theorem cutoff_reflection (radius : ℝ) (value : BurnolL2)
 (even : reflectL2 value=value) : reflectL2 (originalPhysicalCutoff radius value)=originalPhysicalCutoff radius value := by
 apply Lp.ext
 have moved:=negMeasurePreserving.quasiMeasurePreserving.ae_eq (originalPhysicalCutoff_coeFn radius value)
 have parity:=Lp.coeFn_compMeasurePreserving value negMeasurePreserving
 change (reflectL2 value : ℝ→ℂ)=ᵐ[volume] (value : ℝ→ℂ) ∘ (fun x=>-x) at parity
 rw [even] at parity
 filter_upwards [Lp.coeFn_compMeasurePreserving (originalPhysicalCutoff radius value) negMeasurePreserving,
   moved,originalPhysicalCutoff_coeFn radius value,parity] with x reflected shifted direct equal
 simp only [Function.comp_def] at shifted equal
 rw [show reflectL2 (originalPhysicalCutoff radius value) x=originalPhysicalCutoff radius value (-x) from reflected,
   shifted,direct]
 have incidence : -x∈symmetricInterval radius ↔ x∈symmetricInterval radius := by
  change -radius≤-x ∧ -x≤radius ↔ -radius≤x ∧ x≤radius
  constructor <;> rintro ⟨lower,upper⟩ <;> constructor <;> linarith
 by_cases inside : x∈symmetricInterval radius
 · rw [Set.indicator_of_mem inside,Set.indicator_of_mem (incidence.mpr inside)]
   exact equal.symm
 · rw [Set.indicator_of_notMem inside,Set.indicator_of_notMem (fun h=>inside (incidence.mp h))]

private theorem position_column_even (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) :
 reflectL2 (positionColumn coordinate h)=positionColumn coordinate h := by
 rw [positionColumn_action,map_sub,map_smul,reflectL2_burnolMultiplicativeDilation]
 have returned : reflectL2 (burnolQuarterZeroExtension
   (OriginalRieszSource.Constructor.returnState coordinate : BurnolQuarterIntervalL2))=
   burnolQuarterZeroExtension (OriginalRieszSource.Constructor.returnState coordinate : BurnolQuarterIntervalL2) := by
  change reflectL2 (burnolRadiusZeroExtension (1/4:ℝ)
    (OriginalRieszSource.Constructor.returnState coordinate : BurnolQuarterIntervalL2))=_
  have returnEven : reflectRestricted (1/4:ℝ)
    (OriginalRieszSource.Constructor.returnState coordinate : BurnolQuarterIntervalL2)=
    (OriginalRieszSource.Constructor.returnState coordinate : BurnolQuarterIntervalL2) :=
    burnolRieszSingleFourierReturn_reflection_fixed coordinate
  rw [burnolRadiusZeroExtension_reflect,returnEven]
  rfl
 have gap : reflectL2 (OriginalRieszSourceGreen.gapState coordinate)=OriginalRieszSourceGreen.gapState coordinate :=
  burnolAmbientEvenPart_even _
 rw [map_add,gap,returned]

/-- Own positive/negative source column supports generate the actual quarter restriction. -/
theorem actual_inside_columns_quarter (h : ℝ) (nonnegative : 0≤h) :
 originalPhysicalCutoff (1/4:ℝ) (actualInsidePosition observation nontrivial half h)=actualInsidePosition observation nontrivial half h ∧
 originalPhysicalCutoff (1/4:ℝ) (actualInsideFourier observation nontrivial half h)=actualInsideFourier observation nontrivial half h := by
 constructor
 · unfold actualInsidePosition
   change FiniteMobiusResolventFlux.cutoff (1/4:ℝ) (_+_)=_
   rw [map_add]
   change originalPhysicalCutoff (1/4:ℝ) _+originalPhysicalCutoff (1/4:ℝ) _=_
   rw [positionColumn_quarter _ h nonnegative,cutoff_idempotent]
 · unfold actualInsideFourier
   change FiniteMobiusResolventFlux.cutoff (1/4:ℝ) (_+_)=_
   rw [map_add]
   change originalPhysicalCutoff (1/4:ℝ) _+originalPhysicalCutoff (1/4:ℝ) _=_
   rw [fourierColumn_negative_quarter _ h nonnegative,cutoff_idempotent]

theorem actual_inside_columns_even (h : ℝ) :
 reflectL2 (actualInsidePosition observation nontrivial half h)=actualInsidePosition observation nontrivial half h ∧
 reflectL2 (actualInsideFourier observation nontrivial half h)=actualInsideFourier observation nontrivial half h := by
 constructor
 · unfold actualInsidePosition
   rw [map_add,position_column_even,cutoff_reflection _ _ (position_column_even _ _)]
 · unfold actualInsideFourier
   rw [map_add,OriginalColumnMomentSource.original_column_even,
    cutoff_reflection _ _ (OriginalColumnMomentSource.original_column_even _ _)]

private theorem tate_quarter_four_zero (value : BurnolL2)
 (supported : originalPhysicalCutoff (1/4:ℝ) value=value) :
 FiniteMobiusResolventFlux.cutoff 4 (burnolTateReciprocalL2 value)=0 := by
 have raw:=originalPhysicalCutoff_coeFn (1/4:ℝ) value
 rw [supported] at raw
 have moved:=burnolTateReciprocalRaw_ae_congr (Lp.memLp value) ((Lp.memLp value).ae_eq raw) raw
 apply Lp.ext
 filter_upwards [FiniteMobiusResolventFlux.cutoff_read 4 (burnolTateReciprocalL2 value),
   burnolTateReciprocalL2_coeFn value,moved,Lp.coeFn_zero ℂ 2 volume,
   volume.ae_ne (0:ℝ),volume.ae_ne (4:ℝ),volume.ae_ne (-4:ℝ)]
   with x cut tate source zero nonzero notFour notNegFour
 rw [cut,zero]
 simp only [Pi.zero_apply]
 by_cases inside : x∈symmetricInterval 4
 · rw [Set.indicator_of_mem inside,tate,source]
   unfold burnolTateReciprocalRaw
   rw [Set.indicator_of_notMem,mul_zero]
   intro inverseInside
   have bound : |x|≤4:=abs_le.mpr inside
   have strict : |x|<4 := lt_of_le_of_ne bound (by
    intro equal
    rcases eq_or_eq_neg_of_abs_eq equal with same | same
    · exact notFour same
    · exact notNegFour same)
   have inverseBound : (|x|)⁻¹≤(1/4:ℝ):=by simpa only [abs_inv] using abs_le.mpr inverseInside
   have greater : (1/4:ℝ)<(|x|)⁻¹ := by
    have inverseOrder:=(inv_lt_inv₀ (by norm_num : (0:ℝ)<4) (abs_pos.mpr nonzero)).mpr strict
    norm_num at inverseOrder
    exact inverseOrder
   exact (not_le_of_gt greater) inverseBound
 · rw [Set.indicator_of_notMem inside]

/-- The literal position column generates a four-unit reciprocal rank response of the original R. -/
theorem actual_position_R_reciprocal_rank (h : ℝ) (nonnegative : 0≤h) :
 FiniteMobiusResolventFlux.cutoff 4 (burnolTateReciprocalL2
   (OriginalKFullSourceRResponse.Op.R observation nontrivial half (actualInsidePosition observation nontrivial half h)))=
 (2*burnolRadiusMellinTailEvaluator 4 (by norm_num)
   (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).value
   (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).rightHalf
   (burnolTateReciprocalL2 (actualInsidePosition observation nontrivial half h))) •
 FiniteMobiusResolventFlux.interiorBase (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) := by
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 have even : reflectL2 (burnolTateReciprocalL2 (actualInsidePosition observation nontrivial half h))=
   burnolTateReciprocalL2 (actualInsidePosition observation nontrivial half h) := by
  rw [←burnolTateReciprocal_reflect,(actual_inside_columns_even observation nontrivial half h).1]
 have source:=FiniteMobiusResolventFlux.cutoff_Rplus_rank coordinate
   (burnolTateReciprocalL2 (actualInsidePosition observation nontrivial half h)) even
 have support:=tate_quarter_four_zero (actualInsidePosition observation nontrivial half h)
   (actual_inside_columns_quarter observation nontrivial half h nonnegative).1
 rw [support] at source
 have right : 1/4<(coordinate.value/2).re := by
  rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]
 have empty : FiniteMobiusResolventFlux.Rplus (coordinate.value/2) 0=0 := by
  unfold FiniteMobiusResolventFlux.Rplus FiniteMobiusResolventFlux.RplusIntegrand
  simp
 rw [empty,sub_zero,←FiniteMobiusResolventFlux.tate_R _ right] at source
 exact source



end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKInsideDebtRSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
