import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKInsideDebtRAction.Qualification
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
local instance actionInsideDebtAmbientComplete : CompleteSpace BurnolPaAmbientCarrier := by
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

private theorem reciprocal_four_quarter_split (value : BurnolL2) :
 burnolTateReciprocalL2 (FiniteMobiusResolventFlux.cutoff 4 (burnolTateReciprocalL2 value))=
 value-originalPhysicalCutoff (1/4:ℝ) value := by
 classical
 have raw : ((value-originalPhysicalCutoff (1/4:ℝ) value : BurnolL2) : ℝ→ℂ)=ᵐ[volume]
   fun x=>if x∈symmetricInterval (1/4:ℝ) then 0 else value x := by
  filter_upwards [Lp.coeFn_sub value (originalPhysicalCutoff (1/4:ℝ) value),
    originalPhysicalCutoff_coeFn (1/4:ℝ) value] with x subtraction cut
  rw [subtraction,Pi.sub_apply,cut]
  by_cases inside : x∈symmetricInterval (1/4:ℝ)
  · rw [Set.indicator_of_mem inside,if_pos inside,sub_self]
  · rw [Set.indicator_of_notMem inside,if_neg inside,sub_zero]
 have moved:=burnolTateReciprocalRaw_ae_congr
   (Lp.memLp (value-originalPhysicalCutoff (1/4:ℝ) value))
   ((Lp.memLp (value-originalPhysicalCutoff (1/4:ℝ) value)).ae_eq raw) raw
 have dual : FiniteMobiusResolventFlux.cutoff 4 (burnolTateReciprocalL2 value)=
   burnolTateReciprocalL2 (value-originalPhysicalCutoff (1/4:ℝ) value) := by
  apply Lp.ext
  filter_upwards [FiniteMobiusResolventFlux.cutoff_read 4 (burnolTateReciprocalL2 value),
    burnolTateReciprocalL2_coeFn value,
    burnolTateReciprocalL2_coeFn (value-originalPhysicalCutoff (1/4:ℝ) value),
    moved,volume.ae_ne (0:ℝ),volume.ae_ne (4:ℝ),volume.ae_ne (-4:ℝ)]
    with x cut source tate exterior nonzero notFour notNegFour
  rw [cut,tate,exterior]
  have incidence : x∈symmetricInterval 4 ↔ x⁻¹∉symmetricInterval (1/4:ℝ) := by
   have neq : |x|≠4 := by
    intro equal
    rcases eq_or_eq_neg_of_abs_eq equal with same | same
    · exact notFour same
    · exact notNegFour same
   have positive:=abs_pos.mpr nonzero
   constructor
   · intro inside inverseInside
     have bound : |x|<4:=lt_of_le_of_ne (abs_le.mpr inside) neq
     have inverseOrder:=(inv_lt_inv₀ (by norm_num : (0:ℝ)<4) positive).mpr bound
     norm_num at inverseOrder
     have inverseBound : (|x|)⁻¹≤(1/4:ℝ):=by simpa only [abs_inv] using abs_le.mpr inverseInside
     exact (not_le_of_gt inverseOrder) inverseBound
   · intro outside
     by_contra notInside
     have greater : 4 < |x| :=lt_of_not_ge (fun bound=>notInside (abs_le.mp bound))
     have inverseOrder:=(inv_lt_inv₀ positive (by norm_num : (0:ℝ)<4)).mpr greater
     norm_num at inverseOrder
     apply outside
     apply abs_le.mp
     simpa only [abs_inv] using inverseOrder.le
  by_cases inside : x∈symmetricInterval 4
  · rw [Set.indicator_of_mem inside,source]
    unfold burnolTateReciprocalRaw
    dsimp only
    rw [if_neg (incidence.mp inside)]
  · rw [Set.indicator_of_notMem inside]
    unfold burnolTateReciprocalRaw
    dsimp only
    rw [if_pos (by by_contra outside;exact inside (incidence.mpr outside)),mul_zero]
 rw [dual,burnolTateReciprocalL2_involutive]

/-- The actual R response has its native quarter residual plus a source-generated normalized quarter-unit tail. -/
theorem actual_position_R_rank_decomposition (h : ℝ) (nonnegative : 0≤h) :
 OriginalKFullSourceRResponse.Op.R observation nontrivial half (actualInsidePosition observation nontrivial half h)=
 originalPhysicalCutoff (1/4:ℝ)
   (OriginalKFullSourceRResponse.Op.R observation nontrivial half (actualInsidePosition observation nontrivial half h))+
 (2*burnolRadiusMellinTailEvaluator 4 (by norm_num)
   (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).value
   (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).rightHalf
   (burnolTateReciprocalL2 (actualInsidePosition observation nontrivial half h))) •
 burnolRadiusNormalizedUnitTail (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) (1/4:ℝ) (by norm_num) := by
 have source:=congrArg burnolTateReciprocalL2
   (actual_position_R_reciprocal_rank observation nontrivial half h nonnegative)
 rw [reciprocal_four_quarter_split,map_smul,FiniteMobiusResolventFlux.interiorBase,
   burnolTateReciprocalL2_involutive] at source
 linear_combination (norm:=module) source

/-- The same literal Fourier column drives the opposite Rplus direction; its source support remains quarter-sized. -/
theorem actual_fourier_Rplus_quarter (h : ℝ) (nonnegative : 0≤h) :
 originalPhysicalCutoff (1/4:ℝ)
   (FiniteMobiusResolventFlux.Rplus
     ((OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).value/2)
     (actualInsideFourier observation nontrivial half h))=
 FiniteMobiusResolventFlux.Rplus
   ((OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).value/2)
   (actualInsideFourier observation nontrivial half h) := by
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 have right : 1/4<(coordinate.value/2).re := by
  rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]
 have source:=OriginalPrimitiveRankBalance.cutoff_Rplus_source (1/4:ℝ) (by norm_num)
   (coordinate.value/2) right (actualInsideFourier observation nontrivial half h)
 have support:= (actual_inside_columns_quarter observation nontrivial half h nonnegative).2
 change FiniteMobiusResolventFlux.cutoff (1/4:ℝ) (actualInsideFourier observation nontrivial half h)=_ at support
 rw [support] at source
 exact source

/-- Actual Fourier parity and the paid opposite-direction action generate this response; no R/F commutation is assumed. -/
theorem actual_fourier_R_opposite_action (h : ℝ) :
 OriginalKFullSourceRResponse.Op.R observation nontrivial half (fourierL2 (actualInsideFourier observation nontrivial half h))=
 fourierL2 (FiniteMobiusResolventFlux.Rplus
   ((OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).value/2)
   (actualInsideFourier observation nontrivial half h)) := by
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 have right : 1/4<(coordinate.value/2).re := by
  rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]
 have even:=(actual_inside_columns_even observation nontrivial half h).2
 have oppositeEven:=FiniteMobiusResolventFlux.Rplus_even coordinate
   (actualInsideFourier observation nontrivial half h) even
 apply fourierL2.injective
 change fourierL2 (burnolDirectRightResolvent (coordinate.value/2)
   (fourierL2 (actualInsideFourier observation nontrivial half h)))=_
 rw [FiniteMobiusResolventFlux.fourier_R _ right,fourierL2_fourierL2,even,
   fourierL2_fourierL2,oppositeEven]


def actualPositionTailCoefficient (h : ℝ) : ℂ :=
 2*burnolRadiusMellinTailEvaluator 4 (by norm_num)
   (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).value
   (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).rightHalf
   (burnolTateReciprocalL2 (actualInsidePosition observation nontrivial half h))

def actualInsideNativeREffect (h : ℝ) : BurnolL2 :=
 originalPhysicalCutoff (1/4:ℝ)
   (OriginalKFullSourceRResponse.Op.R observation nontrivial half (actualInsidePosition observation nontrivial half h))+
 actualPositionTailCoefficient observation nontrivial half h •
   burnolRadiusNormalizedUnitTail (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) (1/4:ℝ) (by norm_num)+
 fourierL2 (FiniteMobiusResolventFlux.Rplus
   ((OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).value/2)
   (actualInsideFourier observation nontrivial half h))+
 OriginalKFullSourceRResponse.Op.R observation nontrivial half
   (Full.meanDebt (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h : BurnolL2)

/-- The full inside effect actually consumes the source rank and opposite-direction responses while retaining the two means. -/
theorem actual_complete_inside_R_action (h : ℝ) (nonnegative : 0≤h) :
 insideDebtREffect observation nontrivial half h=actualInsideNativeREffect observation nontrivial half h := by
 unfold insideDebtREffect actualInsideNativeREffect actualPositionTailCoefficient
 rw [actual_fourier_R_opposite_action observation nontrivial half h]
 exact congrArg (fun material : BurnolL2=>material+
   fourierL2 (FiniteMobiusResolventFlux.Rplus
     ((OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).value/2)
     (actualInsideFourier observation nontrivial half h))+
   OriginalKFullSourceRResponse.Op.R observation nontrivial half
     (Full.meanDebt (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h : BurnolL2))
   (actual_position_R_rank_decomposition observation nontrivial half h nonnegative)


end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKInsideDebtRSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
