import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSectorEulerMixedSource.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSectorEulerMixedSource
open Complex MeasureTheory Filter FourierTransform
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local notation "K" => burnolCompletedMellinRieszVector
local instance sectorFootPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

local notation "q" => (1/4:ℝ)
local notation "μ" => FiniteMobiusResolventFlux.actualMean
local notation "s" => OriginalKConstantContactSourceAction.ConstantSource.seed
local notation "U" => OriginalRieszSource.Response.wholeU
local notation "V" => OriginalRieszSource.Response.wholeV

/-- The true positive Rplus source support and source mean precede the physical reader. -/
theorem actual_compact_F_R_right_price (coordinate : BurnolCompletedMellinCoordinate)
 (source : BurnolL2) (compact : originalPhysicalCutoff q source=source)
 (even : reflectL2 source=source) (physical : BurnolPaAmbientCarrier) :
 inner ℂ (physical:BurnolL2) (burnolDirectRightResolvent (coordinate.value/2) (fourierL2 source))=
 -(1/2:ℂ)*star (FiniteMobiusResolventFlux.actualMean (fourierL2 (physical:BurnolL2)))*
  FiniteMobiusResolventFlux.actualMean source/(coordinate.value/2) :=by
 have right:1/4<(coordinate.value/2).re:=by
  rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]
 have support:=OriginalPrimitiveRankBalance.cutoff_Rplus_source q (by norm_num)
  (coordinate.value/2) right source
 change FiniteMobiusResolventFlux.cutoff q source=source at compact
 rw [compact] at support
 have opposite:burnolDirectRightResolvent (coordinate.value/2) (fourierL2 source)=
  fourierL2 (FiniteMobiusResolventFlux.Rplus (coordinate.value/2) source) :=by
  apply fourierL2.injective
  rw [FiniteMobiusResolventFlux.fourier_R _ right,fourierL2_fourierL2,even,
   fourierL2_fourierL2,FiniteMobiusResolventFlux.Rplus_even coordinate source even]
 rw [opposite]
 have twice:fourierL2 (fourierL2 (physical:BurnolL2))=(physical:BurnolL2):=by
  rw [fourierL2_fourierL2]
  exact mem_evenL2ClosedFace_iff.mp physical.property.2
 have moved:=fourierL2.inner_map_map (fourierL2 (physical:BurnolL2))
  (FiniteMobiusResolventFlux.Rplus (coordinate.value/2) source)
 rw [twice] at moved
 rw [moved]
 have price:=paid172QuarterPhysicalPrice
  (evenFaceFourierEquiv burnolUnscaledCommonGapRadius physical)
  (FiniteMobiusResolventFlux.Rplus (coordinate.value/2) source)
 change inner ℂ (fourierL2 (physical:BurnolL2))
  (originalPhysicalCutoff q (FiniteMobiusResolventFlux.Rplus (coordinate.value/2) source))=_ at price
 change originalPhysicalCutoff q (FiniteMobiusResolventFlux.Rplus (coordinate.value/2) source)=_ at support
 rw [support,OriginalKFourierQuarterRplusAction.actual_compact_Rplus_mean_action _ right source compact] at price
 change inner ℂ (fourierL2 (physical:BurnolL2)) (FiniteMobiusResolventFlux.Rplus (coordinate.value/2) source)=
  (1/2:ℂ)*star (FiniteMobiusResolventFlux.actualMean (fourierL2 (physical:BurnolL2)))*
  (-FiniteMobiusResolventFlux.actualMean source/(coordinate.value/2)) at price
 rw [price]
 ring

/-- Only the physical projection vanishes; the same raw R source stock remains. -/
theorem actual_compact_mean_zero_F_R_projection (coordinate : BurnolCompletedMellinCoordinate)
 (source : BurnolL2) (compact : originalPhysicalCutoff q source=source)
 (even : reflectL2 source=source) (meanZero : FiniteMobiusResolventFlux.actualMean source=0) :
 burnolEvenAmbientProjection (burnolDirectRightResolvent (coordinate.value/2) (fourierL2 source))=0 :=by
 apply (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.orthogonalProjectionOnto_eq_zero_iff.mpr
 rw [Submodule.mem_orthogonal']
 intro physical member
 let material:BurnolPaAmbientCarrier:=⟨physical,member⟩
 have price:=actual_compact_F_R_right_price coordinate source compact even material
 rw [meanZero,mul_zero,zero_div] at price
 exact (inner_eq_zero_symm).mpr price


def actualCompactRightPrice (c : BurnolCompletedMellinCoordinate) (source : BurnolL2)
 (physical : BurnolPaAmbientCarrier) : ℂ:=
 (1/2:ℂ)*star (μ (physical:BurnolL2))*
 ((OriginalKCompactAdjointRSource.actualCompactTailCoefficient c source*
  (((2*q:ℝ):ℂ)*(q:ℂ)^(-c.value))-μ source)/(c.value/2-1/2))+
 OriginalKCompactAdjointRSource.actualCompactTailCoefficient c source*
 star (-(2:ℂ)*inner ℂ (K (OriginalKQuarterTailPhysicalSource.actualStarSource c)) physical+
 (2:ℂ)*burnolMellinGapMoment (star c.value)*μ (physical:BurnolL2))

/-- The complete compact R rank is read on the physical receiver's actual right foot. -/
theorem actual_compact_R_right_price (c : BurnolCompletedMellinCoordinate)
 (source : BurnolL2) (compact : originalPhysicalCutoff q source=source)
 (even : reflectL2 source=source) (physical : BurnolPaAmbientCarrier) :
 inner ℂ (physical:BurnolL2) (burnolDirectRightResolvent (c.value/2) source)=
 actualCompactRightPrice c source physical :=by
 have read:=paid172QuarterPhysicalPrice physical
  (burnolDirectRightResolvent (c.value/2) source)
 rw [OriginalKCompactAdjointRSource.actual_compact_R_rank_source c source compact even,
  inner_add_right,inner_smul_right,read,
  OriginalKCompactAdjointRSource.actual_compact_quarter_mean_price c source compact even]
 let dual:=OriginalKQuarterTailPhysicalSource.actualStarSource c
 have tail:=congrArg star (OriginalKCompactAdjointRSource.actual_compact_tail_physical_price dual physical)
 have twice:OriginalKQuarterTailPhysicalSource.actualStarSource dual=c:=by
  unfold dual OriginalKQuarterTailPhysicalSource.actualStarSource
  cases c
  simp only [star_star]
 rw [twice] at tail
 have tailRead:inner ℂ (physical:BurnolL2) (burnolRadiusNormalizedUnitTail c q (by norm_num))=
 star (-(2:ℂ)*inner ℂ (K dual) physical+(2:ℂ)*burnolMellinGapMoment dual.value*μ (physical:BurnolL2)):=by
  calc
   inner ℂ (physical:BurnolL2) (burnolRadiusNormalizedUnitTail c q (by norm_num))=
    star (inner ℂ (burnolRadiusNormalizedUnitTail c q (by norm_num)) (physical:BurnolL2)) :=
     (inner_conj_symm (physical:BurnolL2) (burnolRadiusNormalizedUnitTail c q (by norm_num))).symm
   _=_:=tail
 rw [tailRead]
 rfl

/-- Own mean-zero quarter source generates its zero Fourier R projection. -/
theorem actual_quarter_mean_zero_source (source : BurnolQuarterMeanZeroCarrier) :
 μ (burnolQuarterZeroExtension (source:BurnolQuarterIntervalL2))=0 :=by
 change ((‖intervalConstant q‖:ℂ)^2)⁻¹*inner ℂ (intervalConstant q)
  (burnolRadiusRestriction q (burnolRadiusZeroExtension q (source:BurnolQuarterIntervalL2)))=0
 rw [burnolRadiusRestriction_zeroExtension]
 have zero:inner ℂ (intervalConstant q) (source:BurnolQuarterIntervalL2)=0 :=
  (Submodule.mem_orthogonal _ _).mp source.property _ (Submodule.mem_span_singleton_self _)
 rw [zero,mul_zero]

theorem actual_original_UV_F_R_projection (c : BurnolCompletedMellinCoordinate) :
 burnolEvenAmbientProjection (burnolDirectRightResolvent (c.value/2) (fourierL2 U))=0 ∧
 burnolEvenAmbientProjection (burnolDirectRightResolvent (c.value/2) (fourierL2 V))=0 :=by
 have source:=OriginalKCompactAdjointRSource.actual_original_UV_compact_even
 exact ⟨actual_compact_mean_zero_F_R_projection c U source.1 source.2.1
  (actual_quarter_mean_zero_source OriginalRieszSource.Response.u),
  actual_compact_mean_zero_F_R_projection c V source.2.2.1 source.2.2.2
  (actual_quarter_mean_zero_source OriginalRieszSource.Response.v)⟩

theorem actual_seed_source_qualification :
 originalPhysicalCutoff q s=s ∧ reflectL2 s=s ∧ μ s=1 :=by
 constructor
 · change burnolRadiusZeroExtension q (burnolRadiusRestriction q (burnolRadiusZeroExtension q (intervalConstant q)))=_
   rw [burnolRadiusRestriction_zeroExtension]
   rfl
 constructor
 · exact OriginalKGapProjectionEulerSource.actual_seed_even
 · change ((‖intervalConstant q‖:ℂ)^2)⁻¹*inner ℂ (intervalConstant q)
    (burnolRadiusRestriction q (burnolRadiusZeroExtension q (intervalConstant q)))=1
   rw [burnolRadiusRestriction_zeroExtension]
   have normSource:((‖intervalConstant q‖:ℝ):ℂ)^2=(1/2:ℂ):=by
    have native:=burnolIntervalConstant_norm_sq (by norm_num:(0:ℝ)<q)
    norm_num at native
    exact native
   have actualSelf:inner ℂ (intervalConstant q) (intervalConstant q)=(1/2:ℂ):=by
    rw [L2.inner_def]
    have raw:(fun x:ℝ=>inner ℂ (intervalConstant q x) (intervalConstant q x))=ᵐ[
     volume.restrict (symmetricInterval q)] fun _=>(1:ℂ):=by
     filter_upwards [intervalConstant_coeFn q] with x read
     rw [read]
     simp
    rw [integral_congr_ae raw,integral_const]
    norm_num [symmetricInterval,real_smul]
   rw [normSource,actualSelf]
   norm_num

def actualSeedRightPrice (c : BurnolCompletedMellinCoordinate) (physical : BurnolPaAmbientCarrier) : ℂ:=
 actualCompactRightPrice c s physical

def actualFourierSeedRightPrice (c : BurnolCompletedMellinCoordinate) (physical : BurnolPaAmbientCarrier) : ℂ:=
 -(1/2:ℂ)*star (μ (fourierL2 (physical:BurnolL2)))/(c.value/2)

theorem actual_original_seed_R_right_prices (c : BurnolCompletedMellinCoordinate) (physical : BurnolPaAmbientCarrier) :
 inner ℂ (physical:BurnolL2) (burnolDirectRightResolvent (c.value/2) s)=actualSeedRightPrice c physical ∧
 inner ℂ (physical:BurnolL2) (burnolDirectRightResolvent (c.value/2) (fourierL2 s))=actualFourierSeedRightPrice c physical :=by
 have source:=actual_seed_source_qualification
 constructor
 · exact actual_compact_R_right_price c s source.1 source.2.1 physical
 · have generated:=actual_compact_F_R_right_price c s source.1 source.2.1 physical
   rw [source.2.2,mul_one] at generated
   exact generated

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSectorEulerMixedSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
