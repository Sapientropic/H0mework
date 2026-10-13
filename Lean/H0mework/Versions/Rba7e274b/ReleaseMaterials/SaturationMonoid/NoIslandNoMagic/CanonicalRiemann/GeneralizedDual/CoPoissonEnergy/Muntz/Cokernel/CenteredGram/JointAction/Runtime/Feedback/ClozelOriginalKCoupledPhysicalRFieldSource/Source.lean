import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSectorEulerMixedSource.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCoupledPhysicalRFieldSource
open Complex MeasureTheory Filter FourierTransform
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local notation "K" => burnolCompletedMellinRieszVector
local instance coupledPhysicalFieldComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

namespace Paid
export OriginalKSectorEulerMixedSource (actual_seed_source_qualification actual_original_UV_F_R_projection)
end Paid
local notation "P" => burnolEvenAmbientProjection
local notation "G" => OriginalRieszFiniteSynthesis.gapMeanVector
local notation "q" => (1/4:ℝ)
local notation "μ" => FiniteMobiusResolventFlux.actualMean
local notation "s" => OriginalKConstantContactSourceAction.ConstantSource.seed
local notation "U" => OriginalRieszSource.Response.wholeU
local notation "V" => OriginalRieszSource.Response.wholeV

/-- The already-paid quarter reader and original G readback generate the complete projected quarter field. -/
theorem actual_quarter_projected_field (source : BurnolL2) :
 P (originalPhysicalCutoff q source)=(μ source/2) • G :=by
 apply ext_inner_right ℂ
 intro physical
 have read:=(evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule
  |>.inner_orthogonalProjectionOnto_eq_of_mem_right physical (originalPhysicalCutoff q source)
 change inner ℂ (P (originalPhysicalCutoff q source)) physical=
  inner ℂ (originalPhysicalCutoff q source) (physical:BurnolL2) at read
 rw [read,inner_smul_left,OriginalRieszFiniteSynthesis.gapMeanVector_readback,←FiniteMobiusResolventFlux.actual_mean_physical]
 have quarter:=congrArg star (paid172QuarterPhysicalPrice physical source)
 have actual:inner ℂ (originalPhysicalCutoff q source) (physical:BurnolL2)=
  star ((1/2:ℂ)*star (μ (physical:BurnolL2))*μ source):=by
  exact ((inner_conj_symm (originalPhysicalCutoff q source) (physical:BurnolL2)).symm).trans quarter
 rw [actual]
 simp only [star_mul,star_div₀,star_ofNat,star_one,star_star,starRingEnd_apply]
 ring

/-- The actual constant projects to the original G with its paid half unit. -/
theorem actual_seed_projected_field : P s=(1/2:ℂ) • G :=by
 have source:=actual_quarter_projected_field s
 rw [Paid.actual_seed_source_qualification.1,Paid.actual_seed_source_qualification.2.2] at source
 exact source

/-- The original Fourier seed uses the existing signed lower P/F law, not a new projection exchange. -/
theorem actual_Fourier_seed_projected_field : P (fourierL2 s)=(1/2:ℂ) • Fphysical G :=by
 apply Subtype.ext
 have source:=fourierL2_evenBurnolPhysicalProjection burnolUnscaledCommonGapRadius s
 change fourierL2 (P s:BurnolL2)=(P (fourierL2 s):BurnolL2) at source
 rw [actual_seed_projected_field] at source
 change fourierL2 ((1/2:ℂ) • (G:BurnolL2))=(P (fourierL2 s):BurnolL2) at source
 rw [map_smul] at source
 exact source.symm

def actualCompactProjectedRField (c : BurnolCompletedMellinCoordinate) (source : BurnolL2) : BurnolPaAmbientCarrier:=
 -(2*OriginalKCompactAdjointRSource.actualCompactTailCoefficient c source) •
  K (OriginalKQuarterTailPhysicalSource.actualStarSource c)+
 ((1/2:ℂ)*((OriginalKCompactAdjointRSource.actualCompactTailCoefficient c source*
  (((2*q:ℝ):ℂ)*(q:ℂ)^(-c.value))-μ source)/(c.value/2-1/2))+
 (2:ℂ)*OriginalKCompactAdjointRSource.actualCompactTailCoefficient c source*
  star (burnolMellinGapMoment (OriginalKQuarterTailPhysicalSource.actualStarSource c).value)) • G

/-- Actual compact R rank, its actual quarter mean and the paid whole qtail projection generate the full physical R field. -/
theorem actual_compact_projected_R_source (c : BurnolCompletedMellinCoordinate)
 (source : BurnolL2) (compact : originalPhysicalCutoff q source=source) (even : reflectL2 source=source) :
 P (burnolDirectRightResolvent (c.value/2) source)=actualCompactProjectedRField c source :=by
 rw [OriginalKCompactAdjointRSource.actual_compact_R_rank_source c source compact even,map_add,map_smul,
  actual_quarter_projected_field,OriginalKCompactAdjointRSource.actual_compact_quarter_mean_price c source compact even,
  OriginalKQuarterTailPhysicalSource.actual_quarter_tail_physical_source]
 unfold actualCompactProjectedRField OriginalKCompactAdjointRSource.actualCompactTailCoefficient
 module

theorem actual_original_UV_projected_R_fields (c : BurnolCompletedMellinCoordinate) :
 P (burnolDirectRightResolvent (c.value/2) U)=actualCompactProjectedRField c U ∧
 P (burnolDirectRightResolvent (c.value/2) V)=actualCompactProjectedRField c V ∧
 P (burnolDirectRightResolvent (c.value/2) (fourierL2 U))=0 ∧
 P (burnolDirectRightResolvent (c.value/2) (fourierL2 V))=0 :=by
 have source:=OriginalKCompactAdjointRSource.actual_original_UV_compact_even
 have Fourier:=Paid.actual_original_UV_F_R_projection c
 exact ⟨actual_compact_projected_R_source c U source.1 source.2.1,
  actual_compact_projected_R_source c V source.2.2.1 source.2.2.2,Fourier.1,Fourier.2⟩

/-- Both seed responses are generated as complete physical fields; their raw R fields remain the original source. -/
theorem actual_original_seed_projected_R_fields (c : BurnolCompletedMellinCoordinate) :
 P (burnolDirectRightResolvent (c.value/2) s)=actualCompactProjectedRField c s ∧
 P (burnolDirectRightResolvent (c.value/2) (fourierL2 s))=-(c.value⁻¹) • Fphysical G :=by
 have source:=Paid.actual_seed_source_qualification
 constructor
 · exact actual_compact_projected_R_source c s source.1 source.2.1
 · apply ext_inner_right ℂ
   intro physical
   have read:=(evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule
    |>.inner_orthogonalProjectionOnto_eq_of_mem_right physical
     (burnolDirectRightResolvent (c.value/2) (fourierL2 s))
   change inner ℂ (P (burnolDirectRightResolvent (c.value/2) (fourierL2 s))) physical=
    inner ℂ (burnolDirectRightResolvent (c.value/2) (fourierL2 s)) (physical:BurnolL2) at read
   rw [read,inner_smul_left]
   have seedRight:=(OriginalKSectorEulerMixedSource.actual_original_seed_R_right_prices c physical).2
   unfold OriginalKSectorEulerMixedSource.actualFourierSeedRightPrice at seedRight
   have actual:inner ℂ (burnolDirectRightResolvent (c.value/2) (fourierL2 s)) (physical:BurnolL2)=
    star (-(1/2:ℂ)*star (μ (fourierL2 (physical:BurnolL2)))/(c.value/2)):=
    ((inner_conj_symm (burnolDirectRightResolvent (c.value/2) (fourierL2 s)) (physical:BurnolL2)).symm).trans (congrArg star seedRight)
   rw [actual]
   have means:=OriginalKGapProjectionEulerSource.actual_source_fourier_input (G:BurnolL2) physical
   change inner ℂ (Fphysical G) physical=inner ℂ G (Fphysical physical) at means
   rw [means,OriginalRieszFiniteSynthesis.gapMeanVector_readback]
   change star (-(1/2:ℂ)*star (μ (fourierL2 (physical:BurnolL2)))/(c.value/2))=
    star (-c.value⁻¹)*μ (fourierL2 (physical:BurnolL2))
   simp only [star_neg,star_mul,star_div₀,star_ofNat,star_one,star_star]
   have inverseRead:star (c.value⁻¹)=(star c.value)⁻¹:=map_inv₀ (starRingEnd ℂ) c.value
   rw [inverseRead]
   ring

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCoupledPhysicalRFieldSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
