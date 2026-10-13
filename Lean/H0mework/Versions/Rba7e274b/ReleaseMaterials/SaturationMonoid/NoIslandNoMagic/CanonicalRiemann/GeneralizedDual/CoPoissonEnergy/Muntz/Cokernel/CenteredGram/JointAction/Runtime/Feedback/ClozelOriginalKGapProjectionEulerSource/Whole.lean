import Lean
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKGapProjectionEulerSource.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKGapProjectionEulerSource
open Complex MeasureTheory Set Filter SourceGeneratedHilbertCokernel
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
namespace Paid
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.FiniteMobiusResolventFlux (actualMean Rplus RplusIntegrand Rplus_integrable)
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalJointFluxSource (actual_mean_source_integral actual_mean_dilation_source source_weight_mean_phase)
end Paid
local notation "q" => (1/4:ℝ)
local notation "T" => burnolMeanZeroTruncatedFourier

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

/-- The actual raw source unit is fixed by the paid seed/gap normalization. -/
theorem actual_raw_gap_seed : burnolAmbientGapRieszVector q=(2:ℂ) • Seed.seed :=by
 have source:=OriginalKJordanSeedFieldSource.actual_seed_gap_source
 have scaled:=congrArg (fun field:BurnolL2=>(2:ℂ) • field) source
 change (2:ℂ) • Seed.seed=(2:ℂ) • ((2*q:ℂ) • burnolAmbientGapRieszVector q) at scaled
 rw [smul_smul] at scaled
 norm_num at scaled
 exact scaled.symm

theorem actual_raw_gap_correction_even :
 reflectL2 (burnolAmbientRawMeanZeroCorrection Seed.seed)=burnolAmbientRawMeanZeroCorrection Seed.seed :=by
 unfold burnolAmbientRawMeanZeroCorrection
 rw [actual_first_gap_correction]
 change reflectL2 (burnolRadiusZeroExtension q (-(T actualGapResponse:BurnolQuarterIntervalL2))+
  fourierL2 (burnolRadiusZeroExtension q (actualGapResponse:BurnolQuarterIntervalL2)))=
  burnolRadiusZeroExtension q (-(T actualGapResponse:BurnolQuarterIntervalL2))+
  fourierL2 (burnolRadiusZeroExtension q (actualGapResponse:BurnolQuarterIntervalL2))
 rw [map_add,←fourierL2_reflectL2_commute,burnolRadiusZeroExtension_reflect,
  burnolRadiusZeroExtension_reflect,map_neg,actual_gap_return_even,actual_gap_response_even]

/-- Original physical G consumes the same seed's actual complete block correction; no box substitute or projection/derivative commutation. -/
theorem actual_gap_mean_whole_source :
 (OriginalRieszFiniteSynthesis.gapMeanVector:BurnolL2)=(2:ℂ) • actualGapWhole :=by
 have source:burnolAmbientExtendedSonineProjectionFormula Seed.seed=actualGapWhole :=by
  unfold burnolAmbientExtendedSonineProjectionFormula burnolAmbientEvenMeanZeroCorrection
  rw [actual_seed_even_part]
  have evenpart:burnolAmbientEvenPart (burnolAmbientRawMeanZeroCorrection Seed.seed)=
   burnolAmbientRawMeanZeroCorrection Seed.seed:=by
   unfold burnolAmbientEvenPart
   rw [actual_raw_gap_correction_even]
   module
  rw [evenpart]
  unfold burnolAmbientRawMeanZeroCorrection actualGapWhole
  rw [actual_first_gap_correction]
  change Seed.seed-(burnolQuarterZeroExtension (-(T actualGapResponse:BurnolQuarterIntervalL2))+
   fourierL2 (burnolQuarterZeroExtension (actualGapResponse:BurnolQuarterIntervalL2)))=_
  rw [map_neg]
  module
 unfold OriginalRieszFiniteSynthesis.gapMeanVector
 change (burnolEvenAmbientProjection (burnolAmbientGapRieszVector q):BurnolL2)=_
 rw [actual_raw_gap_seed,map_smul]
 change (2:ℂ) • ((evenBurnolClosedFace q).toSubmodule.orthogonalProjectionOnto Seed.seed:BurnolL2)=_
 rw [burnolEvenOrthogonalProjectionOnto_eq_resolventFormula,source]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKGapProjectionEulerSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
