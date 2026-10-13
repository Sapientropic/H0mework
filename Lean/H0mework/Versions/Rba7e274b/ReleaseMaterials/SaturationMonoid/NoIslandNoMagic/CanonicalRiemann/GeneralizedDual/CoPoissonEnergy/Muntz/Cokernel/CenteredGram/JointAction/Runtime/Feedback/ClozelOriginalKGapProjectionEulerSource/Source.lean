import Lean
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteResponseEulerSource.Consumer
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

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

namespace Seed
export OriginalKConstantSeedWholeRAction.ConstantSource (seed)
end Seed
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "T" => burnolMeanZeroTruncatedFourier
local notation "L" => burnolMeanZeroOneMinusSquare

def actualGapSource : M:=burnolAmbientMeanZeroFourier Seed.seed
def actualGapResponse : M:=burnolAmbientMeanZeroSecondCorrection Seed.seed

theorem actual_seed_even : reflectL2 Seed.seed=Seed.seed :=by
 change reflectL2 (burnolRadiusZeroExtension q (intervalConstant q))=burnolRadiusZeroExtension q (intervalConstant q)
 rw [burnolRadiusZeroExtension_reflect,reflectRestricted_intervalConstant]

theorem actual_seed_even_part : burnolAmbientEvenPart Seed.seed=Seed.seed :=by
 unfold burnolAmbientEvenPart
 rw [actual_seed_even]
 module

/-- The literal original seed has zero centered position source, before any physical projection. -/
theorem actual_seed_position_source : burnolAmbientMeanZeroPosition Seed.seed=0 :=by
 apply Subtype.ext
 change burnolQuarterMeanZeroProjection (burnolQuarterRestriction (burnolAmbientEvenPart Seed.seed))=0
 rw [actual_seed_even_part]
 change burnolQuarterMeanZeroProjection (burnolRadiusRestriction q (burnolRadiusZeroExtension q (intervalConstant q)))=0
 rw [burnolRadiusRestriction_zeroExtension]
 exact (burnolQuarterMeanZeroProjection_eq_zero_iff _).mpr (Submodule.mem_span_singleton_self _)

/-- Existing block source equations generate the actual first correction from the same response. -/
theorem actual_first_gap_correction : burnolAmbientMeanZeroFirstCorrection Seed.seed= -T actualGapResponse :=by
 have source:=burnolMeanZeroBlock_first_equation (burnolAmbientMeanZeroBlockRhs Seed.seed)
 change burnolAmbientMeanZeroFirstCorrection Seed.seed+T actualGapResponse=
  burnolAmbientMeanZeroPosition Seed.seed at source
 rw [actual_seed_position_source] at source
 exact eq_neg_of_add_eq_zero_left source

/-- The same source block generates the full actual gap response equation; no response or endpoint is constructor input. -/
theorem actual_gap_response_equation : L actualGapResponse=actualGapSource :=by
 have source:=burnolMeanZeroBlock_second_equation (burnolAmbientMeanZeroBlockRhs Seed.seed)
 change T (burnolAmbientMeanZeroFirstCorrection Seed.seed)+actualGapResponse=actualGapSource at source
 rw [actual_first_gap_correction,map_neg] at source
 change actualGapResponse-T (T actualGapResponse)=actualGapSource
 simpa only [sub_eq_add_neg,add_comm] using source

/-- Actual gap response retains the same source parity by inverse uniqueness, not a generic physical claim. -/
theorem actual_gap_response_even : reflectRestricted q (actualGapResponse:BurnolQuarterIntervalL2)=actualGapResponse :=by
 have rightParity:=burnolAmbientMeanZeroFourier_reflection_fixed Seed.seed
 have generated : L (sourceMeanZeroReflection actualGapResponse)=actualGapSource :=by
  change sourceMeanZeroReflection actualGapResponse-T (T (sourceMeanZeroReflection actualGapResponse))=_
  rw [sourceMeanZeroFourier_reflect,sourceMeanZeroFourier_reflect]
  apply Subtype.ext
  change reflectRestricted q (actualGapResponse:BurnolQuarterIntervalL2)-
   reflectRestricted q (T (T actualGapResponse):BurnolQuarterIntervalL2)=_
  rw [←map_sub]
  have actual:=congrArg (fun state:M=>reflectRestricted q (state:BurnolQuarterIntervalL2)) actual_gap_response_equation
  exact actual.trans rightParity
 have inverseLeft:burnolMeanZeroBlockInverse*L=1:=Ring.inverse_mul_cancel _ burnolMeanZeroOneMinusSquare_isUnit
 have recovered:=congrArg burnolMeanZeroBlockInverse (generated.trans actual_gap_response_equation.symm)
 change (burnolMeanZeroBlockInverse*L) (sourceMeanZeroReflection actualGapResponse)=
  (burnolMeanZeroBlockInverse*L) actualGapResponse at recovered
 rw [inverseLeft] at recovered
 exact congrArg (fun state:M=>(state:BurnolQuarterIntervalL2)) recovered

theorem actual_gap_return_even : reflectRestricted q (T actualGapResponse:BurnolQuarterIntervalL2)=T actualGapResponse :=by
 have fixed:sourceMeanZeroReflection actualGapResponse=actualGapResponse:=Subtype.ext actual_gap_response_even
 have source:=sourceMeanZeroFourier_reflect actualGapResponse
 rw [fixed] at source
 exact congrArg (fun state:M=>(state:BurnolQuarterIntervalL2)) source.symm

def actualGapWhole : BurnolL2:=Seed.seed+
 burnolQuarterZeroExtension (T actualGapResponse:BurnolQuarterIntervalL2)-
 fourierL2 (burnolQuarterZeroExtension (actualGapResponse:BurnolQuarterIntervalL2))

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKGapProjectionEulerSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
