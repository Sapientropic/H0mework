import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKResponseCofinalSourceAction.Control
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKResponseCofinalSourceAction
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

local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "S" => burnolMeanZeroTruncatedFourierSquare

def actualWholeRead : M→L[ℂ]BurnolL2 :=
 burnolQuarterZeroExtension.comp (Submodule.subtypeL burnolQuarterMeanZeroClosedFace.toSubmodule)

def actualCoefficientRead (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2→L[ℂ]ℂ :=
 (2:ℂ) • (burnolRadiusMellinTailEvaluator 4 (by norm_num)
  (OriginalKQuarterTailPhysicalSource.actualStarSource coordinate).value
  (OriginalKQuarterTailPhysicalSource.actualStarSource coordinate).rightHalf).comp burnolTateReciprocalL2

def actualFirstRead (coordinate : BurnolCompletedMellinCoordinate) : M→L[ℂ]ℂ :=
 (actualCoefficientRead coordinate).comp actualWholeRead

def actualSecondRead (coordinate : BurnolCompletedMellinCoordinate) : M→L[ℂ]ℂ :=
 let cut:BurnolL2→L[ℂ]BurnolL2:=(burnolRadiusZeroExtension q).comp (burnolRadiusRestriction q)
 let action:=burnolDirectRightResolventCLM (OriginalKQuarterTailPhysicalSource.actualStarSource coordinate)
 (actualCoefficientRead coordinate).comp ((cut.comp action).comp actualWholeRead)

/-- The first independent coefficient consumer reads exactly the original full source, not a stream value recognized by equality. -/
theorem actual_first_read_source (coordinate : BurnolCompletedMellinCoordinate) (value : M) :
 actualFirstRead coordinate value=OriginalKCompactAdjointRSource.actualCompactTailCoefficient
  (OriginalKQuarterTailPhysicalSource.actualStarSource coordinate) (actualWholeRead value) :=rfl

/-- The second independent consumer reads the actual first R-generated cutoff before its own coefficient. -/
theorem actual_second_read_source (coordinate : BurnolCompletedMellinCoordinate) (value : M) :
 actualSecondRead coordinate value=OriginalKCompactAdjointRSource.actualCompactTailCoefficient
  (OriginalKQuarterTailPhysicalSource.actualStarSource coordinate)
  (OriginalKCompactJordanRankSource.actualFirstCut coordinate (actualWholeRead value)) :=rfl

/-- The actual finite source update generates every first coefficient increment. -/
theorem actual_first_coefficient_increment (coordinate : BurnolCompletedMellinCoordinate) (n : Nat) :
 actualFirstRead coordinate (actualU (n+1))-actualFirstRead coordinate (actualU n)=
 actualFirstRead coordinate ((S^n) OriginalRieszSource.Response.eta) :=by
 rw [←map_sub,actual_source_increment]

/-- Same source update generates the second coefficient before any original price is read. -/
theorem actual_second_coefficient_increment (coordinate : BurnolCompletedMellinCoordinate) (n : Nat) :
 actualSecondRead coordinate (actualU (n+1))-actualSecondRead coordinate (actualU n)=
 actualSecondRead coordinate ((S^n) OriginalRieszSource.Response.eta) :=by
 rw [←map_sub,actual_source_increment]

/-- Controlled actual source residual pays its own first coefficient price; no Pa-projected norm is borrowed. -/
theorem actual_first_coefficient_error (coordinate : BurnolCompletedMellinCoordinate) (n : Nat) :
 ‖actualFirstRead coordinate OriginalRieszSource.Response.u-actualFirstRead coordinate (actualU n)‖≤
 ‖actualFirstRead coordinate‖*((1/4:ℝ)^n*‖OriginalRieszSource.Response.u‖) :=by
 rw [←map_sub]
 exact ((actualFirstRead coordinate).le_opNorm _).trans
  (mul_le_mul_of_nonneg_left (actual_source_error_bound n) (norm_nonneg _))

theorem actual_second_coefficient_error (coordinate : BurnolCompletedMellinCoordinate) (n : Nat) :
 ‖actualSecondRead coordinate OriginalRieszSource.Response.u-actualSecondRead coordinate (actualU n)‖≤
 ‖actualSecondRead coordinate‖*((1/4:ℝ)^n*‖OriginalRieszSource.Response.u‖) :=by
 rw [←map_sub]
 exact ((actualSecondRead coordinate).le_opNorm _).trans
  (mul_le_mul_of_nonneg_left (actual_source_error_bound n) (norm_nonneg _))

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKResponseCofinalSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
