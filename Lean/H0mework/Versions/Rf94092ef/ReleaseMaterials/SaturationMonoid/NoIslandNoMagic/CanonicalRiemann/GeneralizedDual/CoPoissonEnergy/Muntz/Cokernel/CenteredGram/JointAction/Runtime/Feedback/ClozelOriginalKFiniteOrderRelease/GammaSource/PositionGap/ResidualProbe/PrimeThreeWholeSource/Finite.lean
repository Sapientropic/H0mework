import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.PrimeThreeWholeSource.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.PrimeThree.Gram.Action

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PrimeThreeWholeSource.Finite
open BurnolPhysicalState OriginalPaPhysicalGreen
local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

local notation "P" => OriginalKCombPhysicalAction.physicalProjection
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder

def pa (value : BurnolL2) : BurnolPaAmbientCarrier :=
  burnolCompactCoPoissonClosedRange.toSubmodule.starProjection (burnolEvenAmbientProjection value)

theorem pa_mem (value : BurnolL2) : pa value ∈ burnolCompactCoPoissonClosedRange :=
  Submodule.starProjection_apply_mem _ _

def residual (value : BurnolL2) : BurnolL2 := P value-(pa value : BurnolL2)
def outside (value : BurnolL2) : BurnolL2 := O value

theorem split (value : BurnolL2) : (pa value : BurnolL2)+residual value+outside value=value := by
  have whole := OriginalKCombFullResidualAction.split_complete value
  change P value+O value=value at whole
  dsimp only [residual,outside]
  have front : (pa value : BurnolL2)+(P value-(pa value : BurnolL2))=P value := by abel
  rw [front]
  exact whole

def sigma (value : BurnolL2) : BurnolL2 := burnolMobiusSourceL2 (pa value)
def mean (value : BurnolL2) : ℂ := burnolConstantGapCoefficient burnolUnscaledCommonGapRadius (pa value)

private theorem cutoff_add (radius : ℝ) (x y : BurnolL2) :
    originalPhysicalCutoff radius (x+y)=originalPhysicalCutoff radius x+originalPhysicalCutoff radius y := by
  simp only [originalPhysicalCutoff,map_add]

theorem source_action (value : BurnolL2) (N : Nat) :
    originalPhysicalCutoff ((N : ℝ)+1) (Math.action value) =
      originalPhysicalCutoff ((N : ℝ)+1) (finitePrimeThreeSourceAction (sigma value) (primeThreeGramCount N)) +
      (((Real.sqrt 3 : ℂ)-(Real.sqrt 3 : ℂ)⁻¹)*mean value) • physicalMeanCell ((N : ℝ)+1) +
      originalPhysicalCutoff ((N : ℝ)+1) (Math.action (residual value)) +
      originalPhysicalCutoff ((N : ℝ)+1) (Math.action (outside value)) := by
  have finite := primeThree_finite_source_action (pa value) (pa_mem value)
    ((N : ℝ)+1) (primeThreeGramCount N) (Nat.le_ceil _)
  have complete := congrArg (fun v : BurnolL2 => originalPhysicalCutoff ((N : ℝ)+1) (Math.action v)) (split value)
  simp only [map_add, cutoff_add] at complete
  change originalPhysicalCutoff ((N : ℝ)+1) (Math.action (pa value : BurnolL2)) +
    originalPhysicalCutoff ((N : ℝ)+1) (Math.action (residual value)) +
    originalPhysicalCutoff ((N : ℝ)+1) (Math.action (outside value)) = _ at complete
  rw [Math.action_original,finite] at complete
  exact complete.symm

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PrimeThreeWholeSource.Finite
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
