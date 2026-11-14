import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryNativeKConductorSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.PrimeThree.Physical.Residue

-- This owned family retains large receipt types in its later source consumers.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PrimeThreeWholeSource"

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PrimeThreeWholeSource.Math
open BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalGamma.Source.FiniteLogCounting OriginalGamma.Source.RelativeConductorGapReadback
namespace CS
export BoundaryNativeKConductorSource (Source sub sub_gamma)
end CS
open private log_pair_dilation gamma_pair_dilation from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.RelativeConductorGapReadback
open private inverse_log_from_complete_source from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaMobiusActedDLogSource
open private logPair_smul from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.FourierLogDomainSource

def scale : ℝ := Real.sqrt 3
def shift : ℝ := Real.log scale
def weight : ℝ := Real.sqrt scale

theorem weight_gt_one : 1 < weight := by
  have scaleSquare : scale^2 = 3 := Real.sq_sqrt (by norm_num)
  have scaleNonnegative : 0 ≤ scale := Real.sqrt_nonneg _
  have scaleLarge : 1 < scale := by nlinarith
  have weightSquare : weight^2 = scale := Real.sq_sqrt scaleNonnegative
  have weightNonnegative : 0 ≤ weight := Real.sqrt_nonneg _
  nlinarith
theorem weight_pos : 0 < weight := lt_trans zero_lt_one weight_gt_one
theorem strength_pos : 0 < weight-weight⁻¹ := by
  have below : weight⁻¹ < 1 := (inv_lt_one₀ weight_pos).2 weight_gt_one
  linarith [weight_gt_one]

def dilation (h : ℝ) : BurnolL2 →L[ℂ] BurnolL2 :=
  (burnolMultiplicativeDilation h).toLinearIsometry.toContinuousLinearMap

def action : BurnolL2 →L[ℂ] BurnolL2 :=
  (weight : ℂ) • dilation shift - (weight : ℂ)⁻¹ • dilation (-shift)

theorem action_original (value : BurnolL2) : action value = primeThreePhysicalResidue value := rfl

theorem lower_bound (value : BurnolL2) : (weight-weight⁻¹)*‖value‖ ≤ ‖action value‖ := by
  have read := norm_sub_norm_le ((weight : ℂ) • dilation shift value)
    ((weight : ℂ)⁻¹ • dilation (-shift) value)
  have weightNorm : ‖(weight : ℂ)‖ = weight := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos weight_pos]
  rw [norm_smul, norm_smul, norm_inv, weightNorm,
    show ‖dilation shift value‖=‖value‖ from (burnolMultiplicativeDilation shift).norm_map value,
    show ‖dilation (-shift) value‖=‖value‖ from (burnolMultiplicativeDilation (-shift)).norm_map value] at read
  change (weight-weight⁻¹)*‖value‖ ≤
    ‖(weight : ℂ) • dilation shift value-(weight : ℂ)⁻¹ • dilation (-shift) value‖
  exact (le_of_eq (sub_mul _ _ _)).trans read

theorem action_live {value : BurnolL2} (live : value ≠ 0) : action value ≠ 0 := by
  intro zero
  have bound := lower_bound value
  rw [zero, norm_zero] at bound
  have positive := mul_pos strength_pos (norm_pos_iff.mpr live)
  linarith

theorem action_resolvent (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    action (burnolDirectRightResolventCLM coordinate value) = burnolDirectRightResolventCLM coordinate (action value) := by
  change (weight : ℂ) • burnolMultiplicativeDilation shift (burnolDirectRightResolvent (coordinate.value/2) value) -
    (weight : ℂ)⁻¹ • burnolMultiplicativeDilation (-shift) (burnolDirectRightResolvent (coordinate.value/2) value) =
    burnolDirectRightResolventCLM coordinate ((weight : ℂ) • burnolMultiplicativeDilation shift value-
      (weight : ℂ)⁻¹ • burnolMultiplicativeDilation (-shift) value)
  rw [map_sub, map_smul, map_smul]
  exact congrArg₂ (·-·)
    (congrArg ((weight : ℂ) • ·) (burnolDirectRightResolvent_dilation (coordinate.value/2) shift value).symm)
    (congrArg ((weight : ℂ)⁻¹ • ·) (burnolDirectRightResolvent_dilation (coordinate.value/2) (-shift) value).symm)

private def positionAfter (h : ℝ) (source : CS.Source) :=
  burnolMultiplicativeDilation h source.position-(h : ℂ) • burnolMultiplicativeDilation h source.value

def dilate (h : ℝ) (source : CS.Source) : CS.Source where
  value := burnolMultiplicativeDilation h source.value
  position := positionAfter h source
  inverse := fourierL2.symm (burnolMultiplicativeDilation h source.gamma-positionAfter h source)
  even := by rw [reflectL2_burnolMultiplicativeDilation, source.even]
  position_graph := log_pair_dilation h _ _ source.position_graph
  inverse_graph := inverse_log_from_complete_source _ _ _ (gamma_pair_dilation h _ _ source.graph)
    (log_pair_dilation h _ _ source.position_graph)

theorem dilate_gamma (h : ℝ) (source : CS.Source) : (dilate h source).gamma = burnolMultiplicativeDilation h source.gamma := by
  change positionAfter h source+fourierL2 (fourierL2.symm (_-positionAfter h source)) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  abel

def scalar (coefficient : ℂ) (source : CS.Source) : CS.Source where
  value := coefficient • source.value
  position := coefficient • source.position
  inverse := coefficient • source.inverse
  even := by rw [map_smul, source.even]
  position_graph := logPair_smul _ _ _ source.position_graph
  inverse_graph := by
    rw [map_smul]
    exact logPair_smul _ _ _ source.inverse_graph

theorem scalar_gamma (coefficient : ℂ) (source : CS.Source) : (scalar coefficient source).gamma = coefficient • source.gamma := by
  change coefficient • source.position+fourierL2 (coefficient • source.inverse) = _
  rw [map_smul, ← smul_add]
  rfl

def sourceAction (source : CS.Source) : CS.Source :=
  CS.sub (scalar weight (dilate shift source)) (scalar (weight : ℂ)⁻¹ (dilate (-shift) source))

theorem source_action_value (source : CS.Source) : (sourceAction source).value = action source.value := rfl

theorem source_action_gamma (source : CS.Source) : (sourceAction source).gamma = action source.gamma := by
  rw [sourceAction, CS.sub_gamma, scalar_gamma, scalar_gamma, dilate_gamma, dilate_gamma]
  rfl

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PrimeThreeWholeSource.Math
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
