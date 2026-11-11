import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.CutPower
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.LogDomains
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaMobiusActedDLogSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.RelativeConductorGapReadback

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.VolterraKernel
open Complex MeasureTheory Set Filter BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalGamma.Source.KGamma OriginalGamma.Source.RelativeConductorGapReadback
open OriginalGamma.Source.FiniteLogCounting OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.CutPower
open scoped InnerProductSpace Topology
open private gamma_pair_dilation from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.RelativeConductorGapReadback
open private inverse_log_from_complete_source from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaMobiusActedDLogSource
local notation "q" => (1/4 : ℝ)
local notation "D" => burnolMultiplicativeDilation

def radiusShift (radius : ℝ) : ℝ := Real.log (4/radius)

def radiusScale (coordinate : BurnolCompletedMellinCoordinate) (radius : ℝ) : ℂ :=
  (fullMellinTranslationCharacter coordinate.value (radiusShift radius))⁻¹

def radiusTail (coordinate : BurnolCompletedMellinCoordinate) (radius : ℝ) : BurnolL2 :=
  radiusScale coordinate radius • D (radiusShift radius)
    (burnolRadiusNormalizedUnitTail coordinate 4 (by norm_num))

def radiusGamma (coordinate : BurnolCompletedMellinCoordinate) (radius : ℝ) : BurnolL2 :=
  radiusScale coordinate radius • D (radiusShift radius) (fourTailGamma coordinate)

theorem actual_radius_tail (coordinate : BurnolCompletedMellinCoordinate)
    (radius : ℝ) (positive : 0<radius) :
    radiusTail coordinate radius=burnolRadiusNormalizedUnitTail coordinate radius positive := by
  have location : 4*Real.exp (-radiusShift radius)=radius := by
    rw [radiusShift,Real.exp_neg,Real.exp_log (div_pos (by norm_num) positive)]
    field_simp
  have moved := burnolRadiusNormalizedUnitTail_dilation coordinate 4 (by norm_num) (radiusShift radius)
  have paid : D (radiusShift radius) (burnolRadiusNormalizedUnitTail coordinate 4 (by norm_num))=
      fullMellinTranslationCharacter coordinate.value (radiusShift radius) •
        burnolRadiusNormalizedUnitTail coordinate radius positive := by
    simpa only [location] using moved
  rw [radiusTail,paid,smul_smul,radiusScale,
    inv_mul_cancel₀ (show fullMellinTranslationCharacter coordinate.value (radiusShift radius)≠0 from Complex.exp_ne_zero _),one_smul]

theorem actual_radius_Gamma (coordinate : BurnolCompletedMellinCoordinate) (radius : ℝ) :
    GammaPair (radiusTail coordinate radius) (radiusGamma coordinate radius) := by
  intro test
  rw [radiusTail,radiusGamma,inner_smul_right,inner_smul_right,
    gamma_pair_dilation (radiusShift radius) _ _ (actual_four_tail_Gamma coordinate) test]

def cutValue (coordinate : BurnolCompletedMellinCoordinate) (radius : ℝ) : BurnolL2 :=
  burnolRadiusNormalizedUnitTail coordinate 4 (by norm_num)-radiusTail coordinate radius

def cutGamma (coordinate : BurnolCompletedMellinCoordinate) (radius : ℝ) : BurnolL2 :=
  fourTailGamma coordinate-radiusGamma coordinate radius

theorem actual_cut_Gamma (coordinate : BurnolCompletedMellinCoordinate) (radius : ℝ) :
    GammaPair (cutValue coordinate radius) (cutGamma coordinate radius) := by
  intro test
  rw [cutValue,cutGamma,inner_sub_right,inner_sub_right,
    actual_four_tail_Gamma coordinate test,actual_radius_Gamma coordinate radius test]

theorem actual_cut_raw (coordinate : BurnolCompletedMellinCoordinate)
    (radius : ℝ) (admitted : radius∈Icc q 4) :
    (cutValue coordinate radius : ℝ → ℂ)=ᵐ[volume] fun t =>
      if radius < |t| ∧ |t|≤4 then ((|t| : ℝ) : ℂ)^(-coordinate.value) else 0 := by
  have positive : 0<radius := by linarith [admitted.1]
  rw [cutValue,actual_radius_tail coordinate radius positive]
  filter_upwards [Lp.coeFn_sub (burnolRadiusNormalizedUnitTail coordinate 4 (by norm_num))
    (burnolRadiusNormalizedUnitTail coordinate radius positive),
    burnolRadiusUnitTail_coeFn coordinate 4 (by norm_num),
    burnolRadiusUnitTail_coeFn coordinate radius positive] with t difference upper lower
  rw [difference,Pi.sub_apply,upper,lower]
  by_cases below : radius < |t|
  · by_cases above : 4 < |t|
    · rw [if_pos below,if_pos above,sub_self,if_neg (fun inside => not_lt_of_ge inside.2 above)]
    · rw [if_pos below,if_neg above,zero_sub,neg_neg,if_pos ⟨below,le_of_not_gt above⟩]
  · have outside : ¬4 < |t| := by linarith [admitted.2]
    rw [if_neg below,if_neg outside,sub_self,if_neg (fun inside => below inside.1)]

theorem actual_cut_even (coordinate : BurnolCompletedMellinCoordinate)
    (radius : ℝ) (admitted : radius∈Icc q 4) :
    reflectL2 (cutValue coordinate radius)=cutValue coordinate radius :=
  burnolReflectL2_eq_of_even_raw _ _ (actual_cut_raw coordinate radius admitted)
    (fun t => by simp only [abs_neg])

theorem actual_shift_continuous : ContinuousOn radiusShift (Icc q 4) := by
  apply ContinuousOn.log
  · exact continuousOn_const.div continuousOn_id (fun radius inside => by linarith [inside.1])
  · intro radius inside
    exact div_ne_zero (by norm_num) (by linarith [inside.1])

theorem actual_scale_continuous (coordinate : BurnolCompletedMellinCoordinate) :
    ContinuousOn (radiusScale coordinate) (Icc q 4) := by
  apply ContinuousOn.inv₀
  · exact Complex.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn actual_shift_continuous))
  · intro radius _
    exact Complex.exp_ne_zero _

theorem actual_cut_continuous (coordinate : BurnolCompletedMellinCoordinate) :
    ContinuousOn (cutValue coordinate) (Icc q 4) :=
  continuousOn_const.sub ((actual_scale_continuous coordinate).smul
    ((burnolMultiplicativeDilation_stronglyContinuous _).comp_continuousOn actual_shift_continuous))

theorem actual_cut_Gamma_continuous (coordinate : BurnolCompletedMellinCoordinate) :
    ContinuousOn (cutGamma coordinate) (Icc q 4) :=
  continuousOn_const.sub ((actual_scale_continuous coordinate).smul
    ((burnolMultiplicativeDilation_stronglyContinuous _).comp_continuousOn actual_shift_continuous))

theorem actual_cut_joint_bound (coordinate : BurnolCompletedMellinCoordinate) :
    ∃ bound : ℝ, 0≤bound ∧ ∀ radius∈Icc q 4,
      ‖cutValue coordinate radius‖≤bound ∧ ‖cutGamma coordinate radius‖≤bound := by
  obtain ⟨first,bounds⟩ := isCompact_Icc.exists_bound_of_continuousOn (actual_cut_continuous coordinate)
  obtain ⟨second,other⟩ := isCompact_Icc.exists_bound_of_continuousOn (actual_cut_Gamma_continuous coordinate)
  refine ⟨max 0 (max first second),le_max_left _ _,?_⟩
  intro radius admitted
  exact ⟨(bounds radius admitted).trans ((le_max_left _ _).trans (le_max_right _ _)),
    (other radius admitted).trans ((le_max_right _ _).trans (le_max_right _ _))⟩

/-- The complete conductor kernel has a genuine source-variable L2 norm on the whole radius window. -/
theorem actual_cut_joint_Gamma_domain (coordinate : BurnolCompletedMellinCoordinate) :
    MemLp (cutGamma coordinate) 2 (volume.restrict (Icc q 4)) := by
  obtain ⟨bound,_,bounds⟩ := actual_cut_joint_bound coordinate
  apply MemLp.of_bound
    ((actual_cut_Gamma_continuous coordinate).aestronglyMeasurable measurableSet_Icc) bound
  filter_upwards [ae_restrict_mem measurableSet_Icc] with radius admitted
  exact (bounds radius admitted).2

private def positionRaw (coordinate : BurnolCompletedMellinCoordinate)
    (radius t : ℝ) : ℂ := (Real.log |t| : ℂ)*cutValue coordinate radius t

private theorem position_domain (coordinate : BurnolCompletedMellinCoordinate)
    (radius : ℝ) (admitted : radius∈Icc q 4) :
    MemLp (positionRaw coordinate radius) 2 volume := by
  have regular : ContinuousOn (fun t : ℝ => (Real.log t : ℂ)) (Icc q 4) := by
    intro t inside
    have positive : 0<t := by linarith [inside.1]
    exact (Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log positive.ne')).continuousWithinAt
  obtain ⟨bound,bounds⟩ := isCompact_Icc.exists_bound_of_continuousOn regular
  have logarithm : Measurable (fun t : ℝ => (Real.log |t| : ℂ)) := by fun_prop
  apply (Lp.memLp (cutValue coordinate radius)).of_le_mul
    (f := positionRaw coordinate radius) (c := bound)
    (logarithm.aestronglyMeasurable.mul
      (Lp.stronglyMeasurable (cutValue coordinate radius)).aestronglyMeasurable)
  filter_upwards [actual_cut_raw coordinate radius admitted] with t source
  change ‖(Real.log |t| : ℂ)*cutValue coordinate radius t‖≤bound*‖cutValue coordinate radius t‖
  by_cases inside : radius < |t| ∧ |t|≤4
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (bounds |t| ⟨admitted.1.trans inside.1.le,inside.2⟩) (norm_nonneg _)
  · have empty : cutValue coordinate radius t=0 := source.trans (if_neg inside)
    simpa only [empty,mul_zero,norm_zero] using (le_rfl : (0 : ℝ)≤0)

def cutPosition (coordinate : BurnolCompletedMellinCoordinate)
    (radius : ℝ) (admitted : radius∈Icc q 4) : BurnolL2 :=
  (position_domain coordinate radius admitted).toLp (positionRaw coordinate radius)

def cutFrequency (coordinate : BurnolCompletedMellinCoordinate)
    (radius : ℝ) (admitted : radius∈Icc q 4) : BurnolL2 :=
  fourierL2.symm (cutGamma coordinate radius-cutPosition coordinate radius admitted)

theorem actual_cut_two_sources (coordinate : BurnolCompletedMellinCoordinate)
    (radius : ℝ) (admitted : radius∈Icc q 4) :
    LogPair (cutValue coordinate radius) (cutPosition coordinate radius admitted) ∧
      LogPair (fourierL2.symm (cutValue coordinate radius)) (cutFrequency coordinate radius admitted) := by
  have first : LogPair (cutValue coordinate radius) (cutPosition coordinate radius admitted) :=
    (position_domain coordinate radius admitted).coeFn_toLp
  exact ⟨first,inverse_log_from_complete_source _ _ _ (actual_cut_Gamma coordinate radius) first⟩

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.VolterraKernel
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
