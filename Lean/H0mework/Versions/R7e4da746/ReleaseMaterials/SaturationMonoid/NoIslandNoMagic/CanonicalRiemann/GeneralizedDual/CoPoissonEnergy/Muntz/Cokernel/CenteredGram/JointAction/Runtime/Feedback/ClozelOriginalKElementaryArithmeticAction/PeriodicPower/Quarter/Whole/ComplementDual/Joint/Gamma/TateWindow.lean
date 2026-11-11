import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaMobiusActedDLogSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.NativePa
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.VolterraKernel

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.TateWindow
open Complex MeasureTheory Set Filter BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalGamma.Source.KGamma OriginalGamma.Source.RelativeConductorGapReadback
open OriginalGamma.Source.JointLogConductor
open OriginalGamma.Source.FiniteLogCounting OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.VolterraKernel
open scoped InnerProductSpace Topology
open private inverse_log_from_complete_source from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaMobiusActedDLogSource
local notation "q" => (1/4 : ℝ)
local notation "T" => burnolTateReciprocalL2
local notation "ν" => burnolMobiusSourceL2
local notation "A" => sourceAnnulusCut

local instance : CompleteSpace BurnolPaAmbientCarrier :=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

/-- The actual physical shell fixes the sign and reciprocal radius of this same-c cut. -/
theorem actual_shell_source (coordinate : BurnolCompletedMellinCoordinate)
    (radius : ℝ) (admitted : radius∈Icc q 4) :
    ν (volterraPhysicalShell coordinate radius)=cutValue coordinate radius⁻¹ := by
  have reciprocal := volterraShell_reciprocal_admitted radius admitted
  have positive : 0<radius⁻¹ := by linarith [reciprocal.1]
  rw [volterraPhysicalShell,dif_pos admitted,map_neg,closedShellState_source,
    cutValue,actual_radius_tail coordinate radius⁻¹ positive]
  change -(burnolRadiusNormalizedUnitTail coordinate radius⁻¹ positive-
    burnolRadiusNormalizedUnitTail coordinate 4 (by norm_num))=_
  module

private theorem reciprocal_continuous :
    ContinuousOn (fun radius : ℝ => radius⁻¹) (Icc q 4) := by
  apply continuousOn_id.inv₀
  intro radius admitted
  change radius≠0
  linarith [admitted.1]

theorem actual_reciprocal_Gamma_continuous (coordinate : BurnolCompletedMellinCoordinate) :
    ContinuousOn (fun radius : ℝ => cutGamma coordinate radius⁻¹) (Icc q 4) :=
  (actual_cut_Gamma_continuous coordinate).comp reciprocal_continuous
    (fun radius admitted => volterraShell_reciprocal_admitted radius admitted)

theorem actual_Gamma_integrand_integrable (coordinate : BurnolCompletedMellinCoordinate)
    (value : BurnolL2) :
    IntegrableOn (fun radius : ℝ => volterraSourceDensity coordinate value radius •
      cutGamma coordinate radius⁻¹) (Icc q 4) := by
  obtain ⟨bound,_,bounds⟩ := actual_cut_joint_bound coordinate
  have density := volterraSourceDensity_integrableOn coordinate value
  apply (density.norm.mul_const bound).mono'
    (density.aestronglyMeasurable.smul
      ((actual_reciprocal_Gamma_continuous coordinate).aestronglyMeasurable measurableSet_Icc))
  filter_upwards [ae_restrict_mem measurableSet_Icc] with radius admitted
  change ‖volterraSourceDensity coordinate value radius • cutGamma coordinate radius⁻¹‖≤_
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left
    (bounds radius⁻¹ (volterraShell_reciprocal_admitted radius admitted)).2 (norm_nonneg _)

def tateWindow (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) : BurnolL2 :=
  T (sourceVolterraWindow coordinate (A value))

def tateWindowGamma (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) : BurnolL2 :=
  ∫ radius : ℝ in Icc q 4, volterraSourceDensity coordinate value radius •
    cutGamma coordinate radius⁻¹

theorem actual_tate_window_source (coordinate : BurnolCompletedMellinCoordinate)
    (value : BurnolL2) (even : reflectL2 value=value) :
    tateWindow coordinate value=ν (sourceVolterraPhysical coordinate value) := by
  have source := congrArg T (sourceVolterraPhysical_source_cut coordinate value even)
  rw [burnolTateReciprocalL2_involutive] at source
  exact source.symm

theorem actual_tate_window_integral (coordinate : BurnolCompletedMellinCoordinate)
    (value : BurnolL2) (even : reflectL2 value=value) :
    tateWindow coordinate value=
      ∫ radius : ℝ in Icc q 4, volterraSourceDensity coordinate value radius •
        cutValue coordinate radius⁻¹ := by
  rw [actual_tate_window_source coordinate value even,sourceVolterraPhysical,
    ←burnolMobiusSourceL2.integral_comp_comm (sourceVolterraPhysical_integrable coordinate value)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro radius admitted
  change ν (volterraSourceDensity coordinate value radius • volterraPhysicalShell coordinate radius)=_
  rw [map_smul,actual_shell_source coordinate radius admitted]

private theorem value_integrand_integrable (coordinate : BurnolCompletedMellinCoordinate)
    (value : BurnolL2) :
    IntegrableOn (fun radius : ℝ => volterraSourceDensity coordinate value radius •
      cutValue coordinate radius⁻¹) (Icc q 4) := by
  have source := burnolMobiusSourceL2.integrable_comp (sourceVolterraPhysical_integrable coordinate value)
  apply source.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with radius admitted
  rw [map_smul,actual_shell_source coordinate radius admitted]

/-- The genuine Tate reader, rather than an uncut homogeneous function, supplies the whole Gamma source. -/
theorem actual_tate_window_Gamma (coordinate : BurnolCompletedMellinCoordinate)
    (value : BurnolL2) (even : reflectL2 value=value) :
    GammaPair (tateWindow coordinate value) (tateWindowGamma coordinate value) := by
  intro test
  have first := (innerSL ℂ (wholeConductorTest test)).integral_comp_comm
    (value_integrand_integrable coordinate value)
  have second := (innerSL ℂ (test.toLp 2 volume)).integral_comp_comm
    (actual_Gamma_integrand_integrable coordinate value)
  simp only [innerSL_apply_apply] at first second
  rw [actual_tate_window_integral coordinate value even,tateWindowGamma,←first,←second]
  apply setIntegral_congr_fun measurableSet_Icc
  intro radius _
  change inner ℂ (wholeConductorTest test)
    (volterraSourceDensity coordinate value radius • cutValue coordinate radius⁻¹)=_
  simp only [inner_smul_right]
  exact congrArg (volterraSourceDensity coordinate value radius*·)
    (actual_cut_Gamma coordinate radius⁻¹ test)

private theorem cut_supported (coordinate : BurnolCompletedMellinCoordinate)
    (radius : ℝ) (admitted : radius∈Icc q 4) :
    A (cutValue coordinate radius)=cutValue coordinate radius := by
  apply Lp.ext
  filter_upwards [sourceAnnulusCut_coeFn (cutValue coordinate radius),
    actual_cut_raw coordinate radius admitted] with t cut raw
  rw [cut]
  split_ifs with inside
  · rfl
  · rw [raw,if_neg (fun active => inside ⟨admitted.1.trans_lt active.1,active.2⟩)]

theorem actual_tate_window_supported (coordinate : BurnolCompletedMellinCoordinate)
    (value : BurnolL2) (even : reflectL2 value=value) :
    A (tateWindow coordinate value)=tateWindow coordinate value := by
  rw [actual_tate_window_integral coordinate value even,
    ←sourceAnnulusCut.integral_comp_comm (value_integrand_integrable coordinate value)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro radius admitted
  change A (volterraSourceDensity coordinate value radius • cutValue coordinate radius⁻¹)=_
  rw [map_smul,cut_supported coordinate radius⁻¹
    (volterraShell_reciprocal_admitted radius admitted)]

private def positionRaw (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (t : ℝ) : ℂ := (Real.log |t| : ℂ)*tateWindow coordinate value t

private theorem position_domain (coordinate : BurnolCompletedMellinCoordinate)
    (value : BurnolL2) (even : reflectL2 value=value) :
    MemLp (positionRaw coordinate value) 2 volume := by
  have regular : ContinuousOn (fun t : ℝ => (Real.log t : ℂ)) (Icc q 4) := by
    intro t inside
    have positive : 0<t := by linarith [inside.1]
    exact (Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log positive.ne')).continuousWithinAt
  obtain ⟨bound,bounds⟩ := isCompact_Icc.exists_bound_of_continuousOn regular
  have logarithm : Measurable (fun t : ℝ => (Real.log |t| : ℂ)) := by fun_prop
  apply (Lp.memLp (tateWindow coordinate value)).of_le_mul
    (f := positionRaw coordinate value) (c := bound)
    (logarithm.aestronglyMeasurable.mul
      (Lp.stronglyMeasurable (tateWindow coordinate value)).aestronglyMeasurable)
  have raw := sourceAnnulusCut_coeFn (tateWindow coordinate value)
  rw [actual_tate_window_supported coordinate value even] at raw
  filter_upwards [raw] with t supported
  change ‖(Real.log |t| : ℂ)*tateWindow coordinate value t‖≤bound*‖tateWindow coordinate value t‖
  by_cases inside : q < |t| ∧ |t|≤4
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (bounds |t| ⟨inside.1.le,inside.2⟩) (norm_nonneg _)
  · have empty : tateWindow coordinate value t=0 := supported.trans (if_neg inside)
    simpa only [empty,mul_zero,norm_zero] using (le_rfl : (0 : ℝ)≤0)

def tateWindowPosition (coordinate : BurnolCompletedMellinCoordinate)
    (value : BurnolL2) (even : reflectL2 value=value) : BurnolL2 :=
  (position_domain coordinate value even).toLp (positionRaw coordinate value)

def tateWindowFrequency (coordinate : BurnolCompletedMellinCoordinate)
    (value : BurnolL2) (even : reflectL2 value=value) : BurnolL2 :=
  fourierL2.symm (tateWindowGamma coordinate value-tateWindowPosition coordinate value even)

theorem actual_tate_window_two_sources (coordinate : BurnolCompletedMellinCoordinate)
    (value : BurnolL2) (even : reflectL2 value=value) :
    LogPair (tateWindow coordinate value) (tateWindowPosition coordinate value even) ∧
      LogPair (fourierL2.symm (tateWindow coordinate value)) (tateWindowFrequency coordinate value even) := by
  have first : LogPair (tateWindow coordinate value) (tateWindowPosition coordinate value even) :=
    (position_domain coordinate value even).coeFn_toLp
  exact ⟨first,inverse_log_from_complete_source _ _ _
    (actual_tate_window_Gamma coordinate value even) first⟩

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.TateWindow
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
