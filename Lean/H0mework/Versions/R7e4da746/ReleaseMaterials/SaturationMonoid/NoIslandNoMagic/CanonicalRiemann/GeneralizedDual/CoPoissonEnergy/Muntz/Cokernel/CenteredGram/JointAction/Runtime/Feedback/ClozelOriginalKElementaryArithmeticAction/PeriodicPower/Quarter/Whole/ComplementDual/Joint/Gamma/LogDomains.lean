import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.CutLog
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaMobiusActedDLogSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.LogDomains
open Complex MeasureTheory Set Filter BurnolPhysicalState
open OriginalGamma.Source.FiniteLogCounting OriginalGamma.Source.RelativeConductorGapReadback
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.CutLog
open scoped InnerProductSpace Topology
open private inverse_log_from_complete_source from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaMobiusActedDLogSource
local notation "q" => (1/4 : ℝ)

private def positionRaw (coordinate : BurnolCompletedMellinCoordinate) (u : ℝ) : ℂ :=
  (Real.log |u| : ℂ)*logValue coordinate u

private theorem position_domain (coordinate : BurnolCompletedMellinCoordinate) :
    MemLp (positionRaw coordinate) 2 volume := by
  have regular : ContinuousOn (fun u : ℝ => (Real.log u : ℂ)) (Icc q 4) := by
    intro u inside
    have positive : 0<u := by linarith [inside.1]
    exact (Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log positive.ne')).continuousWithinAt
  obtain ⟨bound,bounds⟩ := isCompact_Icc.exists_bound_of_continuousOn regular
  have logarithm : Measurable (fun u : ℝ => (Real.log |u| : ℂ)) := by fun_prop
  apply (Lp.memLp (logValue coordinate)).of_le_mul (f := positionRaw coordinate) (c := bound)
    (logarithm.aestronglyMeasurable.mul (Lp.stronglyMeasurable (logValue coordinate)).aestronglyMeasurable)
  filter_upwards [actual_log_raw coordinate] with u source
  change ‖(Real.log |u| : ℂ)*logValue coordinate u‖≤bound*‖logValue coordinate u‖
  by_cases inside : q < |u| ∧ |u|≤4
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (bounds |u| ⟨inside.1.le,inside.2⟩) (norm_nonneg _)
  · have empty : logValue coordinate u=0 := source.trans (if_neg inside)
    simpa only [empty,mul_zero,norm_zero] using (le_rfl : (0 : ℝ)≤0)

def logPosition (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  (position_domain coordinate).toLp (positionRaw coordinate)

def logFrequency (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  fourierL2.symm (logGamma coordinate-logPosition coordinate)

theorem actual_log_position_source (coordinate : BurnolCompletedMellinCoordinate) :
    LogPair (logValue coordinate) (logPosition coordinate) :=
  (position_domain coordinate).coeFn_toLp

/-- The exact cut logarithmic source pays both original logarithmic domains while its Gamma value remains whole. -/
theorem actual_log_two_sources (coordinate : BurnolCompletedMellinCoordinate) :
    LogPair (logValue coordinate) (logPosition coordinate) ∧
      LogPair (fourierL2.symm (logValue coordinate)) (logFrequency coordinate) :=
  ⟨actual_log_position_source coordinate,
    inverse_log_from_complete_source _ _ _ (actual_log_Gamma coordinate) (actual_log_position_source coordinate)⟩

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.LogDomains
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
