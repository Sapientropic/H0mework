import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.PairedCotest

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKPairedBEulerJunctionSource OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactPaired
open scoped Topology InnerProductSpace
open private dual_tate from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactPaired
open private forward_fourier from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeGramSource
local notation "h" => junctionShift
local notation "T" => burnolTateReciprocalL2
local notation "R" => burnolDirectRightResolventCLM
local notation "K" => burnolCompletedMellinRieszVector
local notation "P" => burnolEvenAmbientProjection

private theorem forward_tate (N : ℕ) (value : BurnolL2) :
    FiniteForcing.source N (T value) = T (DualSource.source N value) := by
  have source := congrArg T (dual_tate N (T value))
  rw [burnolTateReciprocalL2_involutive, burnolTateReciprocalL2_involutive] at source
  exact source.symm

private theorem reverse_fourier_symm (N : ℕ) (value : BurnolL2) :
    DualSource.source N (fourierL2.symm value) = fourierL2.symm (FiniteForcing.source N value) := by
  have source := congrArg fourierL2.symm (forward_fourier N (fourierL2.symm value))
  rw [fourierL2.apply_symm_apply, fourierL2.symm_apply_apply] at source
  exact source.symm

private theorem reverse_resolvent (N : ℕ) (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    DualSource.source N (R c value) = R c (DualSource.source N value) := by
  have channel (radius : ℝ) : ContinuousChannels.channel 1 radius (R c value) =
      R c (ContinuousChannels.channel 1 radius value) := by
    simp only [ContinuousChannels.channel, map_smul, one_mul]
    change (Real.sqrt radius : ℂ)⁻¹ • burnolMultiplicativeDilation (Real.log radius)
      (burnolDirectRightResolvent (c.value / 2) value) =
      (Real.sqrt radius : ℂ)⁻¹ • burnolDirectRightResolvent (c.value / 2)
        (burnolMultiplicativeDilation (Real.log radius) value)
    rw [burnolDirectRightResolvent_dilation]
  unfold DualSource.source
  simp_rw [channel]
  rw [map_sub, map_sum]
  congr 1
  exact (R c).integral_comp_comm (ContinuousChannels.channel_integrable 1 N value)

private theorem reverse_power (N : ℕ) (c : BurnolCompletedMellinCoordinate) (j : ℕ) (value : BurnolL2) :
    DualSource.source N (((R c)^j) value) = ((R c)^j) (DualSource.source N value) := by
  induction j with
  | zero => simp only [pow_zero, one_apply_eq_self]
  | succ j previous =>
    rw [pow_succ', mul_apply_eq_comp, reverse_resolvent, previous, mul_apply_eq_comp]

/-- The cotest of the true outside source has its full strong forward value before the source is integrated. -/
theorem actual_paired_cotest_tate_forward (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) :
    Tendsto (fun N : ℕ => FiniteForcing.source N (T
      (((star (pairedMellinTranslationCharacter c.value h) • K c - P (sourceAction c) : BurnolPaAmbientCarrier) : BurnolL2))))
      atTop (𝓝 (T (pairedCotestReverse c))) := by
  have source := (burnolTateReciprocalL2.continuous.tendsto _).comp (actual_paired_cotest_reverse c zero)
  exact source.congr' (Eventually.of_forall (fun N => (forward_tate N _).symm))

/-- The actual original R power and inverse Fourier act on the complete generated cotest value. -/
theorem actual_paired_cotest_whole_reverse (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (j : ℕ) :
    Tendsto (fun N : ℕ => DualSource.source N (((R c)^j) (fourierL2.symm
      (((star (pairedMellinTranslationCharacter c.value h) • K c - P (sourceAction c) : BurnolPaAmbientCarrier) : BurnolL2)))))
      atTop (𝓝 (((R c)^j) (fourierL2.symm (pairedCotestForward c)))) := by
  have fourier := (fourierL2.symm.continuous.tendsto _).comp (actual_paired_cotest_forward c zero)
  have source := (((R c)^j).continuous.tendsto _).comp fourier
  exact source.congr' (Eventually.of_forall (fun N => by
    dsimp only [Function.comp_apply]
    rw [reverse_power, reverse_fourier_symm]))

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
