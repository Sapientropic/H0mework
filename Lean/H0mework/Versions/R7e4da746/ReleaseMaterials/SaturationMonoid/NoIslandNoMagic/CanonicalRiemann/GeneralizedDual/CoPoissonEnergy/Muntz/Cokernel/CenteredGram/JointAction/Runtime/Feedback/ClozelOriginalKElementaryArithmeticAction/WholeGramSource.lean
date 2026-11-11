import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.UnitResolvent

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.WholeGramSource
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen
open OriginalRieszFinitePairing.CoPoisson OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKCoefficientBFiniteAction OriginalKSourceResolventReconstruction OriginalKExteriorCoPoissonAction
open OriginalKFixedBoundarySourceFibre
open scoped InnerProductSpace Topology

private theorem forward_resolvent (N : Nat) (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    FiniteForcing.source N (sourceResolvent c value) =
      sourceResolvent c (FiniteForcing.source N value) := by
  let action := burnolDirectRightResolventCLM (OriginalPrimitiveRankBalance.conjugateCoordinate c)
  have channel (radius : ℝ) : ContinuousChannels.channel (-1) radius (action value) =
      action (ContinuousChannels.channel (-1) radius value) := by
    simp only [ContinuousChannels.channel, map_smul]
    change (Real.sqrt radius : ℂ)⁻¹ • burnolMultiplicativeDilation (-1*Real.log radius)
      (burnolDirectRightResolvent (star c.value/2) value) =
        (Real.sqrt radius : ℂ)⁻¹ • burnolDirectRightResolvent (star c.value/2)
          (burnolMultiplicativeDilation (-1*Real.log radius) value)
    rw [burnolDirectRightResolvent_dilation]
  have integer (n : Nat) : Channels.sourceChannel n (action value) =
      action (Channels.sourceChannel n value) := by
    simpa only [ContinuousChannels.channel, Channels.sourceChannel, neg_one_mul] using channel n
  change FiniteForcing.source N (action value) = action (FiniteForcing.source N value)
  unfold FiniteForcing.source ContinuousChannels.normalization
  simp_rw [integer, channel]
  rw [map_sub, map_sum]
  congr 1
  exact action.integral_comp_comm (ContinuousChannels.channel_integrable (-1) N value)

/-- The actual forward programme acts on the whole original unit resolvent field. -/
theorem unit_resolvent_forward_finite (c : BurnolCompletedMellinCoordinate) (N : Nat) :
    FiniteForcing.source N (elementarySource c) =
      unitResolventSource c (FiniteForcing.source N ConstantDual.seed) := by
  rw [←elementary_unit_resolvent c]
  change CountingDual.sourceCLM N (unitResolventSource c ConstantDual.seed) = _
  rw [unitResolventSource, map_smul, map_sub, map_smul]
  change _ = (star c.value * GapEuler.gapMean (1/4) c) •
    (FiniteForcing.source N ConstantDual.seed - ((1-star c.value)/2) •
      sourceResolvent c (FiniteForcing.source N ConstantDual.seed))
  simp only [CountingDual.sourceCLM_apply]
  rw [forward_resolvent]

private theorem unit_resolvent_continuous (c : BurnolCompletedMellinCoordinate) :
    Continuous (unitResolventSource c) := by
  let action := burnolDirectRightResolventCLM (OriginalPrimitiveRankBalance.conjugateCoordinate c)
  have expression : unitResolventSource c = fun value =>
      (star c.value * GapEuler.gapMean (1/4) c) •
        (value - ((1-star c.value)/2) • action value) := rfl
  rw [expression]
  fun_prop

theorem elementary_forward_tendsto (c : BurnolCompletedMellinCoordinate) :
    Tendsto (fun N : Nat => FiniteForcing.source N (elementarySource c)) atTop
      (𝓝 (unitResolventSource c ConstantForward.value)) := by
  have source := ((unit_resolvent_continuous c).tendsto ConstantForward.value).comp
    ConstantForward.original_tendsto
  exact source.congr' (Eventually.of_forall (fun N => (unit_resolvent_forward_finite c N).symm))

private theorem forward_fourier (N : Nat) (value : BurnolL2) :
    FiniteForcing.source N (fourierL2 value) = fourierL2 (DualSource.source N value) := by
  have channel (radius : ℝ) : ContinuousChannels.channel (-1) radius (fourierL2 value) =
      fourierL2 (ContinuousChannels.channel 1 radius value) := by
    simp only [ContinuousChannels.channel, one_mul, neg_one_mul, map_smul,
      fourierL2_burnolMultiplicativeDilation]
  have integer (n : Nat) : Channels.sourceChannel n (fourierL2 value) =
      fourierL2 (ContinuousChannels.channel 1 n value) := by
    simpa only [ContinuousChannels.channel, Channels.sourceChannel, neg_one_mul] using channel n
  unfold FiniteForcing.source ContinuousChannels.normalization DualSource.source
  simp_rw [integer, channel]
  rw [map_sub, map_sum]
  congr 1
  exact fourierL2.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm
    (ContinuousChannels.channel_integrable 1 N value)

private theorem forward_boundary (N : Nat) (c : BurnolCompletedMellinCoordinate) (h : ℝ) (value : BurnolL2) :
    FiniteForcing.source N (finiteBoundaryAction c h value) =
      finiteBoundaryAction c h (FiniteForcing.source N value) := by
  change CountingDual.sourceCLM N (finiteBoundaryAction c h value) = _
  unfold finiteBoundaryAction
  rw [map_sub, map_smul, map_smul, map_add]
  change _ = pairedMellinTranslationCharacter c.value h • FiniteForcing.source N value -
    (1/2 : ℂ) • (burnolMultiplicativeDilation h (FiniteForcing.source N value) +
      burnolMultiplicativeDilation (-h) (FiniteForcing.source N value))
  simp only [CountingDual.sourceCLM_apply]
  rw [SeedCounting.source_dilation, SeedCounting.source_dilation]

/-- This whole source is explicit: the original forward unit field and both complete loss channels. -/
def coreForwardSource (c : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolL2 :=
  finiteBoundaryAction c h (unitResolventSource c ConstantForward.value) - (1/2 : ℂ) •
    (FullUnit.fullForward c h 1 - fourierL2 (FullUnit.fullReverse c h 0))

theorem core_forward_finite (c : BurnolCompletedMellinCoordinate) (h : ℝ) (N : Nat) :
    FiniteForcing.source N (sourceCore c h) =
      finiteBoundaryAction c h (unitResolventSource c (FiniteForcing.source N ConstantDual.seed)) -
        (1/2 : ℂ) • (FiniteForcing.source N (FullUnit.fullSource c h 1) -
          fourierL2 (DualSource.source N (FullUnit.fullSource c h 0))) := by
  change CountingDual.sourceCLM N (sourceCore c h) = _
  rw [sourceCore, map_sub, map_smul, map_sub]
  change FiniteForcing.source N (finiteBoundaryAction c h (elementarySource c)) -
    (1/2 : ℂ) • (FiniteForcing.source N (FullUnit.fullSource c h 1) -
      FiniteForcing.source N (fourierL2 (FullUnit.fullSource c h 0))) = _
  rw [forward_boundary, unit_resolvent_forward_finite, forward_fourier]

theorem core_forward_tendsto (c : BurnolCompletedMellinCoordinate) (h : ℝ) (nonnegative : 0 ≤ h) :
    Tendsto (fun N : Nat => FiniteForcing.source N (sourceCore c h)) atTop
      (𝓝 (coreForwardSource c h)) := by
  have continuousBoundary : Continuous (fun value : BurnolL2 => finiteBoundaryAction c h value) := by
    unfold finiteBoundaryAction
    fun_prop
  have elementary := (continuousBoundary.tendsto (unitResolventSource c ConstantForward.value)).comp
    (elementary_forward_tendsto c)
  have fourier := (fourierL2.continuous.tendsto (FullUnit.fullReverse c h 0)).comp
    (FullUnit.full_reverse_tendsto c h nonnegative 0)
  have actual := elementary.sub (((FullUnit.full_forward_tendsto c h nonnegative 1).sub fourier).const_smul (1/2 : ℂ))
  have finite (N : Nat) : FiniteForcing.source N (sourceCore c h) =
      finiteBoundaryAction c h (FiniteForcing.source N (elementarySource c)) - (1/2 : ℂ) •
        (FiniteForcing.source N (FullUnit.fullSource c h 1) -
          fourierL2 (DualSource.source N (FullUnit.fullSource c h 0))) := by
    rw [core_forward_finite, unit_resolvent_forward_finite]
  exact actual.congr' (Eventually.of_forall (fun N => (finite N).symm))

def wholeInput (c : BurnolCompletedMellinCoordinate) (h : ℝ) : Fin 3 → BurnolL2 :=
  ![FullUnit.fullSource c h 0, FullUnit.fullSource c h 1, sourceCore c h]

def wholeForward (c : BurnolCompletedMellinCoordinate) (h : ℝ) : Fin 3 → BurnolL2 :=
  ![FullUnit.fullForward c h 0, FullUnit.fullForward c h 1, coreForwardSource c h]

def wholeReverse (c : BurnolCompletedMellinCoordinate) (h : ℝ) : Fin 3 → BurnolL2 :=
  ![FullUnit.fullReverse c h 0, FullUnit.fullReverse c h 1, coreUnitResolventSource c h]

theorem whole_forward_tendsto (c : BurnolCompletedMellinCoordinate) (h : ℝ) (nonnegative : 0 ≤ h) (i : Fin 3) :
    Tendsto (fun N : Nat => FiniteForcing.source N (wholeInput c h i)) atTop
      (𝓝 (wholeForward c h i)) := by
  fin_cases i
  · exact FullUnit.full_forward_tendsto c h nonnegative 0
  · exact FullUnit.full_forward_tendsto c h nonnegative 1
  · exact core_forward_tendsto c h nonnegative

theorem whole_reverse_tendsto (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0)
    (h : ℝ) (nonnegative : 0 ≤ h) (i : Fin 3) :
    Tendsto (fun N : Nat => DualSource.source N (wholeInput c h i)) atTop
      (𝓝 (wholeReverse c h i)) := by
  fin_cases i
  · exact FullUnit.full_reverse_tendsto c h nonnegative 0
  · exact FullUnit.full_reverse_tendsto c h nonnegative 1
  · exact actual_core_unit_resolvent_action c zero h nonnegative

/-- The same cutoff acts on the complete original inputs before either whole Gram is read. -/
theorem finite_whole_gram (c : BurnolCompletedMellinCoordinate) (h : ℝ) (N : Nat) (i j : Fin 3) :
    inner ℂ (FiniteForcing.source N (wholeInput c h i)) (FiniteForcing.source N (wholeInput c h j)) =
      inner ℂ (DualSource.source N (wholeInput c h i)) (DualSource.source N (wholeInput c h j)) :=
  DualSourceGram.finite_gram N (wholeInput c h i) (wholeInput c h j)

/-- All nine entries retain the whole L2 channels, including their full unit and both means. -/
theorem whole_gram (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0)
    (h : ℝ) (nonnegative : 0 ≤ h) (i j : Fin 3) :
    inner ℂ (wholeForward c h i) (wholeForward c h j) =
      inner ℂ (wholeReverse c h i) (wholeReverse c h j) := by
  have forward := (whole_forward_tendsto c h nonnegative i).inner (𝕜 := ℂ)
    (whole_forward_tendsto c h nonnegative j)
  have reverse := (whole_reverse_tendsto c zero h nonnegative i).inner (𝕜 := ℂ)
    (whole_reverse_tendsto c zero h nonnegative j)
  have same := forward.congr' (Eventually.of_forall (fun N => finite_whole_gram c h N i j))
  exact tendsto_nhds_unique same reverse

end OriginalKElementaryArithmeticAction.WholeGramSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
