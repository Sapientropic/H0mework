import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.PairedDrive

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszSource OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKPairedBEulerJunctionSource OriginalKPairedBEulerJunctionSource.BandFullStockEuler
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactForward OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactPaired
open scoped Topology InnerProductSpace ContDiff
open private fourier_raw_even_of_fixed from
  H0mework.Versions.R7e4da746.Arithmetic.RieszFinitePairing.ExteriorRaw
open private forward_fourier from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeGramSource
open private dual_dilation from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.CountingCut
local notation "q" => (1 / 4 : ℝ)
local notation "h" => junctionShift
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "E" => burnolQuarterZeroExtension
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "F" => fourierL2
local notation "K" => burnolCompletedMellinRieszVector
local notation "P" => burnolEvenAmbientProjection
local notation "Q" => pairedBurnolMultiplicativeDilation h

def pairedReturnProgramme (c : BurnolCompletedMellinCoordinate) (i : Fin 2) : BurnolL2 :=
  InfiniteWeightedProgram.program
    (deriv (weight (burnolMeanZeroFourierRaw (sourcePartner c i)))) burnolUnitCountingPrimitiveL2

private theorem partner_fixed (c : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    reflectRestricted q (sourcePartner c i : Hq) = (sourcePartner c i : Hq) := by
  fin_cases i
  · exact source_correction_even c 1
  · exact source_correction_even c 0

private theorem partner_even (c : BurnolCompletedMellinCoordinate) (i : Fin 2)
    (x : ℝ) (_inside : x ∈ symmetricInterval q) :
    burnolMeanZeroFourierRaw (sourcePartner c i) |x| = burnolMeanZeroFourierRaw (sourcePartner c i) x := by
  have even (x : ℝ) : burnolMeanZeroFourierRaw (sourcePartner c i) (-x) =
      burnolMeanZeroFourierRaw (sourcePartner c i) x := by
    unfold burnolMeanZeroFourierRaw
    rw [fourier_raw_even_of_fixed _ (partner_fixed c i) x]
  by_cases positive : 0 ≤ x
  · rw [abs_of_nonneg positive]
  · rw [abs_of_neg (lt_of_not_ge positive), even]

private theorem actual_paired_return_graph (c : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    Tendsto (fun N : ℕ => FiniteForcing.source N (E (S (sourcePartner c i) : Hq))) atTop
      (𝓝 (pairedReturnProgramme c i)) ∧
    Tendsto (fun N : ℕ => DualSource.source N (E (S (sourcePartner c i) : Hq))) atTop
      (𝓝 (poissonPair (pairedReturnProgramme c i))) := by
  let raw := burnolMeanZeroFourierRaw (sourcePartner c i)
  have smooth := OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.Derivative.actual_return_contDiff (sourcePartner c i)
  obtain ⟨weightDerivative, slopeContinuous, measured, domain, head⟩ :=
    actual_compact_c1_inputs (S (sourcePartner c i) : Hq) raw (deriv raw)
      (burnolMeanZeroFourier_ae_raw _) (partner_even c i)
      smooth.continuous.measurable smooth.continuous.continuousOn
      (smooth.continuous_deriv (by norm_num)).continuousOn
      (fun x _ _ => (smooth.differentiable (by norm_num) x).hasDerivAt)
  exact ⟨actual_compact_forward _ raw (burnolMeanZeroFourier_ae_raw _) (partner_even c i)
      weightDerivative slopeContinuous measured domain head,
    actual_compact_reverse _ raw (burnolMeanZeroFourier_ae_raw _) (partner_even c i)
      weightDerivative slopeContinuous domain head⟩

private theorem correction_source (c : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    E (sourceCorrection c i : Hq) = E (sourceDrive c i : Hq) - E (S (sourcePartner c i) : Hq) := by
  have source : sourceCorrection c i + S (sourcePartner c i) = sourceDrive c i := by
    fin_cases i
    · exact source_B_first c
    · exact (add_comm _ _).trans (source_B_second c)
  have quarter := congrArg (fun state : M => (state : Hq)) (eq_sub_of_add_eq source)
  simpa only [Submodule.coe_sub, map_sub] using congrArg E quarter

def pairedCorrectionForward (c : BurnolCompletedMellinCoordinate) (i : Fin 2) : BurnolL2 :=
  pairedDriveForward c i - pairedReturnProgramme c i

def pairedCorrectionReverse (c : BurnolCompletedMellinCoordinate) (i : Fin 2) : BurnolL2 :=
  pairedDriveReverse c i - poissonPair (pairedReturnProgramme c i)

/-- The inverse fibres retain the original drive jumps and the complete smooth return programme. -/
theorem actual_paired_correction_forward (c : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    Tendsto (fun N : ℕ => FiniteForcing.source N (E (sourceCorrection c i : Hq))) atTop
      (𝓝 (pairedCorrectionForward c i)) := by
  have source := (actual_paired_drive_forward c i).sub (actual_paired_return_graph c i).1
  exact source.congr' (Eventually.of_forall (fun N => by
    change _ = CountingDual.sourceCLM N (E (sourceCorrection c i : Hq))
    rw [correction_source, map_sub]
    rfl))

theorem actual_paired_correction_reverse (c : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    Tendsto (fun N : ℕ => DualSource.source N (E (sourceCorrection c i : Hq))) atTop
      (𝓝 (pairedCorrectionReverse c i)) := by
  have source := (actual_paired_drive_reverse c i).sub (actual_paired_return_graph c i).2
  exact source.congr' (Eventually.of_forall (fun N => by
    rw [correction_source]
    simp only [CountingDual.dual_eq_adjoint, map_sub]))

def pairedWholeCorrectionForward (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  pairedCorrectionForward c 0 + F (pairedCorrectionReverse c 1)

def pairedWholeCorrectionReverse (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  pairedCorrectionReverse c 0 + F (pairedCorrectionForward c 1)

theorem actual_paired_whole_correction_forward (c : BurnolCompletedMellinCoordinate) :
    Tendsto (fun N : ℕ => FiniteForcing.source N (correctionRaw c)) atTop
      (𝓝 (pairedWholeCorrectionForward c)) := by
  have source := (actual_paired_correction_forward c 0).add
    ((fourierL2.continuous.tendsto _).comp (actual_paired_correction_reverse c 1))
  exact source.congr' (Eventually.of_forall (fun N => by
    change _ = CountingDual.sourceCLM N (correctionRaw c)
    rw [correctionRaw, map_add]
    simp only [CountingDual.sourceCLM_apply, forward_fourier]
    rfl))

theorem actual_paired_whole_correction_reverse (c : BurnolCompletedMellinCoordinate) :
    Tendsto (fun N : ℕ => DualSource.source N (correctionRaw c)) atTop
      (𝓝 (pairedWholeCorrectionReverse c)) := by
  have source := (actual_paired_correction_reverse c 0).add
    ((fourierL2.continuous.tendsto _).comp (actual_paired_correction_forward c 1))
  exact source.congr' (Eventually.of_forall (fun N => by
    dsimp only [Function.comp_apply]
    conv_rhs => rw [correctionRaw, CountingDual.dual_eq_adjoint, map_add]
    simp only [← CountingDual.dual_eq_adjoint, KCounting.dual_fourier]
    rfl))

private theorem forward_paired (N : ℕ) (value : BurnolL2) :
    FiniteForcing.source N (Q value) = Q (FiniteForcing.source N value) := by
  change CountingDual.sourceCLM N ((1 / 2 : ℂ) •
    (burnolMultiplicativeDilation h value + burnolMultiplicativeDilation (-h) value)) = _
  rw [map_smul, map_add]
  simp only [CountingDual.sourceCLM_apply, SeedCounting.source_dilation]
  rfl

private theorem reverse_paired (N : ℕ) (value : BurnolL2) :
    DualSource.source N (Q value) = Q (DualSource.source N value) := by
  change DualSource.source N ((1 / 2 : ℂ) •
    (burnolMultiplicativeDilation h value + burnolMultiplicativeDilation (-h) value)) = _
  simp only [CountingDual.dual_eq_adjoint, map_smul, map_add]
  simp only [← CountingDual.dual_eq_adjoint, dual_dilation]
  rfl

def pairedCotestForward (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  star (pairedMellinTranslationCharacter c.value h) • KCountingGram.value c -
    Q (KCountingGram.value c) + pairedWholeCorrectionForward c

def pairedCotestReverse (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  star (pairedMellinTranslationCharacter c.value h) • poissonPair (KCountingGram.value c) -
    Q (poissonPair (KCountingGram.value c)) + pairedWholeCorrectionReverse c

private theorem literal_cotest_source (c : BurnolCompletedMellinCoordinate) :
    ((star (pairedMellinTranslationCharacter c.value h) • K c - P (sourceAction c) : BurnolPaAmbientCarrier) : BurnolL2) =
      star (pairedMellinTranslationCharacter c.value h) • (K c : BurnolL2) - sourceAction c + correctionRaw c := by
  rw [Submodule.coe_sub, Submodule.coe_smul, source_action_projection]
  module

/-- This is the actual fixed physical cotest, with both original B fibres and all constants. -/
theorem actual_paired_cotest_forward (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) :
    Tendsto (fun N : ℕ => FiniteForcing.source N
      (((star (pairedMellinTranslationCharacter c.value h) • K c - P (sourceAction c) : BurnolPaAmbientCarrier) : BurnolL2)))
      atTop (𝓝 (pairedCotestForward c)) := by
  have original := KCountingGram.forward_tendsto c zero
  have moved := ((pairedBurnolMultiplicativeDilation h).continuous.tendsto _).comp original
  have source := ((original.const_smul (star (pairedMellinTranslationCharacter c.value h))).sub moved).add
    (actual_paired_whole_correction_forward c)
  exact source.congr' (Eventually.of_forall (fun N => by
    change _ = CountingDual.sourceCLM N _
    rw [literal_cotest_source, map_add, map_sub, map_smul]
    simp only [CountingDual.sourceCLM_apply, sourceAction, forward_paired]
    rfl))

theorem actual_paired_cotest_reverse (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) :
    Tendsto (fun N : ℕ => DualSource.source N
      (((star (pairedMellinTranslationCharacter c.value h) • K c - P (sourceAction c) : BurnolPaAmbientCarrier) : BurnolL2)))
      atTop (𝓝 (pairedCotestReverse c)) := by
  have original := KCounting.original_tendsto c zero
  rw [actual_original_K_paired_value c zero] at original
  have moved := ((pairedBurnolMultiplicativeDilation h).continuous.tendsto _).comp original
  have source := ((original.const_smul (star (pairedMellinTranslationCharacter c.value h))).sub moved).add
    (actual_paired_whole_correction_reverse c)
  exact source.congr' (Eventually.of_forall (fun N => by
    rw [literal_cotest_source]
    simp only [CountingDual.dual_eq_adjoint, map_add, map_sub, map_smul]
    simp only [← CountingDual.dual_eq_adjoint, sourceAction, reverse_paired]
    rfl))

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
