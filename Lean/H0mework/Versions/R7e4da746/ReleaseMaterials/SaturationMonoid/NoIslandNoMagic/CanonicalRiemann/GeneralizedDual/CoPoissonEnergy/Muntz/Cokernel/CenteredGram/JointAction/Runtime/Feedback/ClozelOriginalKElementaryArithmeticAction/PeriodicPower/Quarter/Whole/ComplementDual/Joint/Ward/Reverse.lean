import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Realizer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountingDual
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DualSourceRaw
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Source.Volterra.Window

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward

open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSource.Translator OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKFiniteOrderRelease.UnitPowerJordanSource
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.OriginalB OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.JointSource
open OriginalPaPhysicalGreen
open scoped Topology

local notation "F" => fourierL2
local notation "E" => burnolQuarterZeroExtension
local notation "Rq" => burnolQuarterRestriction
local notation "Hq" => BurnolQuarterIntervalL2
local notation "S" => burnolMeanZeroTruncatedFourier

/-- The independent reverse acts on this actual source, including the original gap-tail field. -/
def reverseFeed (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  fourierL2.symm (quarterWave c) - burnolAmbientEvenPart (burnolAmbientCompletedMellinKernelFormula c) +
    E (correction c.value c.belowOne : Hq)

theorem actual_reverse_feed (c : BurnolCompletedMellinCoordinate) :
    F (reverseFeed c) = jointSource c := by
  rw [reverseFeed, map_add, map_sub, fourierL2.apply_symm_apply]
  rfl

theorem actual_reverse_feed_B (c : BurnolCompletedMellinCoordinate) :
    reverseFeed c =
      fourierL2.symm (quarterWave c) - burnolAmbientEvenPart (burnolAmbientCompletedMellinKernelFormula c) +
        ForcingPrimitive.leadingCoefficient c • E (S (logBFirst c 0) : Hq) -
          E (S (burnolRieszSingleFourierSource c) : Hq) := by
  have field := congrArg (fun state : BurnolQuarterMeanZeroCarrier => (state : Hq))
    (actual_original_dual_correction c)
  change (correction c.value c.belowOne : Hq) =
    ForcingPrimitive.leadingCoefficient c • (S (logBFirst c 0) : Hq) -
      (S (burnolRieszSingleFourierSource c) : Hq) at field
  rw [reverseFeed, field, map_sub, map_smul]
  module

/-- The q head of this same field contains the complete original B/log return, with no mean dropped. -/
theorem actual_reverse_quarter_feed (c : BurnolCompletedMellinCoordinate) :
    Rq (reverseFeed c) =
      Rq (fourierL2.symm (quarterWave c)) -
        Rq (burnolAmbientEvenPart (burnolAmbientCompletedMellinKernelFormula c)) +
          (correction c.value c.belowOne : Hq) := by
  rw [reverseFeed, map_add, map_sub, burnolQuarterRestriction_zeroExtension]

/-- The same outside field is read after the entire q head has been removed. -/
theorem actual_reverse_outside_feed (c : BurnolCompletedMellinCoordinate) :
    reverseFeed c - E (Rq (reverseFeed c)) =
      (fourierL2.symm (quarterWave c) - burnolAmbientEvenPart (burnolAmbientCompletedMellinKernelFormula c)) -
        E (Rq (fourierL2.symm (quarterWave c) -
          burnolAmbientEvenPart (burnolAmbientCompletedMellinKernelFormula c))) := by
  rw [reverseFeed, map_add, burnolQuarterRestriction_zeroExtension, map_add]
  module

theorem actual_reverse_fourier (N : ℕ) (seed : BurnolL2) :
    DualSource.source N (F seed) = F (FiniteForcing.source N seed) := by
  have channel (a : ℝ) : ContinuousChannels.channel 1 a (F seed) =
      F (ContinuousChannels.channel (-1) a seed) := by
    simp only [ContinuousChannels.channel, one_mul, neg_one_mul, map_smul,
      fourierL2_burnolMultiplicativeDilation, neg_neg]
  have integer (n : ℕ) : ContinuousChannels.channel 1 n (F seed) =
      F (Channels.sourceChannel n seed) := by
    simpa only [ContinuousChannels.channel, Channels.sourceChannel, one_mul, neg_one_mul]
      using channel n
  unfold DualSource.source FiniteForcing.source ContinuousChannels.normalization
  simp_rw [integer, channel]
  rw [map_sub, map_sum]
  congr 1
  exact fourierL2.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm
    (ContinuousChannels.channel_integrable (-1) N seed)

/-- The finite reverse is computed on the literal complete joint source, before every projection. -/
theorem actual_joint_reverse_source (c : BurnolCompletedMellinCoordinate) (N : ℕ) :
    DualSource.source N (jointSource c) =
      F (FiniteForcing.source N
        (fourierL2.symm (quarterWave c) - burnolAmbientEvenPart (burnolAmbientCompletedMellinKernelFormula c) +
          ForcingPrimitive.leadingCoefficient c • E (S (logBFirst c 0) : Hq) -
            E (S (burnolRieszSingleFourierSource c) : Hq))) := by
  rw [← actual_reverse_feed c, actual_reverse_fourier, actual_reverse_feed_B]

def cutChannel (a : ℝ) (value : BurnolL2) : BurnolL2 :=
  sourceAnnulusCut (ContinuousChannels.channel 1 a value) -
    ContinuousChannels.channel 1 a (sourceAnnulusCut value)

def annulusMask (x : ℝ) : ℂ := if (1 / 4 : ℝ) < |x| ∧ |x| ≤ 4 then 1 else 0

/-- These are the actual source rows crossing the two fixed cut boundaries. -/
theorem actual_cut_channel_raw (a : ℝ) (positive : 0 < a) (value : BurnolL2) :
    (cutChannel a value : ℝ → ℂ) =ᵐ[volume]
      fun x => (annulusMask x - annulusMask (a * x)) * value (a * x) := by
  have raw (v : BurnolL2) : (ContinuousChannels.channel 1 a v : ℝ → ℂ) =ᵐ[volume]
      fun x => v (a * x) := DualSourceRaw.channel_coeFn v _ (Filter.Eventually.of_forall (fun _ => rfl)) a positive
  have moved := (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ)) positive.ne').ae
    (sourceAnnulusCut_coeFn value)
  filter_upwards [Lp.coeFn_sub (sourceAnnulusCut (ContinuousChannels.channel 1 a value))
      (ContinuousChannels.channel 1 a (sourceAnnulusCut value)),
    sourceAnnulusCut_coeFn (ContinuousChannels.channel 1 a value), raw value,
    raw (sourceAnnulusCut value), moved] with x difference cut first second movedCut
  simp only [smul_eq_mul] at movedCut
  rw [cutChannel, difference, Pi.sub_apply, cut, first, second, movedCut]
  dsimp only [annulusMask]
  split_ifs <;> ring

theorem cut_channel_integrable (N : ℕ) (value : BurnolL2) :
    IntegrableOn (fun a : ℝ => cutChannel a value) (Ioc 0 (N : ℝ)) :=
  (sourceAnnulusCut.integrable_comp (ContinuousChannels.channel_integrable 1 N value)).sub
    (ContinuousChannels.channel_integrable 1 N (sourceAnnulusCut value))

def cutBoundaryStock (N : ℕ) (value : BurnolL2) : BurnolL2 :=
  (∑ n ∈ Finset.Ico 1 N, cutChannel n value) -
    ∫ a : ℝ in Ioc 0 (N : ℝ), cutChannel a value

/-- The same N keeps both integer crossings and the full continuous normalization. -/
theorem actual_cut_boundary_stock (N : ℕ) (value : BurnolL2) :
    sourceAnnulusCut (DualSource.source N value) - DualSource.source N (sourceAnnulusCut value) =
      cutBoundaryStock N value := by
  unfold DualSource.source cutBoundaryStock cutChannel
  rw [map_sub, map_sum,
    ← sourceAnnulusCut.integral_comp_comm (ContinuousChannels.channel_integrable 1 N value),
    integral_sub (sourceAnnulusCut.integrable_comp (ContinuousChannels.channel_integrable 1 N value))
      (ContinuousChannels.channel_integrable 1 N (sourceAnnulusCut value)),
    Finset.sum_sub_distrib]
  module

theorem actual_joint_cut_boundary_stock (c : BurnolCompletedMellinCoordinate) (N : ℕ) :
    sourceAnnulusCut (DualSource.source N (jointSource c)) -
      DualSource.source N (sourceAnnulusCut (jointSource c)) =
        cutBoundaryStock N (jointSource c) := actual_cut_boundary_stock N (jointSource c)

/-- Every integer reverse channel misses the compact head; its continuous normalization is kept separately. -/
theorem actual_compact_cut_channel_zero (a : ℝ) (large : 1 ≤ a) (state : Hq) :
    cutChannel a (E state) = 0 := by
  have positive : 0 < a := lt_of_lt_of_le (by norm_num) large
  have moved := (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ)) positive.ne').ae
    (burnolQuarterZeroExtension_coe state)
  apply Lp.ext
  filter_upwards [actual_cut_channel_raw a positive (E state), moved, Lp.coeFn_zero ℂ 2 volume]
    with x cut extended zeroAt
  simp only [smul_eq_mul] at extended
  rw [cut, extended, zeroAt]
  by_cases inside : |a * x| ≤ (1 / 4 : ℝ)
  · have smaller : |x| ≤ |a * x| := by
      rw [abs_mul, abs_of_pos positive]
      nlinarith [abs_nonneg x]
    have small : |x| ≤ (1 / 4 : ℝ) := smaller.trans inside
    have first : annulusMask x = 0 := if_neg (fun h => (not_lt.mpr small) h.1)
    have second : annulusMask (a * x) = 0 := if_neg (fun h => (not_lt.mpr inside) h.1)
    rw [first, second, sub_self, zero_mul]
    rfl
  · rw [indicator_of_notMem (show a * x ∉ symmetricInterval (1 / 4 : ℝ) from
      fun h => inside (abs_le.mpr h))]
    simp

theorem actual_compact_annulus_zero (state : Hq) : sourceAnnulusCut (E state) = 0 := by
  apply Lp.ext
  filter_upwards [sourceAnnulusCut_coeFn (E state), burnolQuarterZeroExtension_coe state,
    Lp.coeFn_zero ℂ 2 volume] with x cut extended zeroAt
  rw [cut, zeroAt]
  by_cases band : (1 / 4 : ℝ) < |x| ∧ |x| ≤ 4
  · rw [if_pos band, extended, indicator_of_notMem (show x ∉ symmetricInterval (1 / 4 : ℝ) from
      fun h => (not_lt.mpr (abs_le.mpr h)) band.1)]
    rfl
  · rw [if_neg band]
    rfl

/-- The entire compact head has an exact continuous-source debit; integer invisibility does not delete it. -/
theorem actual_compact_cut_stock (N : ℕ) (state : Hq) :
    cutBoundaryStock N (E state) =
      -sourceAnnulusCut (∫ a : ℝ in Ioc 0 (N : ℝ), ContinuousChannels.channel 1 a (E state)) := by
  rw [← actual_cut_boundary_stock, actual_compact_annulus_zero]
  have dualZero : DualSource.source N 0 = 0 := by
    simp only [CountingDual.dual_eq_adjoint, map_zero]
  rw [dualZero, sub_zero]
  unfold DualSource.source
  rw [map_sub, map_sum]
  have integer (n : ℕ) (inside : n ∈ Finset.Ico 1 N) :
      sourceAnnulusCut (ContinuousChannels.channel 1 n (E state)) = 0 := by
    have large : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ico.mp inside).1
    have actual := actual_compact_cut_channel_zero n large state
    simpa only [cutChannel, actual_compact_annulus_zero, ContinuousChannels.channel, map_zero,
      smul_zero, sub_zero] using actual
  rw [Finset.sum_eq_zero integer, zero_sub]

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
