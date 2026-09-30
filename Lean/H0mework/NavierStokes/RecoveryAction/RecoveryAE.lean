import H0mework.NavierStokes.RecoveryAction.RecoveryAdvance
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Order.LeftRightNhds

set_option autoImplicit false
open scoped BigOperators ENNReal Topology

namespace SaturationMonoid.NavierStokes.NativeRecoveryAEWindows

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientWholeStateSourceOwnedLocalBarrier
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open NativeRecoveryControlProducer NativeRecoveryWindowAdvance NativeEndpointPositiveTime

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}

def enstrophy (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ) (time : ℝ) : ℝ :=
  finiteStateVorticityCoefficientEnstrophy (wholeRestartModes radius) ((ledger.family.stage radius).trajectory time)

theorem enstrophy_nonnegative (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ) (time : ℝ) : 0 ≤ enstrophy ledger radius time := by
  unfold enstrophy finiteStateVorticityCoefficientEnstrophy
  exact Finset.sum_nonneg fun _ _ => complexCoordinateAmplitudeSq_nonneg _

theorem enstrophy_integrable (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ) : Integrable (enstrophy ledger radius) (volume.restrict (Icc (0 : ℝ) 1)) := by
  have original := ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger.GeneratedWholeRestartVelocityEndpointGalerkinStage.vorticityMass_intervalIntegrable
    (ledger.family.stage radius) ⟨1, by norm_num⟩
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
  change IntervalIntegrable (fun time => finiteStateVorticityCoefficientEnstrophy
    (wholeRestartModes radius) ((ledger.family.stage radius).trajectory time)) volume 0 1
  simpa only [enstrophy, finiteStateVorticityMass, finiteStateVorticityCoefficientEnstrophy,
    complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] using original

theorem enstrophy_lintegral_le (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ) :
    (∫⁻ time in Icc (0 : ℝ) 1, ENNReal.ofReal (enstrophy ledger radius time)) ≤ ENNReal.ofReal (kineticAllowance ledger) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (enstrophy_integrable ledger radius)
    (Eventually.of_forall (enstrophy_nonnegative ledger radius))]
  apply ENNReal.ofReal_le_ofReal
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  exact enstrophy_integral_le ledger radius le_rfl zero_le_one le_rfl

theorem ae_bounded_source_subsequence
    (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger) :
    ∀ᵐ time ∂volume.restrict (Icc (0 : ℝ) 1),
      ∃ ceiling : ℝ, ∃ extraction : ℕ → ℕ, StrictMono extraction ∧
        ∀ index, enstrophy ledger (receipt.core.subsequence (extraction index)) time + 1 ≤ ceiling := by
  let rows (index : ℕ) (time : ℝ) := ENNReal.ofReal (enstrophy ledger (receipt.core.subsequence index) time)
  have measurable (index) : AEMeasurable (rows index) (volume.restrict (Icc (0 : ℝ) 1)) :=
    (enstrophy_integrable ledger (receipt.core.subsequence index)).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have integral : (∫⁻ time in Icc (0 : ℝ) 1, liminf (fun index => rows index time) atTop) ≤
      ENNReal.ofReal (kineticAllowance ledger) := by
    apply (lintegral_liminf_le' measurable).trans
    exact liminf_le_of_frequently_le' (Frequently.of_forall fun index => enstrophy_lintegral_le ledger (receipt.core.subsequence index))
  have limitMeasurable : AEMeasurable (fun time => liminf (fun index => rows index time) atTop)
      (volume.restrict (Icc (0 : ℝ) 1)) := by
    simp only [liminf_eq_iSup_iInf_of_nat']
    exact .iSup fun first => .iInf fun index => measurable (index + first)
  have finite := ae_lt_top' limitMeasurable (lt_of_le_of_lt integral ENNReal.ofReal_lt_top).ne
  filter_upwards [finite] with time finite
  obtain ⟨bound, bounded⟩ := ENNReal.exists_nat_gt finite.ne
  have frequent : ∃ᶠ index in atTop, rows index time < (bound : ℝ≥0∞) := frequently_lt_of_liminf_lt (by isBoundedDefault) bounded
  obtain ⟨extraction, strict, extracted⟩ := extraction_of_frequently_atTop frequent
  refine ⟨(bound : ℝ) + 1, extraction, strict, ?_⟩
  intro index
  have positive : (0 : ℝ) < bound := by
    have positiveNat : 0 < bound := by
      by_contra nonpositive
      have zero : bound = 0 := Nat.eq_zero_of_not_pos nonpositive
      simp only [zero, Nat.cast_zero, not_lt_zero] at bounded
    exact_mod_cast positiveNat
  have realBound : enstrophy ledger (receipt.core.subsequence (extraction index)) time < (bound : ℝ) := by
    apply (ENNReal.ofReal_lt_ofReal_iff positive).mp
    simpa only [rows, ENNReal.ofReal_natCast] using extracted index
  linarith

def futureDuration (ceiling terminal anchor : ℝ) : ℝ :=
  min (sourceOwnedWholeStateDuration nu ceiling) ((terminal - anchor) / 2)

theorem source_ae_future_span
    (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (terminal : ℝ) (terminalLe : terminal ≤ 1) :
    ∀ᵐ anchor ∂volume.restrict (Icc (0 : ℝ) 1), anchor < terminal →
      Nonempty {span : ControlSpan receipt terminal // span.first = anchor} := by
  filter_upwards [ae_bounded_source_subsequence receipt, ae_restrict_mem measurableSet_Icc]
    with anchor source inside
  intro before
  obtain ⟨ceiling, extraction, strict, initial⟩ := source
  let duration := futureDuration (nu := nu) ceiling terminal anchor
  have positive : 0 < duration := lt_min (sourceOwnedWholeStateDuration_pos nu ceiling) (half_pos (sub_pos.mpr before))
  have lastLt : anchor + duration < terminal := by
    have bound : duration ≤ (terminal - anchor) / 2 := min_le_right _ _
    linarith
  refine ⟨⟨{
    first := anchor
    last := anchor + duration
    first_nonnegative := inside.1
    ordered := by linarith
    last_lt := lastLt
    terminal_le_one := terminalLe
    ceiling := ceiling
    activity := localActivityAllowance nu ceiling duration
    extraction := extraction
    extraction_strict := strict
    paid := Eventually.of_forall ?_ }, rfl⟩⟩
  intro index
  exact endpoint_local_control ledger (receipt.core.subsequence (extraction index)) anchor ceiling duration
    inside.1 positive.le (lastLt.le.trans terminalLe) (initial index) (min_le_left _ _)

def regularSet (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger) (terminal : ℝ) : Set ℝ :=
  ⋃ span : ControlSpan receipt terminal, Ioo span.first span.last

theorem regularSet_open (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (terminal : ℝ) : IsOpen (regularSet receipt terminal) :=
  isOpen_iUnion fun _ => isOpen_Ioo

theorem isolated_complement_of_right_interval {domain : Set ℝ} {time last : ℝ}
    (ordered : time < last) (covered : Ioo time last ⊆ domain) :
    𝓝[domainᶜ ∩ Ioi time] time = ⊥ := by
  rw [← empty_mem_iff_bot, mem_nhdsWithin_iff_exists_mem_nhds_inter]
  refine ⟨Iio last, Iio_mem_nhds ordered, ?_⟩
  intro point inside
  exact (inside.2.1 (covered ⟨inside.2.2, inside.1⟩)).elim

theorem ae_regularSet (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (terminal : ℝ) (terminalLe : terminal ≤ 1) :
    ∀ᵐ time ∂volume.restrict (Ioo (0 : ℝ) terminal), time ∈ regularSet receipt terminal := by
  let domain := regularSet receipt terminal
  let exceptional := {time ∈ domainᶜ | 𝓝[domainᶜ ∩ Ioi time] time = ⊥}
  have countable : exceptional.Countable := countable_setOfPred_isolated_right_within
  have outside : ∀ᵐ time ∂(volume : Measure ℝ), time ∉ exceptional := by
    rw [ae_iff]
    convert! countable.measure_zero volume using 2
    ext point
    simp only [mem_ofPred_eq, not_not]
  have subset : Ioo (0 : ℝ) terminal ⊆ Icc (0 : ℝ) 1 :=
    fun _ inside => ⟨inside.1.le, inside.2.le.trans terminalLe⟩
  have generated := ae_restrict_of_ae_restrict_of_subset subset
    (source_ae_future_span receipt terminal terminalLe)
  filter_upwards [generated, ae_restrict_of_ae outside, ae_restrict_mem measurableSet_Ioo]
    with time source excluded inside
  by_contra missing
  obtain ⟨⟨span, same⟩⟩ := source inside.2
  have positive : time < span.last := same ▸ span.ordered
  have covered : Ioo time span.last ⊆ domain := by
    intro point member
    apply mem_iUnion.mpr
    exact ⟨span, by simpa only [same] using member⟩
  exact excluded ⟨missing, isolated_complement_of_right_interval positive covered⟩

theorem source_ae_control_span (initial : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time ∂volume.restrict (Ioo (0 : ℝ) (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1),
      ∃ span : ControlSpan (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial)
          (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1,
        span.first < time ∧ time < span.last := by
  have actual := ae_regularSet (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial)
    (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1
    (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.2.2
  filter_upwards [actual] with time member
  exact mem_iUnion.mp member

end
end SaturationMonoid.NavierStokes.NativeRecoveryAEWindows
