import H0mework.NavierStokes.RecoveryAction.RecoveryAE
import H0mework.NavierStokes.RecoveryAction.RecoveryJets

set_option autoImplicit false
open scoped ENNReal Topology

namespace SaturationMonoid.NavierStokes.NativeRecoveryRegularDomain

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open NativeSpacetimeControl NativeRecoveryStrongWindow NativeRecoveryTimeJets NativeRecoveryWindowAdvance
open NativeRecoveryAEWindows

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}

def regularDomain (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (terminal : ℝ) : Set Spacetime := regularSet receipt terminal ×ˢ univ

theorem regularDomain_open (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (terminal : ℝ) : IsOpen (regularDomain receipt terminal) := (regularSet_open receipt terminal).prod isOpen_univ

theorem field_contDiffAt_of_regular
    (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (terminal : ℝ) (pair : Spacetime) (member : pair.1 ∈ regularSet receipt terminal) :
    ContDiffAt ℝ (↑(⊤ : ℕ∞)) (field receipt) pair := by
  obtain ⟨span, inside⟩ := mem_iUnion.mp member
  let delta := (pair.1 - span.first) / 2
  have deltaPositive : 0 < delta := half_pos (sub_pos.mpr inside.1)
  have fits : span.first + delta < span.last := by dsimp [delta]; linarith [inside.1, inside.2]
  let window := span.toControlledWindow delta deltaPositive fits
  have after : window.first < pair.1 := by change span.first + delta < pair.1; dsimp [delta]; linarith [inside.1]
  have before : pair.1 < window.last := inside.2
  have belongs : pair ∈ NativeRecoveryTimeJets.slab window := ⟨⟨after.le, before.le⟩, trivial⟩
  have near : NativeRecoveryTimeJets.slab window ∈ 𝓝 pair :=
    prod_mem_nhds (Icc_mem_nhds after before) univ_mem
  exact (field_contDiffOn window pair belongs).contDiffAt near

theorem field_regular_contDiffOn
    (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger) (terminal : ℝ) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (field receipt) (regularDomain receipt terminal) :=
  fun pair member => (field_contDiffAt_of_regular receipt terminal pair member.1).contDiffWithinAt

theorem field_regular_frechet_Lp
    (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (terminal : ℝ) (order : ℕ) (exponent : ℝ≥0∞) {domain : Set Spacetime}
    (compact : IsCompact domain) (contained : domain ⊆ regularDomain receipt terminal) :
    ∃ budget : ℝ, 0 ≤ budget ∧
      MemLp (iteratedFDerivWithin ℝ order (field receipt) (regularDomain receipt terminal))
        exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDerivWithin ℝ order (field receipt) (regularDomain receipt terminal))
        exponent (volume.restrict domain) ≤ ENNReal.ofReal budget * volume domain ^ (1 / exponent.toReal) :=
  spacetime_frechet_Lp_of_smooth _ _ (field_regular_contDiffOn receipt terminal)
    (regularDomain_open receipt terminal).uniqueDiffOn order exponent compact contained

theorem source_ae_actual_spacetime_control (initial : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time ∂volume.restrict (Ioo (0 : ℝ) (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1),
      ∀ point : PhysicalSpace,
        ContDiffAt ℝ (↑(⊤ : ℕ∞)) (field (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial)) (time, point) := by
  have actual := ae_regularSet (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial)
    (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1
    (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.2.2
  filter_upwards [actual] with time regular
  intro point
  exact field_contDiffAt_of_regular _ _ (time, point) regular

theorem uncovered_times_null
    (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (terminal : ℝ) (terminalLe : terminal ≤ 1) :
    volume (Ioo (0 : ℝ) terminal \ regularSet receipt terminal) = 0 := by
  have actual := ae_regularSet receipt terminal terminalLe
  rw [ae_restrict_iff' measurableSet_Ioo, ae_iff] at actual
  convert! actual using 2
  ext time
  simp only [Set.mem_sdiff, mem_ofPred_eq, Classical.not_imp]

end
end SaturationMonoid.NavierStokes.NativeRecoveryRegularDomain
