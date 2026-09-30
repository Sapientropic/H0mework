import H0mework.NavierStokes.PhysicalJets.ChartVorticity
import H0mework.NavierStokes.SourceAction.RootCurrentControl

set_option autoImplicit false
open scoped ContDiff ENNReal

namespace SaturationMonoid.NavierStokes.NativeUnifiedVorticityControl

open PhysicsCore ProofFreeRicherAnholonomicSource Stage9CU
open NativeFinitePrefixTimeChart NativeCurrentPhysicalReadout
open NativeTimeChartVorticityReadout NativeFullOrderSynthesis
open NativeSourceUnifiedActionSplice (target target_is_original_next)
open ThreeDimensionalPeriodicCoarseFilterCore MeasureTheory Set

noncomputable section

def read (index : ℕ) : BasePoint → PhysicalSpace :=
  Fluid.curl (field index) ∘ pullback index

theorem read_original (index : ℕ) (point : BasePoint) (inside : point ∈ physicalDomain index) :
    read index point =
      spatialField ((receipt index).wholePath ⟨point 0, inside.1.le, inside.2.le⟩) (spatialRead point) :=
  unified_curl_physical_read index (point 0) inside (spatialRead point)

theorem read_contDiffAt (index : ℕ) (point : BasePoint) (inside : point ∈ physicalDomain index) :
    ContDiffAt ℝ ∞ (read index) point :=
  (Fluid.curl_contDiff (field_contDiff index)).contDiffAt.comp point (pullback_contDiffAt index point inside)

theorem source_all_order_Lp (index order : ℕ) (exponent : ℝ≥0∞)
    {domain : Set BasePoint} (compact : IsCompact domain) (contained : domain ⊆ physicalDomain index) :
    ∃ bound : ℝ,
      MemLp (iteratedFDeriv ℝ order (read index)) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order (read index)) exponent (volume.restrict domain) ≤
        ENNReal.ofReal bound * volume domain ^ (1 / exponent.toReal) := by
  let : IsFiniteMeasure (volume.restrict domain) := ⟨by simpa using compact.measure_lt_top (μ := volume)⟩
  have continuity : ContinuousOn (iteratedFDeriv ℝ order (read index)) domain := fun point inside =>
    ((read_contDiffAt index point (contained inside)).continuousAt_iteratedFDeriv
      (WithTop.coe_le_coe.mpr le_top)).continuousWithinAt
  obtain ⟨bound, bounded⟩ := compact.exists_bound_of_continuousOn continuity
  have paid : ∀ᵐ point ∂volume.restrict domain, ‖iteratedFDeriv ℝ order (read index) point‖ ≤ bound := by
    filter_upwards [ae_restrict_mem compact.measurableSet] with point inside
    exact bounded point inside
  exact ⟨bound, MemLp.of_bound (continuity.aestronglyMeasurable compact.measurableSet) bound paid,
    by simpa [mul_comm] using eLpNorm_le_of_ae_bound (p := exponent) paid⟩

theorem target_initial_read (index : ℕ) (space : PhysicalSpace) :
    Fluid.curl (field index) (sourcePoint index (contactTime index) space) =
      spatialField (target index).initialState space := by
  rw [unified_curl_contact, target_is_original_next]
  rfl

theorem target_contact_read (index : ℕ) (space : PhysicalSpace) :
    Fluid.curl (field index) (sourcePoint index (nextContactTime index) space) =
      spatialField (target index).contact.physicalState space := by
  rw [unified_curl_next, target_is_original_next]

end
end SaturationMonoid.NavierStokes.NativeUnifiedVorticityControl
