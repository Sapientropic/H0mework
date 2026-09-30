import H0mework.Versions.X.NavierStokes.SourceAction.PhysicalHistory

set_option autoImplicit false
open scoped ContDiff Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativePhysicalHistoryControl

open Set MeasureTheory
open PhysicsCore.ProofFreeRicherAnholonomicSource
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open NativePhysicalHistory
open NativeWholeHistoryClock (duration duration_pos)

noncomputable section

theorem slab_uniqueDiffOn (length : ℕ) : UniqueDiffOn ℝ (slab length) := by
  let time : BasePoint →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 4 => ℝ) 0
  have convex : Convex ℝ (slab length) := (convex_Icc (0 : ℝ) (duration length)).linear_preimage time.toLinearMap
  apply uniqueDiffOn_convex convex
  let interiorSlab : Set BasePoint := {point | point 0 ∈ Ioo (0 : ℝ) (duration length)}
  have opened : IsOpen interiorSlab := isOpen_Ioo.preimage time.continuous
  let center : BasePoint := EuclideanSpace.single 0 (duration length / 2)
  have member : center ∈ interiorSlab := by
    change 0 < center 0 ∧ center 0 < duration length
    simp only [center, PiLp.single_apply, ite_true]
    constructor <;> linarith [duration_pos length]
  have interiorMember : center ∈ interior interiorSlab := by
    rw [opened.interior_eq]
    exact member
  exact ⟨center, interior_mono (show interiorSlab ⊆ slab length from fun _ inside => ⟨inside.1.le, inside.2.le⟩) interiorMember⟩

theorem domain_uniqueDiffOn : UniqueDiffOn ℝ domain := by
  intro point inside
  exact (slab_uniqueDiffOn (index (point 0)) point ⟨inside.1, (index_spec point inside).le⟩).mono (slab_subset _)

theorem all_order_Lp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : BasePoint → E) (smooth : ContDiffOn ℝ ∞ field domain)
    (order : ℕ) (exponent : ℝ≥0∞) {compactDomain : Set BasePoint}
    (compact : IsCompact compactDomain) (contained : compactDomain ⊆ domain) :
    ∃ bound : ℝ,
      MemLp (iteratedFDerivWithin ℝ order field domain) exponent (volume.restrict compactDomain) ∧
      eLpNorm (iteratedFDerivWithin ℝ order field domain) exponent (volume.restrict compactDomain) ≤
        ENNReal.ofReal bound * volume compactDomain ^ (1 / exponent.toReal) := by
  let : IsFiniteMeasure (volume.restrict compactDomain) := ⟨by simpa using compact.measure_lt_top (μ := volume)⟩
  have continuity : ContinuousOn (iteratedFDerivWithin ℝ order field domain) compactDomain := (smooth.continuousOn_iteratedFDerivWithin
    (WithTop.coe_le_coe.mpr le_top) domain_uniqueDiffOn).mono contained
  obtain ⟨bound, bounded⟩ := compact.exists_bound_of_continuousOn continuity
  have paid : ∀ᵐ point ∂volume.restrict compactDomain, ‖iteratedFDerivWithin ℝ order field domain point‖ ≤ bound := by
    filter_upwards [ae_restrict_mem compact.measurableSet] with point inside
    exact bounded point inside
  exact ⟨bound, MemLp.of_bound (continuity.aestronglyMeasurable compact.measurableSet) bound paid,
    by simpa [mul_comm] using eLpNorm_le_of_ae_bound (p := exponent) paid⟩

theorem source_all_order_Lp (modes : Finset IntegerWavevector) (order : ℕ) (exponent : ℝ≥0∞)
    {compactDomain : Set BasePoint} (compact : IsCompact compactDomain) (contained : compactDomain ⊆ domain) :
    ∀ observation ∈ ({field, vorticityField, correctionField modes} : Set (BasePoint → PhysicalSpace)),
      ∃ bound : ℝ,
        MemLp (iteratedFDerivWithin ℝ order observation domain) exponent (volume.restrict compactDomain) ∧
        eLpNorm (iteratedFDerivWithin ℝ order observation domain) exponent (volume.restrict compactDomain) ≤
          ENNReal.ofReal bound * volume compactDomain ^ (1 / exponent.toReal) := by
  intro observation member
  simp only [mem_insert_iff, mem_singleton_iff] at member
  rcases member with rfl | rfl | rfl
  · exact all_order_Lp _ field_contDiffOn order exponent compact contained
  · exact all_order_Lp _ vorticityField_contDiffOn order exponent compact contained
  · exact all_order_Lp _ (correctionField_contDiffOn modes) order exponent compact contained

end
end SaturationMonoid.NavierStokes.NativePhysicalHistoryControl
