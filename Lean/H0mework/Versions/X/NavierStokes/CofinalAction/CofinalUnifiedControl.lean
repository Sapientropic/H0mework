import H0mework.Versions.X.NavierStokes.CofinalAction.CofinalUnifiedAction

set_option autoImplicit false
open scoped ContDiff ENNReal

namespace SaturationMonoid.NavierStokes.NativeCofinalUnifiedControl

open Set MeasureTheory
open PhysicsCore.ProofFreeRicherAnholonomicSource PhysicsCore.Stage9CU.Fluid.CurrentReadout
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeCofinalUnifiedField

noncomputable section

variable {nu : Viscosity}

theorem domain_uniqueDiffOn (initial : GeneratedWholeRestartCurrent nu) : UniqueDiffOn ℝ (domain initial) := by
  let horizon := wholeRestartDuration (target initial).contact
  have positive : 0 < horizon := wholeRestartDuration_pos (target initial).contact
  let time : BasePoint →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 4 => ℝ) 0
  have convex : Convex ℝ (domain initial) := (convex_Icc (0 : ℝ) horizon).linear_preimage time.toLinearMap
  apply uniqueDiffOn_convex convex
  let interiorSlab : Set BasePoint := {point | point 0 ∈ Ioo (0 : ℝ) horizon}
  have opened : IsOpen interiorSlab := isOpen_Ioo.preimage time.continuous
  let center : BasePoint := EuclideanSpace.single 0 (horizon / 2)
  have member : center ∈ interiorSlab := by
    change 0 < center 0 ∧ center 0 < horizon
    simp only [center, PiLp.single_apply, ite_true]
    constructor <;> linarith
  have interiorMember : center ∈ interior interiorSlab := by
    rw [opened.interior_eq]
    exact member
  exact ⟨center, interior_mono (show interiorSlab ⊆ domain initial from fun _ inside => ⟨inside.1.le, inside.2.le⟩) interiorMember⟩

private theorem all_order_Lp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (initial : GeneratedWholeRestartCurrent nu) (field : BasePoint → E) (smooth : ContDiffOn ℝ ∞ field (domain initial))
    (order : ℕ) (exponent : ℝ≥0∞) {compactDomain : Set BasePoint}
    (compact : IsCompact compactDomain) (contained : compactDomain ⊆ domain initial) :
    ∃ bound : ℝ,
      MemLp (iteratedFDerivWithin ℝ order field (domain initial)) exponent (volume.restrict compactDomain) ∧
      eLpNorm (iteratedFDerivWithin ℝ order field (domain initial)) exponent (volume.restrict compactDomain) ≤
        ENNReal.ofReal bound * volume compactDomain ^ (1 / exponent.toReal) := by
  let : IsFiniteMeasure (volume.restrict compactDomain) := ⟨by simpa using compact.measure_lt_top (μ := volume)⟩
  have continuity : ContinuousOn (iteratedFDerivWithin ℝ order field (domain initial)) compactDomain :=
    (smooth.continuousOn_iteratedFDerivWithin (WithTop.coe_le_coe.mpr le_top) (domain_uniqueDiffOn initial)).mono contained
  obtain ⟨bound, bounded⟩ := compact.exists_bound_of_continuousOn continuity
  have paid : ∀ᵐ point ∂volume.restrict compactDomain, ‖iteratedFDerivWithin ℝ order field (domain initial) point‖ ≤ bound := by
    filter_upwards [ae_restrict_mem compact.measurableSet] with point inside
    exact bounded point inside
  exact ⟨bound, MemLp.of_bound (continuity.aestronglyMeasurable compact.measurableSet) bound paid,
    by simpa [mul_comm] using eLpNorm_le_of_ae_bound (p := exponent) paid⟩

theorem source_all_order_Lp (initial : GeneratedWholeRestartCurrent nu) (modes : Finset IntegerWavevector)
    (order : ℕ) (exponent : ℝ≥0∞) {compactDomain : Set BasePoint}
    (compact : IsCompact compactDomain) (contained : compactDomain ⊆ domain initial) :
    ∀ observation ∈ ({field initial, vorticityField initial, correctionField initial modes} : Set (BasePoint → PhysicalSpace)),
      ∃ bound : ℝ,
        MemLp (iteratedFDerivWithin ℝ order observation (domain initial)) exponent (volume.restrict compactDomain) ∧
        eLpNorm (iteratedFDerivWithin ℝ order observation (domain initial)) exponent (volume.restrict compactDomain) ≤
          ENNReal.ofReal bound * volume compactDomain ^ (1 / exponent.toReal) := by
  intro observation member
  simp only [mem_insert_iff, mem_singleton_iff] at member
  rcases member with rfl | rfl | rfl
  · exact all_order_Lp initial _ (field_contDiffOn initial) order exponent compact contained
  · exact all_order_Lp initial _ (vorticityField_contDiffOn initial) order exponent compact contained
  · exact all_order_Lp initial _ (correctionField_contDiffOn initial modes) order exponent compact contained

theorem source_current_all_order_Lp (initial : GeneratedWholeRestartCurrent nu) (order : ℕ) (exponent : ℝ≥0∞)
    {compactDomain : Set BasePoint} (compact : IsCompact compactDomain) (contained : compactDomain ⊆ domain initial) :
    ∃ bound : ℝ, ∀ direction : Fin 4,
      MemLp (iteratedFDerivWithin ℝ order (current (matter initial) (dual initial) direction) (domain initial))
        exponent (volume.restrict compactDomain) ∧
      eLpNorm (iteratedFDerivWithin ℝ order (current (matter initial) (dual initial) direction) (domain initial))
        exponent (volume.restrict compactDomain) ≤ ENNReal.ofReal bound * volume compactDomain ^ (1 / exponent.toReal) := by
  let : IsFiniteMeasure (volume.restrict compactDomain) := ⟨by simpa using compact.measure_lt_top (μ := volume)⟩
  let jets (point : BasePoint) : Fin 4 → ContinuousMultilinearMap ℝ (fun _ : Fin order => BasePoint) ℝ :=
    fun direction => iteratedFDerivWithin ℝ order (current (matter initial) (dual initial) direction) (domain initial) point
  have component (direction : Fin 4) : ContinuousOn
      (iteratedFDerivWithin ℝ order (current (matter initial) (dual initial) direction) (domain initial)) compactDomain :=
    ((current_contDiffOn initial direction).continuousOn_iteratedFDerivWithin
      (WithTop.coe_le_coe.mpr le_top) (domain_uniqueDiffOn initial)).mono contained
  have continuity : ContinuousOn jets compactDomain := continuousOn_pi.mpr component
  obtain ⟨bound, bounded⟩ := compact.exists_bound_of_continuousOn continuity
  refine ⟨bound, fun direction => ?_⟩
  have paid : ∀ᵐ point ∂volume.restrict compactDomain,
      ‖iteratedFDerivWithin ℝ order (current (matter initial) (dual initial) direction) (domain initial) point‖ ≤ bound := by
    filter_upwards [ae_restrict_mem compact.measurableSet] with point inside
    exact (norm_le_pi_norm (jets point) direction).trans (bounded point inside)
  exact ⟨MemLp.of_bound ((component direction).aestronglyMeasurable compact.measurableSet) bound paid,
    by simpa [mul_comm] using eLpNorm_le_of_ae_bound (p := exponent) paid⟩

end
end SaturationMonoid.NavierStokes.NativeCofinalUnifiedControl
