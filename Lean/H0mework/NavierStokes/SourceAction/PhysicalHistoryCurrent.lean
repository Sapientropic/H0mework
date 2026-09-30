import H0mework.NavierStokes.SourceAction.PhysicalHistoryControl

set_option autoImplicit false
open scoped ContDiff ENNReal Topology

namespace SaturationMonoid.NavierStokes.NativePhysicalHistoryCurrent

open Set MeasureTheory
open PhysicsCore ProofFreeRicherAnholonomicSource StageNineHolonomicField
open DiracExteriorMatterAction StageNineFullDiracAdjointMaterial
open Stage9CU.Fluid.CurrentReadout
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open NativePhysicalHistory NativePhysicalHistoryControl NativeFullOrderSynthesis

noncomputable section

def matter (point : BasePoint) : DiracExteriorMatterCarrier := NativeCanonicalFluidCoframe.matter (field point)

def dual (point : BasePoint) : Module.Dual ℂ DiracExteriorMatterCarrier := NativeCanonicalFluidCoframe.dual (field point)

theorem canonical_pairing (point : BasePoint) : FullDiracAdjointPaired (matter point) (dual point) :=
  NativeCanonicalFluidCoframe.canonical_paired _

theorem spatial_read (direction : Fin 3) : current matter dual direction.succ = fun point => field point direction := by
  funext point
  exact Stage9CU.Fluid.InitialLift.spatialCurrent_eq _ direction

theorem temporal_read : current matter dual 0 = fun point => 2 + ‖field point‖ ^ 2 / 8 := by
  funext point
  rw [current, dual, matter, NativeCanonicalFluidCoframe.dual, NativeCanonicalFluidCoframe.matter,
    Stage9CU.Fluid.InitialLift.temporalCurrent_eq, EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]

theorem current_contDiffOn (direction : Fin 4) : ContDiffOn ℝ ∞ (current matter dual direction) domain := by
  refine Fin.cases ?_ (fun spatial => ?_) direction
  · rw [temporal_read]
    exact contDiffOn_const.add ((field_contDiffOn.norm_sq (𝕜 := ℝ)).div_const 8)
  · rw [spatial_read]
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) spatial).contDiff.comp_contDiffOn field_contDiffOn

theorem source_current_all_order_Lp (order : ℕ) (exponent : ℝ≥0∞)
    {compactDomain : Set BasePoint} (compact : IsCompact compactDomain) (contained : compactDomain ⊆ domain) :
    ∃ bound : ℝ, ∀ direction : Fin 4,
      MemLp (iteratedFDerivWithin ℝ order (current matter dual direction) domain) exponent (volume.restrict compactDomain) ∧
      eLpNorm (iteratedFDerivWithin ℝ order (current matter dual direction) domain) exponent (volume.restrict compactDomain) ≤
        ENNReal.ofReal bound * volume compactDomain ^ (1 / exponent.toReal) := by
  let : IsFiniteMeasure (volume.restrict compactDomain) := ⟨by simpa using compact.measure_lt_top (μ := volume)⟩
  let jets (point : BasePoint) : Fin 4 → ContinuousMultilinearMap ℝ (fun _ : Fin order => BasePoint) ℝ :=
    fun direction => iteratedFDerivWithin ℝ order (current matter dual direction) domain point
  have component (direction : Fin 4) :
      ContinuousOn (iteratedFDerivWithin ℝ order (current matter dual direction) domain) compactDomain :=
    ((current_contDiffOn direction).continuousOn_iteratedFDerivWithin
      (WithTop.coe_le_coe.mpr le_top) domain_uniqueDiffOn).mono contained
  have continuity : ContinuousOn jets compactDomain := continuousOn_pi.mpr component
  obtain ⟨bound, bounded⟩ := compact.exists_bound_of_continuousOn continuity
  refine ⟨bound, fun direction => ?_⟩
  have paid : ∀ᵐ point ∂volume.restrict compactDomain,
      ‖iteratedFDerivWithin ℝ order (current matter dual direction) domain point‖ ≤ bound := by
    filter_upwards [ae_restrict_mem compact.measurableSet] with point inside
    exact (norm_le_pi_norm (jets point) direction).trans (bounded point inside)
  exact ⟨MemLp.of_bound ((component direction).aestronglyMeasurable compact.measurableSet) bound paid,
    by simpa [mul_comm] using eLpNorm_le_of_ae_bound (p := exponent) paid⟩

theorem source_initial_current (space : PhysicalSpace) (direction : Fin 3) :
    current matter dual direction.succ (NativeFluidSpatialOperators.slice 0 space) =
      spatialField (wholeBiotSavartVelocityState
        RationalVorticityEvaluator.ButterflyStackedSourceCurrent.stackedShortCurrent.initialState) space direction := by
  rw [spatial_read]
  exact congrArg (fun value : PhysicalSpace => value direction) (field_initial space)

end
end SaturationMonoid.NavierStokes.NativePhysicalHistoryCurrent
