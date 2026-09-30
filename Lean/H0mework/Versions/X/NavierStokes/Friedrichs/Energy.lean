import H0mework.Versions.X.NavierStokes.Friedrichs.Action
import H0mework.Physics.DiracEvolution.WeakGalerkinEnergy
import H0mework.Versions.X.NavierStokes.SourceUnheated.Energy

set_option autoImplicit false
open scoped Matrix Matrix.Norms.Elementwise ENNReal ComplexOrder

namespace SaturationMonoid.NavierStokes.NativeCanonicalFriedrichsEnergy

open MeasureTheory Set PhysicsCore DiracCliffordRepresentation DiracExteriorMatterAction
open StageNineHolonomicField StageNineDiracMatterFiberMassRiesz
open StageNineDiracMatterHermitianEnergy StageNineDiracMatterWeakGalerkinEnergy
open StageNineDiracMatterWeakSpatialGalerkinMass StageEightSourceGeneratedMatter
open ThreeDimensionalPeriodicCoarseFilterCore NativePhysicalFourier NativePhysicalTimeAction
open NativeCanonicalFluidCoframe NativeCanonicalFriedrichsPrincipal

noncomputable section

attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

local instance matrixNormed : NormedAddCommGroup DiracMatrix := Matrix.normedAddCommGroup
local instance matrixTopology : TopologicalSpace DiracMatrix :=
  matrixNormed.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

local instance : Fintype MatterCoordinateIndex := Fintype.ofFinite MatterCoordinateIndex
local instance : Nontrivial MatterCoordinateCarrier := by
  refine ⟨⟨0, matterCoordinateEquiv diracSpinTwoMatterProbe, ?_⟩⟩
  intro zero
  apply diracSpinTwoMatterProbe_nonzero
  apply matterCoordinateEquiv.injective
  simpa using zero.symm

/-- One source-independent constant controls every original full material coordinate. -/
theorem normalized_coercivity :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (velocity : PhysicalSpace) (field : MatterCoordinateCarrier),
      κ * ‖field‖ ^ 2 ≤ matterFiberMassPairing (normalized velocity 0) field field := by
  let energy : Unit → MatterCoordinateCarrier → ℝ :=
    fun _ field => matterFiberMassPairing 1 field field
  have continuous : Continuous (fun data : Unit × MatterCoordinateCarrier => energy data.1 data.2) :=
    ((matterFiberMassPairing 1).continuous.comp continuous_snd).clm_apply continuous_snd
  have positive : ∀ point ∈ (univ : Set Unit), ∀ field, field ≠ 0 → 0 < energy point field := by
    intro point _ field nonzero
    apply diracExteriorMatterCoordinateEnergy_pos 1 Matrix.PosDef.one
    exact fun zero => nonzero (matterCoordinateEquiv.symm.injective (by simpa using zero))
  have scale : ∀ point (parameter : ℝ) field,
      energy point (parameter • field) = parameter ^ 2 * energy point field := by
    intro point parameter field
    simp only [energy, map_smul, smul_apply, smul_eq_mul]
    ring
  obtain ⟨κ, κpos, bound⟩ := exists_modeUniformQuadraticCoercivity
    (univ : Set Unit) isCompact_univ (by exact ⟨(), mem_univ ()⟩) energy continuous positive scale
  refine ⟨κ, κpos, fun velocity field => ?_⟩
  rw [normalized_mass_pairing]
  exact bound () (mem_univ ()) field

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem density_integrable (velocity : PhysicalField) :
    Integrable (fun point => density (velocity point)) (volume : Measure Torus) := by
  have paid := NativePhysicalMaterial.temporalCurrent_integrable velocity
  change Integrable (fun point => NativePhysicalMaterial.current velocity 0 point) volume at paid
  simpa only [NativePhysicalMaterial.temporalCurrent_eq, density] using paid

/-- The original kinetic account pays the normalized spatial coefficient on the whole torus. -/
theorem spatial_integrable (velocity : PhysicalField) (direction : Fin 3) :
    Integrable (fun point => normalized (velocity point) direction.succ) (volume : Measure Torus) := by
  refine ((density_integrable velocity).smul_const
    (diracFrameEvolutionPrincipal direction.succ)).congr (ae_of_all _ fun point => ?_)
  dsimp only
  rw [normalized_spatial]
  rfl

theorem spatial_norm_integral (velocity : PhysicalField) (direction : Fin 3) :
    (∫ point : Torus, ‖normalized (velocity point) direction.succ‖) =
      (2 + ‖velocity‖ ^ 2 / 8) * ‖diracFrameEvolutionPrincipal direction.succ‖ := by
  simp only [normalized_spatial, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (density_pos _)]
  rw [integral_mul_const, density_integral]

/-- Every ordinary first coefficient derivative is paid in L¹ by the same two physical L² legs. -/
theorem spatial_derivative_integrable (velocity tangent : PhysicalField) (direction : Fin 3) :
    Integrable (fun point : Torus =>
      (inner ℝ (velocity point) (tangent point) / 4) •
        diracFrameEvolutionPrincipal direction.succ) volume := by
  exact (((memLp_one_iff_integrable.mp
    ((innerSL ℝ).memLp_of_bilin 1 (Lp.memLp velocity) (Lp.memLp tangent))).div_const 4).smul_const _)

open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition
open NativeEndpointVelocityCarrier NativeViewEnergyContent NativeViewEnergyWork

variable {nu : Viscosity}

def sourceVelocity (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : PhysicalField :=
  realField (wholeVelocity (NativeForwardWindowSource.source seed time).fst)

theorem source_spatial_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (direction : Fin 3) :
    (∫ point : Torus, ‖normalized (sourceVelocity seed time point) direction.succ‖) ≤
      (2 + ‖NativeWordStressEnergy.kineticRead‖ * NativeUnifiedCompleteSource.budget seed / 8) *
        ‖diracFrameEvolutionPrincipal direction.succ‖ := by
  rw [spatial_norm_integral]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have paid := physical_energy_bound seed 0 time
  rw [NativeZeroHeatWindow.source_zero] at paid
  change ‖sourceVelocity seed time‖ ^ 2 / 2 ≤ _ at paid
  linarith

/-- The original complete R-work and viscosity drive this normalized-mass account. -/
theorem source_density_write (seed : GeneratedWholeRestartCurrent nu) (first last : ℝ)
    (first_valid : -1 < first) (last_valid : -1 < last) :
    (∫ point : Torus, density (sourceVelocity seed last point)) -
      (∫ point : Torus, density (sourceVelocity seed first point)) =
        (1 / 4 : ℝ) * ∫ time in first..last,
          residualWork seed 0 time - nu.coeff * dissipation seed 0 time := by
  rw [density_integral, density_integral]
  have paid := NativeUnheatedEnergy.physical_integral seed first last first_valid last_valid
  change ‖sourceVelocity seed last‖ ^ 2 / 2 - ‖sourceVelocity seed first‖ ^ 2 / 2 = _ at paid
  linarith

/-- The complete paired density retains the original unresolved covariance. -/
theorem complete_density_split (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    2 + total seed 0 time / 4 = (∫ point : Torus, density (sourceVelocity seed time point)) +
      unresolved seed 0 time / 4 := by
  rw [density_integral, split, NativeUnheatedEnergy.resolved_original]
  dsimp only [sourceVelocity]
  ring

theorem complete_current_zero (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    (NativePairedCurrentFourier.coefficient
      (wholeVelocity (NativeForwardWindowSource.source seed time).fst)
      (NativeCompleteStressCarrier.read (NativeForwardWindowSource.source seed time).snd) 0 0).re =
        (∫ point : Torus, density (sourceVelocity seed time point)) + unresolved seed 0 time / 4 := by
  rw [← complete_density_split]
  have baseline : NativePairedCurrentFourier.baseline 0 = 2 := by
    simp [NativePairedCurrentFourier.baseline, UnitAddTorus.mFourierCoeff,
      UnitAddTorus.mFourier]
  simp only [NativePairedCurrentFourier.coefficient, Fin.cases_zero,
    baseline, NativePairedCurrentFourier.trace,
    Complex.sub_re, Complex.div_ofNat_re, Complex.re_ofNat, Complex.re_sum,
    total, NativeZeroHeatWindow.source_zero, NativeWordStressEnergy.kineticRead_apply]
  ring

theorem sourceVelocity_next (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    sourceVelocity seed (response.2.clockAdvance + time) = sourceVelocity response.1 time := by
  rw [sourceVelocity, NativeForwardWindowSource.source_next seed response generated time nonnegative]
  rfl

end
end SaturationMonoid.NavierStokes.NativeCanonicalFriedrichsEnergy
