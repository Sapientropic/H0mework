import H0mework.NavierStokes.ResolvedAction.ResolvedUnifiedAction

set_option autoImplicit false
open scoped ContDiff Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeUnifiedCorrectionControl

open Set MeasureTheory
open PhysicsCore.ProofFreeRicherAnholonomicSource PhysicsCore.Stage9CU
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw
open NativeWholeHistoryClock NativeWholeHistoryField NativeResolvedSpacetime
open NativeResolvedUnifiedAction NativeWholeHistoryPhysicalAction
open NativeSourceUnifiedActionSplice (target)
open NativeFinitePrefixTimeChart (spatialRead)
open RationalVorticityEvaluator

noncomputable section

def correction (radius : ℕ) (point : BasePoint) : PhysicalSpace :=
  nativeTurbulenceCorrectionField (wholeRestartModes radius) (vorticity (point 0)) (spatialRead point)

theorem clockRate_contDiff : ContDiff ℝ ∞ clockRate := by
  have sigmoid : ContDiff ℝ ∞ Real.sigmoid := contDiff_sigmoid.of_le le_top
  have fraction : ContDiff ℝ ∞ clockFraction := contDiff_const.mul sigmoid
  exact (contDiff_const.mul (sigmoid.mul (contDiff_const.sub sigmoid))).div
    ((contDiff_const.sub fraction).pow 2) (fun parameter =>
      (sq_pos_of_pos (sub_pos.mpr (clockFraction_lt_one parameter))).ne')

theorem correction_contDiff (radius : ℕ) : ContDiff ℝ ∞ (correction radius) := by
  have expression : correction radius = fun point =>
      (clockRate (point 0))⁻¹ • Fluid.coordinateDerivative (resolvedVorticity (wholeRestartModes radius)) 0 point -
        (butterflyGainViscosity.coeff • Fluid.laplacian (resolvedVorticity (wholeRestartModes radius)) point +
          Fluid.curl (Fluid.cross (resolvedVelocity (wholeRestartModes radius)) (resolvedVorticity (wholeRestartModes radius))) point) :=
    funext fun point => (source_native_correction radius point).symm
  rw [expression]
  have clock : ContDiff ℝ ∞ (fun point : BasePoint => (clockRate (point 0))⁻¹) :=
    (clockRate_contDiff.comp (contDiff_piLp_apply 2)).inv (fun point => (clockRate_pos (point 0)).ne')
  have vort := resolvedVorticity_contDiff (wholeRestartModes radius)
  have vel := resolvedVelocity_contDiff (wholeRestartModes radius)
  exact (clock.smul (Fluid.coordinateDerivative_contDiff vort 0)).sub
    (((Fluid.laplacian_contDiff vort).const_smul butterflyGainViscosity.coeff).add
      (Fluid.curl_contDiff (Fluid.cross_contDiff vel vort)))

def physicalCorrection (radius : ℕ) : BasePoint → PhysicalSpace :=
  correction radius ∘ NativeWholeHistoryPhysical.pullback

theorem physical_contDiffAt (radius : ℕ) (point : BasePoint)
    (inside : point ∈ NativeWholeHistoryPhysical.physicalDomain) :
    ContDiffAt ℝ ∞ (physicalCorrection radius) point :=
  (correction_contDiff radius).contDiffAt.comp point (NativeWholeHistoryPhysical.pullback_contDiffAt point inside)

theorem physical_original (radius length : ℕ) (point : BasePoint)
    (inside : point 0 ∈ Ioc (0 : ℝ) (NativeWholeHistoryClock.duration length)) :
    physicalCorrection radius point = nativeTurbulenceCorrectionField (wholeRestartModes radius)
      (NativeReceiptSpacetime.state (receipt length) (point 0)) (spatialRead point) := by
  change nativeTurbulenceCorrectionField _ (vorticity ((sourcePoint (point 0) (spatialRead point)) 0))
    (spatialRead (sourcePoint (point 0) (spatialRead point))) = _
  rw [sourcePoint_time, sourcePoint_space, vorticity_physical_read length (point 0) inside]

theorem source_all_order_Lp (radius order : ℕ) (exponent : ℝ≥0∞)
    {domain : Set BasePoint} (compact : IsCompact domain) (contained : domain ⊆ NativeWholeHistoryPhysical.physicalDomain) :
    ∃ bound : ℝ,
      MemLp (iteratedFDeriv ℝ order (physicalCorrection radius)) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order (physicalCorrection radius)) exponent (volume.restrict domain) ≤
        ENNReal.ofReal bound * volume domain ^ (1 / exponent.toReal) := by
  let : IsFiniteMeasure (volume.restrict domain) := ⟨by simpa using compact.measure_lt_top (μ := volume)⟩
  have continuity : ContinuousOn (iteratedFDeriv ℝ order (physicalCorrection radius)) domain := fun point inside =>
    ((physical_contDiffAt radius point (contained inside)).continuousAt_iteratedFDeriv
      (WithTop.coe_le_coe.mpr le_top)).continuousWithinAt
  obtain ⟨bound, bounded⟩ := compact.exists_bound_of_continuousOn continuity
  have paid : ∀ᵐ point ∂volume.restrict domain, ‖iteratedFDeriv ℝ order (physicalCorrection radius) point‖ ≤ bound := by
    filter_upwards [ae_restrict_mem compact.measurableSet] with point inside
    exact bounded point inside
  exact ⟨bound, MemLp.of_bound (continuity.aestronglyMeasurable compact.measurableSet) bound paid,
    by simpa [mul_comm] using eLpNorm_le_of_ae_bound (p := exponent) paid⟩

theorem target_initial_correction (radius index : ℕ) (space : PhysicalSpace) :
    correction radius (sourcePoint (NativeWholeHistoryClock.duration index) space) =
      nativeTurbulenceCorrectionField (wholeRestartModes radius) (target index).initialState space := by
  rw [correction, sourcePoint_time, sourcePoint_space, target_initial_state]

theorem target_contact_correction (radius index : ℕ) (space : PhysicalSpace) :
    correction radius (sourcePoint (NativeWholeHistoryClock.duration (index + 1)) space) =
      nativeTurbulenceCorrectionField (wholeRestartModes radius) (target index).contact.physicalState space := by
  rw [correction, sourcePoint_time, sourcePoint_space, target_contact_state]

end
end SaturationMonoid.NavierStokes.NativeUnifiedCorrectionControl
