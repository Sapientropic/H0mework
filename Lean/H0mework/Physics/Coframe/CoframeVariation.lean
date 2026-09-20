import H0mework.Physics.Geometry.CompactSupportIntegrationByParts

/-!
# S9-C3e0: actual coframe variation and its nondegenerate branch corridor

This module opens the coframe equation at the primitive holonomic field, rather
than accepting a metric, stress tensor, coframe equation, or differentiability
certificate.  A compactly supported smooth coframe direction is inserted into
the actual configuration and its generated continuum point field is proved to
change only through the coframe slot.

The determinant and adjugate are proved smooth from their finite polynomial
formulas.  Consequently matrix inversion and the absolute-determinant volume
are smooth at every nondegenerate coframe.  Compact support then upgrades the
pointwise open condition to one parameter neighbourhood which works at every
base point: the varied coframe stays nondegenerate and in the same orientation
branch as the background.

This is deliberately a branch-corridor checkpoint.  It does not define a
stress covector by bare `fderiv`; the actual sectorwise local derivative and
integrated coframe equation remain the next producer gate.
-/

namespace SaturationMonoid.PhysicsCore.StageNineCoframeVariation

open ProofFreeRicherAnholonomicSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineCompactSupportIntegrationByParts
open MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option maxHeartbeats 600000

def varyCoframe
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → LorentzianCoframe) (parameter : ℝ) :
    StageNineHolonomicConfiguration :=
  { configuration with
    coframe := fun point =>
      configuration.coframe point + parameter • variation point }

@[simp] theorem varyCoframe_zero
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → LorentzianCoframe) :
    varyCoframe configuration variation 0 = configuration := by
  cases configuration
  simp [varyCoframe]

def withCoframe
    (field : StageNineContinuumPointField)
    (coframe : LorentzianCoframe) : StageNineContinuumPointField :=
  { field with coframe := coframe }

theorem toContinuumPointField_varyCoframe
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → LorentzianCoframe) (parameter : ℝ)
    (point : BasePoint) :
    toContinuumPointField (varyCoframe configuration variation parameter) point =
      withCoframe (toContinuumPointField configuration point)
        (configuration.coframe point + parameter • variation point) := by
  apply StageNineContinuumPointField.ext <;> rfl

theorem coframe_det_contDiff :
    ContDiff ℝ ∞ (fun coframe : LorentzianCoframe => Matrix.det coframe) := by
  rw [show (fun coframe : LorentzianCoframe => Matrix.det coframe) =
      fun coframe => ∑ σ : Equiv.Perm LorentzianIndex,
        ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∏ index : LorentzianIndex, coframe (σ index) index by
    funext coframe
    exact Matrix.det_apply' _]
  apply ContDiff.sum
  intro permutation _
  apply contDiff_const.mul
  apply contDiff_prod
  intro index _
  fun_prop

theorem coframe_adjugate_contDiff :
    ContDiff ℝ ∞ (fun coframe : LorentzianCoframe => coframe.adjugate) := by
  apply contDiff_pi'
  intro row
  apply contDiff_pi'
  intro column
  rw [show (fun coframe : LorentzianCoframe =>
      coframe.adjugate row column) =
      fun coframe => Matrix.det
        (coframe.updateRow column (Pi.single row 1)) by
    funext coframe
    exact Matrix.adjugate_apply _ _ _]
  rw [show (fun coframe : LorentzianCoframe => Matrix.det
      (coframe.updateRow column (Pi.single row 1))) =
      fun coframe => ∑ σ : Equiv.Perm LorentzianIndex,
        ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∏ index : LorentzianIndex,
            coframe.updateRow column
              (Pi.single row 1) (σ index) index by
    funext coframe
    exact Matrix.det_apply' _]
  apply ContDiff.sum
  intro permutation _
  apply contDiff_const.mul
  apply contDiff_prod
  intro index _
  by_cases updated : permutation index = column
  · rw [show (fun coframe : LorentzianCoframe =>
        coframe.updateRow column
          (Pi.single row (1 : ℝ)) (permutation index) index) =
      fun _ : LorentzianCoframe => if index = row then (1 : ℝ) else 0 by
        funext coframe
        simp [Matrix.updateRow_apply, updated, Pi.single_apply]]
    exact contDiff_const
  · simpa [Matrix.updateRow_apply, updated] using
      (contDiff_pi.mp
        (contDiff_pi.mp
          (contDiff_id : ContDiff ℝ ∞
            (fun coframe : LorentzianCoframe => coframe))
          (permutation index)) index)

theorem coframe_inv_contDiffAt
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0) :
    ContDiffAt ℝ ∞ (fun candidate : LorentzianCoframe => candidate⁻¹)
      coframe := by
  rw [show (fun candidate : LorentzianCoframe => candidate⁻¹) =
      fun candidate =>
        (Matrix.det candidate)⁻¹ • candidate.adjugate by
    funext candidate
    rw [Matrix.inv_def, Ring.inverse_eq_inv]]
  exact (coframe_det_contDiff.contDiffAt.inv nondegenerate).smul
    coframe_adjugate_contDiff.contDiffAt

theorem coframe_volume_contDiffAt
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0) :
    ContDiffAt ℝ ∞
      (fun candidate : LorentzianCoframe => abs (Matrix.det candidate))
      coframe :=
  coframe_det_contDiff.contDiffAt.abs nondegenerate

theorem holonomicCoframe_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    Continuous configuration.coframe := by
  apply continuous_pi
  intro row
  apply continuous_pi
  intro column
  exact (smooth.1 row column).continuous

set_option maxHeartbeats 1200000 in
theorem compactCoframeVariation_eventually_nondegenerate
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation LorentzianCoframe) :
    ∀ᶠ parameter in nhds (0 : ℝ),
      (varyCoframe configuration variation parameter).Nondegenerate := by
  have coframeContinuous := holonomicCoframe_continuous configuration smooth
  have variationContinuous : Continuous
      (variation : BasePoint → LorentzianCoframe) :=
    variation.smooth.continuous
  have variedCoframeContinuous : Continuous fun pair : ℝ × BasePoint =>
      configuration.coframe pair.2 + pair.1 • variation pair.2 :=
    (coframeContinuous.comp continuous_snd).add
      (continuous_fst.smul (variationContinuous.comp continuous_snd))
  have determinantContinuous : Continuous fun pair : ℝ × BasePoint =>
      Matrix.det
        (configuration.coframe pair.2 + pair.1 • variation pair.2) :=
    coframe_det_contDiff.continuous.comp variedCoframeContinuous
  have uniformOnSupport : ∀ᶠ parameter in nhds (0 : ℝ),
      ∀ point ∈ tsupport (variation : BasePoint → LorentzianCoframe),
        Matrix.det
          (configuration.coframe point + parameter • variation point) ≠ 0 := by
    apply variation.compactSupport.eventually_forall_of_forall_eventually
    intro point _
    have atZero :
        Matrix.det
          (configuration.coframe point + (0 : ℝ) • variation point) ≠ 0 := by
      simpa using nondegenerate point
    have atPair :
        (fun pair : ℝ × BasePoint =>
          Matrix.det
            (configuration.coframe pair.2 + pair.1 • variation pair.2))
            (0, point) ≠ 0 :=
      atZero
    exact (determinantContinuous.continuousAt : ContinuousAt
      (fun pair : ℝ × BasePoint =>
        Matrix.det
          (configuration.coframe pair.2 + pair.1 • variation pair.2))
      (0, point)).eventually_ne atPair
  filter_upwards [uniformOnSupport] with parameter supportNondegenerate
  intro point
  by_cases pointInSupport :
      point ∈ tsupport (variation : BasePoint → LorentzianCoframe)
  · exact supportNondegenerate point pointInSupport
  · have pointNotInSupport :
        point ∉ Function.support
          (variation : BasePoint → LorentzianCoframe) := fun inSupport =>
      pointInSupport (subset_closure inSupport)
    have variationZero : variation point = 0 :=
      not_ne_iff.mp pointNotInSupport
    simpa [varyCoframe, variationZero] using nondegenerate point

set_option maxHeartbeats 1200000 in
theorem compactCoframeVariation_eventually_same_orientation
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation LorentzianCoframe) :
    ∀ᶠ parameter in nhds (0 : ℝ),
      ∀ point : BasePoint,
        0 < Matrix.det
              (configuration.coframe point + parameter • variation point) *
            Matrix.det (configuration.coframe point) := by
  have coframeContinuous := holonomicCoframe_continuous configuration smooth
  have variationContinuous : Continuous
      (variation : BasePoint → LorentzianCoframe) :=
    variation.smooth.continuous
  have variedCoframeContinuous : Continuous fun pair : ℝ × BasePoint =>
      configuration.coframe pair.2 + pair.1 • variation pair.2 :=
    (coframeContinuous.comp continuous_snd).add
      (continuous_fst.smul (variationContinuous.comp continuous_snd))
  have variedDeterminantContinuous : Continuous fun pair : ℝ × BasePoint =>
      Matrix.det
        (configuration.coframe pair.2 + pair.1 • variation pair.2) :=
    coframe_det_contDiff.continuous.comp variedCoframeContinuous
  have backgroundDeterminantContinuous : Continuous fun pair : ℝ × BasePoint =>
      Matrix.det (configuration.coframe pair.2) :=
    (coframe_det_contDiff.continuous.comp coframeContinuous).comp
      continuous_snd
  have orientationProductContinuous : Continuous fun pair : ℝ × BasePoint =>
      Matrix.det
          (configuration.coframe pair.2 + pair.1 • variation pair.2) *
        Matrix.det (configuration.coframe pair.2) :=
    variedDeterminantContinuous.mul backgroundDeterminantContinuous
  have uniformOnSupport : ∀ᶠ parameter in nhds (0 : ℝ),
      ∀ point ∈ tsupport (variation : BasePoint → LorentzianCoframe),
        0 < Matrix.det
              (configuration.coframe point + parameter • variation point) *
            Matrix.det (configuration.coframe point) := by
    apply variation.compactSupport.eventually_forall_of_forall_eventually
    intro point _
    have atZero :
        0 < Matrix.det
              (configuration.coframe point + (0 : ℝ) • variation point) *
            Matrix.det (configuration.coframe point) := by
      simpa using mul_self_pos.mpr (nondegenerate point)
    have atPair :
        0 < (fun pair : ℝ × BasePoint =>
          Matrix.det
              (configuration.coframe pair.2 + pair.1 • variation pair.2) *
            Matrix.det (configuration.coframe pair.2)) (0, point) :=
      atZero
    simpa only [Set.mem_Ioi] using
      (orientationProductContinuous.continuousAt : ContinuousAt
        (fun pair : ℝ × BasePoint =>
          Matrix.det
              (configuration.coframe pair.2 + pair.1 • variation pair.2) *
            Matrix.det (configuration.coframe pair.2))
        (0, point)).eventually (Ioi_mem_nhds atPair)
  filter_upwards [uniformOnSupport] with parameter supportOrientation
  intro point
  by_cases pointInSupport :
      point ∈ tsupport (variation : BasePoint → LorentzianCoframe)
  · exact supportOrientation point pointInSupport
  · have pointNotInSupport :
        point ∉ Function.support
          (variation : BasePoint → LorentzianCoframe) := fun inSupport =>
      pointInSupport (subset_closure inSupport)
    have variationZero : variation point = 0 :=
      not_ne_iff.mp pointNotInSupport
    simpa [variationZero] using mul_self_pos.mpr (nondegenerate point)

end

end SaturationMonoid.PhysicsCore.StageNineCoframeVariation
