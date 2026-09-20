import H0mework.Physics.Exterior.NonseparableMasterActionVariations

/-!
# Source-generated nonzero gauge stationary configuration

The proof-free source already generates a genuine non-Abelian Lorentz
curvature.  This module projects one internal block to a finite gauge
two-form `Fₛ`, generates `Bₛ = Kₛ⁻¹ Fₛ` from the exact source tetrad, and
proves that `(Fₛ,Bₛ,0)` is stationary for every live gauge coordinate of the
source-relative Stage-5 action.

For `positiveSource`, the projected curvature has component `1/4`, so the
result is not the old zero-gauge stationary family.  The total tetrad
variation also vanishes at the background, while the separate stress probe
in `NonseparableGravityGaugeSourceAction` proves that gauge stress is not
identically zero away from that background.

Boundary: this is a finite background solution generated from a Lorentz
curvature block.  It is not yet a solution of a continuum Yang--Mills
connection equation and must not be cited as mother-group gauge unification.
-/

namespace SaturationMonoid.PhysicsCore.NonzeroSourceGaugeStationaryConfiguration

open ProofFreeRicherAnholonomicSource
open PhysicalIIPlusFrechetVariation
open JetLocalPhysicalPlebanskiAction
open SourceGeneratedPhysicalPlebanskiConfiguration
open SourceRelativePhysicalStationaryFamily
open EmpiricalReferenceScaleCouplingBoundary
open UnifiedPhysicalMasterAction
open NonseparableGravityGaugeSourceAction
open NonseparableMasterActionVariations

noncomputable section

theorem positiveSource_sourceGaugeCurvature_component :
    sourceGaugeCurvature positiveSource 0 = (1 / 4 : ℝ) := by
  change sourceCurvatureVector positiveSource (0, 0) = (1 / 4 : ℝ)
  rw [← sourceActionConfiguration_curvature_generated]
  exact positiveSource_action_curvature_nonzero_component

theorem positiveSource_sourceGaugeCurvature_ne_zero :
    sourceGaugeCurvature positiveSource ≠ 0 := by
  intro hzero
  have hcomponent := congrArg
    (fun curvature : DynamicGaugeVector => curvature 0) hzero
  rw [positiveSource_sourceGaugeCurvature_component] at hcomponent
  norm_num at hcomponent

theorem sourceGaugeSector_action_withCurvature_eq_zero
    (source : Source) (couplingSquared : ℝˣ)
    (curvature : DynamicGaugeVector) :
    dynamicGaugeSectorAction source (tetradVectorAtOrigin source)
      couplingSquared
      (withGaugeCurvature
        (sourceGaugeSectorConfiguration source couplingSquared) curvature) =
      0 := by
  simp [dynamicGaugeSectorAction, withGaugeCurvature,
    sourceRelativeGaugeAuxiliary, sourceGaugeSectorConfiguration]

theorem sourceGaugeSector_action_withMultiplier_eq_zero
    (source : Source) (couplingSquared : ℝˣ)
    (multiplier : DynamicGaugeVector) :
    dynamicGaugeSectorAction source (tetradVectorAtOrigin source)
      couplingSquared
      ((sourceGaugeSectorConfiguration source couplingSquared)
        |>.withConstitutiveMultiplier multiplier) = 0 := by
  simp [dynamicGaugeSectorAction, dynamicGaugeConstitutiveDefect,
    sourceRelativeGaugeCurvature, sourceRelativeGaugeAuxiliary,
    GaugeSectorConfiguration.withConstitutiveMultiplier,
    sourceGaugeSectorConfiguration, sourceGaugeAuxiliary]

theorem sourceGaugeSector_action_withTetrad_eq_zero
    (source : Source) (couplingSquared : ℝˣ) (tetrad : TetradVector) :
    dynamicGaugeSectorAction source tetrad couplingSquared
      (sourceGaugeSectorConfiguration source couplingSquared) = 0 := by
  simp [dynamicGaugeSectorAction, sourceGaugeSectorConfiguration,
    sourceRelativeGaugeCurvature, sourceRelativeGaugeAuxiliary]

theorem sourceGaugeSector_action_withAuxiliary_eq_penalty
    (source : Source) (couplingSquared : ℝˣ)
    (auxiliary : DynamicGaugeVector) :
    dynamicGaugeSectorAction source (tetradVectorAtOrigin source)
        couplingSquared
        (withGaugeAuxiliary
          (sourceGaugeSectorConfiguration source couplingSquared) auxiliary) =
      ((couplingSquared : ℝ) / 2) *
        gaugePairing
          (auxiliary - sourceGaugeAuxiliary source couplingSquared)
          (auxiliary - sourceGaugeAuxiliary source couplingSquared) := by
  simp [dynamicGaugeSectorAction, withGaugeAuxiliary,
    sourceRelativeGaugeCurvature, sourceRelativeGaugeAuxiliary,
    sourceGaugeSectorConfiguration]

theorem gaugePairing_self_hasFDerivAt_zero :
    HasFDerivAt
      (fun value : DynamicGaugeVector => gaugePairing value value)
      (0 : GaugeCovector) 0 := by
  have hcoordinate (index : Fin 6) :
      HasFDerivAt
        (fun value : DynamicGaugeVector => value index * value index)
        (0 : GaugeCovector) 0 := by
    have hprojection :=
      (ContinuousLinearMap.proj index : GaugeCovector).hasFDerivAt
        (x := (0 : DynamicGaugeVector))
    have hproduct :
        HasFDerivAt
          (⇑(ContinuousLinearMap.proj index : GaugeCovector) *
            ⇑(ContinuousLinearMap.proj index : GaugeCovector))
          (0 : GaugeCovector) 0 :=
      (hprojection.mul hprojection).congr_fderiv (by simp)
    apply hproduct.congr_of_eventuallyEq
    filter_upwards [] with value
    rfl
  have hsum := HasFDerivAt.fun_sum
    (u := Finset.univ) (fun index _ => hcoordinate index)
  simpa only [gaugePairing, Finset.mem_univ, Finset.sum_const_zero]
    using hsum

theorem sourceGaugeSector_deltaCurvature_zero
    (source : Source) (couplingSquared : ℝˣ) :
    dynamicGaugeDeltaCurvature source (tetradVectorAtOrigin source)
      couplingSquared (sourceGaugeSectorConfiguration source couplingSquared) =
      0 := by
  have hzero :
      HasFDerivAt
        (fun curvature : DynamicGaugeVector =>
          dynamicGaugeSectorAction source (tetradVectorAtOrigin source)
            couplingSquared
            (withGaugeCurvature
              (sourceGaugeSectorConfiguration source couplingSquared)
              curvature))
        (0 : GaugeCovector)
        (sourceGaugeSectorConfiguration source couplingSquared).curvature :=
    (hasFDerivAt_const
      (𝕜 := ℝ)
      (x := (sourceGaugeSectorConfiguration source couplingSquared).curvature)
      (c := (0 : ℝ))).congr_of_eventuallyEq
        (Filter.Eventually.of_forall
          (sourceGaugeSector_action_withCurvature_eq_zero
            source couplingSquared))
  exact (actual_dynamicGauge_curvature_derivative source
    (tetradVectorAtOrigin source) couplingSquared
      (sourceGaugeSectorConfiguration source couplingSquared)).unique hzero

theorem sourceGaugeSector_deltaAuxiliary_zero
    (source : Source) (couplingSquared : ℝˣ) :
    dynamicGaugeDeltaAuxiliary source (tetradVectorAtOrigin source)
      couplingSquared (sourceGaugeSectorConfiguration source couplingSquared) =
      0 := by
  let background := sourceGaugeAuxiliary source couplingSquared
  have hshift :
      HasFDerivAt
        (fun auxiliary : DynamicGaugeVector => auxiliary - background)
        (ContinuousLinearMap.id ℝ DynamicGaugeVector) background :=
    (hasFDerivAt_id (𝕜 := ℝ) (x := background)).sub_const background
  have hpairing :
      HasFDerivAt
        (fun auxiliary : DynamicGaugeVector =>
          gaugePairing (auxiliary - background) (auxiliary - background))
        (0 : GaugeCovector) background := by
    have houter :
        HasFDerivAt
          (fun value : DynamicGaugeVector => gaugePairing value value)
          (0 : GaugeCovector) (background - background) := by
      simpa only [sub_self] using gaugePairing_self_hasFDerivAt_zero
    simpa only [Function.comp_def, ContinuousLinearMap.zero_comp] using
      houter.comp
        (f := fun auxiliary : DynamicGaugeVector => auxiliary - background)
        background hshift
  have hpenalty :
      HasFDerivAt
        (fun auxiliary : DynamicGaugeVector =>
          ((couplingSquared : ℝ) / 2) *
            gaugePairing (auxiliary - background) (auxiliary - background))
        (0 : GaugeCovector) background := by
    simpa only [smul_zero] using
      hpairing.const_mul ((couplingSquared : ℝ) / 2)
  have haction :
      HasFDerivAt
        (fun auxiliary : DynamicGaugeVector =>
          dynamicGaugeSectorAction source (tetradVectorAtOrigin source)
            couplingSquared
            (withGaugeAuxiliary
              (sourceGaugeSectorConfiguration source couplingSquared)
              auxiliary))
        (0 : GaugeCovector)
        (sourceGaugeSectorConfiguration source couplingSquared).auxiliary := by
    apply hpenalty.congr_of_eventuallyEq
    filter_upwards [] with auxiliary
    simpa only [background, sourceGaugeSectorConfiguration] using
      sourceGaugeSector_action_withAuxiliary_eq_penalty
        source couplingSquared auxiliary
  exact (actual_dynamicGauge_auxiliary_derivative source
    (tetradVectorAtOrigin source) couplingSquared
      (sourceGaugeSectorConfiguration source couplingSquared)).unique haction

theorem sourceGaugeSector_deltaMultiplier_zero
    (source : Source) (couplingSquared : ℝˣ) :
    dynamicGaugeDeltaMultiplier source (tetradVectorAtOrigin source)
      couplingSquared (sourceGaugeSectorConfiguration source couplingSquared) =
      0 := by
  have hzero :
      HasFDerivAt
        (fun multiplier : DynamicGaugeVector =>
          dynamicGaugeSectorAction source (tetradVectorAtOrigin source)
            couplingSquared
            ((sourceGaugeSectorConfiguration source couplingSquared)
              |>.withConstitutiveMultiplier multiplier))
        (0 : GaugeCovector)
        (sourceGaugeSectorConfiguration source couplingSquared).constitutiveMultiplier :=
    (hasFDerivAt_const
      (𝕜 := ℝ)
      (x := (sourceGaugeSectorConfiguration source couplingSquared).constitutiveMultiplier)
      (c := (0 : ℝ))).congr_of_eventuallyEq
        (Filter.Eventually.of_forall
          (sourceGaugeSector_action_withMultiplier_eq_zero
            source couplingSquared))
  exact (actual_dynamicGauge_multiplier_derivative source
    (tetradVectorAtOrigin source) couplingSquared
      (sourceGaugeSectorConfiguration source couplingSquared)).unique hzero

theorem sourceGaugeSector_stress_zero
    (source : Source) (couplingSquared : ℝˣ) :
    dynamicGaugeStressCovector source (tetradVectorAtOrigin source)
      couplingSquared (sourceGaugeSectorConfiguration source couplingSquared) =
      0 := by
  have hzero :
      HasFDerivAt
        (fun tetrad : TetradVector =>
          dynamicGaugeSectorAction source tetrad couplingSquared
            (sourceGaugeSectorConfiguration source couplingSquared))
        (0 : TetradVector →L[ℝ] ℝ) (tetradVectorAtOrigin source) :=
    (hasFDerivAt_const
      (𝕜 := ℝ)
      (x := tetradVectorAtOrigin source)
      (c := (0 : ℝ))).congr_of_eventuallyEq
        (Filter.Eventually.of_forall
          (sourceGaugeSector_action_withTetrad_eq_zero
            source couplingSquared))
  exact (actual_dynamicGauge_tetrad_derivative source
    (tetradVectorAtOrigin source) couplingSquared
      (sourceGaugeSectorConfiguration source couplingSquared)).unique hzero

theorem sourceGaugeSector_all_variations_zero
    (source : Source) (couplingSquared : ℝˣ) :
    dynamicGaugeDeltaCurvature source (tetradVectorAtOrigin source)
          couplingSquared
          (sourceGaugeSectorConfiguration source couplingSquared) = 0 ∧
      dynamicGaugeDeltaAuxiliary source (tetradVectorAtOrigin source)
          couplingSquared
          (sourceGaugeSectorConfiguration source couplingSquared) = 0 ∧
      dynamicGaugeDeltaMultiplier source (tetradVectorAtOrigin source)
          couplingSquared
          (sourceGaugeSectorConfiguration source couplingSquared) = 0 ∧
      dynamicGaugeStressCovector source (tetradVectorAtOrigin source)
          couplingSquared
          (sourceGaugeSectorConfiguration source couplingSquared) = 0 :=
  ⟨sourceGaugeSector_deltaCurvature_zero source couplingSquared,
    sourceGaugeSector_deltaAuxiliary_zero source couplingSquared,
    sourceGaugeSector_deltaMultiplier_zero source couplingSquared,
    sourceGaugeSector_stress_zero source couplingSquared⟩

def sourceStandardModelGaugeConfiguration
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings) :
    StandardModelGaugeConfiguration where
  strong := sourceGaugeSectorConfiguration source
    boundary.strongCouplingSquared
  weak := sourceGaugeSectorConfiguration source
    boundary.weakCouplingSquared
  hypercharge := sourceGaugeSectorConfiguration source
    boundary.hyperchargeCouplingSquared

/-- One configuration whose gravity and all three gauge backgrounds are
generated from the same proof-free source and exact source tetrad. -/
def sourceNonseparableConfiguration
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings) :
    UnifiedConfiguration where
  gravity := sourceStationaryConfiguration source
  gauge := sourceStandardModelGaugeConfiguration source boundary

@[simp] theorem sourceStationaryConfiguration_tetrad_eq
    (source : Source) :
    (sourceStationaryConfiguration source).tetrad =
      tetradVectorAtOrigin source := by
  rfl

@[simp] theorem sourceNonseparableConfiguration_tetrad
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings) :
    (sourceNonseparableConfiguration source boundary).gravity.tetrad =
      tetradVectorAtOrigin source := by
  rfl

theorem sourceNonseparable_selectedGauge_constitutiveDefect_zero
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (block : GaugeBlock) :
    dynamicGaugeConstitutiveDefect source (tetradVectorAtOrigin source)
      (selectedGaugeCoupling boundary block)
      (selectedGaugeConfiguration
        (sourceNonseparableConfiguration source boundary).gauge block) = 0 := by
  cases block <;>
    simp [sourceNonseparableConfiguration,
      sourceStandardModelGaugeConfiguration, selectedGaugeCoupling,
      selectedGaugeConfiguration]

theorem sourceNonseparable_selectedGauge_deltaCurvature_zero
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (block : GaugeBlock) :
    dynamicGaugeDeltaCurvature source (tetradVectorAtOrigin source)
      (selectedGaugeCoupling boundary block)
      (selectedGaugeConfiguration
        (sourceNonseparableConfiguration source boundary).gauge block) = 0 := by
  cases block <;>
    simp [sourceNonseparableConfiguration,
      sourceStandardModelGaugeConfiguration, selectedGaugeCoupling,
      selectedGaugeConfiguration, sourceGaugeSector_deltaCurvature_zero]

theorem sourceNonseparable_selectedGauge_deltaAuxiliary_zero
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (block : GaugeBlock) :
    dynamicGaugeDeltaAuxiliary source (tetradVectorAtOrigin source)
      (selectedGaugeCoupling boundary block)
      (selectedGaugeConfiguration
        (sourceNonseparableConfiguration source boundary).gauge block) = 0 := by
  cases block <;>
    simp [sourceNonseparableConfiguration,
      sourceStandardModelGaugeConfiguration, selectedGaugeCoupling,
      selectedGaugeConfiguration, sourceGaugeSector_deltaAuxiliary_zero]

theorem sourceNonseparable_selectedGauge_deltaMultiplier_zero
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (block : GaugeBlock) :
    dynamicGaugeDeltaMultiplier source (tetradVectorAtOrigin source)
      (selectedGaugeCoupling boundary block)
      (selectedGaugeConfiguration
        (sourceNonseparableConfiguration source boundary).gauge block) = 0 := by
  cases block <;>
    simp [sourceNonseparableConfiguration,
      sourceStandardModelGaugeConfiguration, selectedGaugeCoupling,
      selectedGaugeConfiguration, sourceGaugeSector_deltaMultiplier_zero]

theorem sourceNonseparable_deltaTetrad_zero
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings) :
    nonseparableDeltaTetrad source boundary
      (sourceNonseparableConfiguration source boundary) = 0 := by
  rw [nonseparableDeltaTetrad_eq_gravity_add_gaugeStress]
  simp [sourceNonseparableConfiguration,
    sourceStandardModelGaugeConfiguration, sourceStationary_deltaE,
    sourceStationaryConfiguration_tetrad_eq,
    sourceGaugeSector_stress_zero]

/-- Stationarity predicate for every finite field coordinate currently present
in the Stage-5 master action. -/
structure NonseparablePhysicalStationaryAtSource
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (q : UnifiedConfiguration) : Prop where
  gravity_connection_zero : deltaOmega source q.gravity = 0
  gravity_bivector_zero : deltaB source q.gravity = 0
  gravity_multiplier_zero : deltaPhi source q.gravity = 0
  total_tetrad_zero : nonseparableDeltaTetrad source boundary q = 0
  gauge_curvature_zero : ∀ block : GaugeBlock,
    dynamicGaugeDeltaCurvature source q.gravity.tetrad
      (selectedGaugeCoupling boundary block)
      (selectedGaugeConfiguration q.gauge block) = 0
  gauge_auxiliary_zero : ∀ block : GaugeBlock,
    dynamicGaugeDeltaAuxiliary source q.gravity.tetrad
      (selectedGaugeCoupling boundary block)
      (selectedGaugeConfiguration q.gauge block) = 0
  gauge_multiplier_zero : ∀ block : GaugeBlock,
    dynamicGaugeDeltaMultiplier source q.gravity.tetrad
      (selectedGaugeCoupling boundary block)
      (selectedGaugeConfiguration q.gauge block) = 0

theorem source_generates_nonseparableStationaryConfiguration
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings) :
    NonseparablePhysicalStationaryAtSource source boundary
      (sourceNonseparableConfiguration source boundary) where
  gravity_connection_zero := by
    simpa [sourceNonseparableConfiguration,
      sourceStationaryConfiguration_tetrad_eq] using
      sourceStationary_deltaOmega source
  gravity_bivector_zero := by
    simpa [sourceNonseparableConfiguration,
      sourceStationaryConfiguration_tetrad_eq] using
      sourceStationary_deltaB source
  gravity_multiplier_zero := by
    simpa [sourceNonseparableConfiguration,
      sourceStationaryConfiguration_tetrad_eq] using
      sourceStationary_deltaPhi source
  total_tetrad_zero := sourceNonseparable_deltaTetrad_zero source boundary
  gauge_curvature_zero := by
    intro block
    simpa [sourceNonseparableConfiguration] using
      sourceNonseparable_selectedGauge_deltaCurvature_zero
        source boundary block
  gauge_auxiliary_zero := by
    intro block
    simpa [sourceNonseparableConfiguration] using
      sourceNonseparable_selectedGauge_deltaAuxiliary_zero
        source boundary block
  gauge_multiplier_zero := by
    intro block
    simpa [sourceNonseparableConfiguration] using
      sourceNonseparable_selectedGauge_deltaMultiplier_zero
        source boundary block

/-- The zero covectors above are the actual Fréchet derivatives of the one
nonseparable master action, not merely named residuals. -/
theorem sourceNonseparable_all_actual_zero_derivatives
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings) :
    let q := sourceNonseparableConfiguration source boundary
    HasFDerivAt
        (fun connection : ConnectionJet =>
          nonseparableMasterAction source boundary
            (q.withGravityConnection connection))
        (0 : ConnectionJet →L[ℝ] ℝ) q.gravity.connection ∧
      HasFDerivAt
        (fun bivector : BivectorVector =>
          nonseparableMasterAction source boundary
            (q.withGravityBivector bivector))
        (0 : BivectorVector →L[ℝ] ℝ) q.gravity.bivector ∧
      HasFDerivAt
        (fun multiplier : BivectorVector =>
          nonseparableMasterAction source boundary
            (q.withGravityMultiplier multiplier))
        (0 : BivectorVector →L[ℝ] ℝ) q.gravity.multiplier ∧
      HasFDerivAt
        (fun tetrad : TetradVector =>
          nonseparableMasterAction source boundary
            (q.withGravityTetrad tetrad))
        (0 : TetradVector →L[ℝ] ℝ) q.gravity.tetrad ∧
      ∀ block : GaugeBlock,
        HasFDerivAt
            (fun curvature : DynamicGaugeVector =>
              nonseparableMasterAction source boundary
                (withSelectedGaugeCurvature q block curvature))
            (0 : GaugeCovector)
              (selectedGaugeConfiguration q.gauge block).curvature ∧
          HasFDerivAt
            (fun auxiliary : DynamicGaugeVector =>
              nonseparableMasterAction source boundary
                (withSelectedGaugeAuxiliary q block auxiliary))
            (0 : GaugeCovector)
              (selectedGaugeConfiguration q.gauge block).auxiliary ∧
          HasFDerivAt
            (fun multiplier : DynamicGaugeVector =>
              nonseparableMasterAction source boundary
                (withSelectedGaugeMultiplier q block multiplier))
            (0 : GaugeCovector)
              (selectedGaugeConfiguration q.gauge block).constitutiveMultiplier := by
  dsimp only
  have hstationary :=
    source_generates_nonseparableStationaryConfiguration source boundary
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (nonseparable_actual_gravity_connection_derivative
      source boundary (sourceNonseparableConfiguration source boundary))
        |>.congr_fderiv hstationary.gravity_connection_zero
  · exact (nonseparable_actual_gravity_bivector_derivative
      source boundary (sourceNonseparableConfiguration source boundary))
        |>.congr_fderiv hstationary.gravity_bivector_zero
  · exact (nonseparable_actual_gravity_multiplier_derivative
      source boundary (sourceNonseparableConfiguration source boundary))
        |>.congr_fderiv hstationary.gravity_multiplier_zero
  · exact (nonseparable_actual_gravity_tetrad_derivative
      source boundary (sourceNonseparableConfiguration source boundary))
        |>.congr_fderiv hstationary.total_tetrad_zero
  · intro block
    exact
      ⟨(nonseparable_actual_selectedGauge_curvature_derivative
          source boundary (sourceNonseparableConfiguration source boundary)
            block).congr_fderiv
            (hstationary.gauge_curvature_zero block),
        (nonseparable_actual_selectedGauge_auxiliary_derivative
          source boundary (sourceNonseparableConfiguration source boundary)
            block).congr_fderiv
            (hstationary.gauge_auxiliary_zero block),
        (nonseparable_actual_selectedGauge_multiplier_derivative
          source boundary (sourceNonseparableConfiguration source boundary)
            block).congr_fderiv
            (hstationary.gauge_multiplier_zero block)⟩

theorem positiveSource_nonseparable_strongCurvature_ne_zero
    (boundary : EmpiricalReferenceScaleCouplings) :
    (sourceNonseparableConfiguration positiveSource boundary).gauge.strong.curvature ≠
      0 := by
  simpa [sourceNonseparableConfiguration,
    sourceStandardModelGaugeConfiguration, sourceGaugeSectorConfiguration]
    using positiveSource_sourceGaugeCurvature_ne_zero

/-- Final nonzero-stationary witness for the finite Stage-5 action. -/
theorem positiveSource_generates_nonzeroGauge_stationaryConfiguration
    (boundary : EmpiricalReferenceScaleCouplings) :
    NonseparablePhysicalStationaryAtSource positiveSource boundary
        (sourceNonseparableConfiguration positiveSource boundary) ∧
      (sourceNonseparableConfiguration positiveSource boundary).gauge.strong.curvature ≠
        0 :=
  ⟨source_generates_nonseparableStationaryConfiguration
      positiveSource boundary,
    positiveSource_nonseparable_strongCurvature_ne_zero boundary⟩

end
end SaturationMonoid.PhysicsCore.NonzeroSourceGaugeStationaryConfiguration
