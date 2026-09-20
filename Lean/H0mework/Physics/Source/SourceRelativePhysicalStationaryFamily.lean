import H0mework.Physics.Source.GeneratedPhysicalPlebanskiConfiguration

/-!
# Source-relative physical stationary family

The jet-local action already supplies four genuine Fréchet variations, but an
independent connection derivative jet prevents a nonzero BF field from being
stationary without the continuum integration-by-parts equation.  This module
therefore states the strongest honest finite result available at this layer:
a source-relative BF--Plebanski density on field differences.

For one proof-free source, let `Bₛ`, `Fₛ`, and `eₛ` be its independently
generated physical bivector, non-Abelian curvature, and tetrad.  The action is

`<B-Bₛ, ⋆(F-Fₛ)> - 1/2 ||B-Bₛ||²
  + <φ, (B-Bₛ) - (P(e)-P(eₛ))>`.

The source configuration is stationary because all three source-relative
defects vanish there.  Neither a stationary point nor a stationarity
certificate is stored in the raw source.  This is a finite background action
density, not a spacetime integral or continuum Einstein/Plebanski recovery.
-/

namespace SaturationMonoid.PhysicsCore.SourceRelativePhysicalStationaryFamily

open ProofFreeRicherAnholonomicSource
open PhysicalIIPlusFrechetVariation
open JetLocalPhysicalPlebanskiAction
open SourceGeneratedPhysicalPlebanskiConfiguration
open scoped RealInnerProductSpace

noncomputable section

def bivectorDefect (source : Source) (bivector : BivectorVector) :
    BivectorVector :=
  bivector - sourceBivectorAtOrigin source

def curvatureDefect (source : Source) (connection : ConnectionJet) :
    BivectorVector :=
  nonAbelianCurvature connection - sourceCurvatureVector source

def physicalBivectorDefect (source : Source) (tetrad : TetradVector) :
    BivectorVector :=
  physicalIIPlusMap tetrad - sourceBivectorAtOrigin source

/-- One source-relative finite BF--Plebanski action density. -/
def sourceRelativeMasterAction (source : Source) (q : Configuration) : ℝ :=
  ⟪bivectorDefect source q.bivector,
      spacetimeHodgeVector (curvatureDefect source q.connection)⟫ -
    (1 / 2 : ℝ) * ‖bivectorDefect source q.bivector‖ ^ 2 +
  ⟪q.multiplier,
      bivectorDefect source q.bivector -
        physicalBivectorDefect source q.tetrad⟫

theorem sourceRelativeMasterAction_connection_contDiff
    (source : Source) (q : Configuration) :
    ContDiff ℝ ⊤
      (fun connection =>
        sourceRelativeMasterAction source (q.withConnection connection)) := by
  have hcurvature :
      ContDiff ℝ ⊤
        (fun connection =>
          spacetimeHodgeVector (curvatureDefect source connection)) :=
    spacetimeHodgeVector_contDiff.comp
      (nonAbelianCurvature_contDiff.sub contDiff_const)
  have hbf :
      ContDiff ℝ ⊤
        (fun connection =>
          ⟪bivectorDefect source q.bivector,
            spacetimeHodgeVector (curvatureDefect source connection)⟫) :=
    contDiff_const.inner ℝ hcurvature
  simpa [sourceRelativeMasterAction, Configuration.withConnection] using
    (hbf.sub contDiff_const).add contDiff_const

theorem sourceRelativeMasterAction_bivector_contDiff
    (source : Source) (q : Configuration) :
    ContDiff ℝ ⊤
      (fun bivector =>
        sourceRelativeMasterAction source (q.withBivector bivector)) := by
  have hdefect :
      ContDiff ℝ ⊤
        (fun bivector : BivectorVector => bivectorDefect source bivector) :=
    contDiff_id.sub contDiff_const
  have hbf :
      ContDiff ℝ ⊤
        (fun bivector : BivectorVector =>
          ⟪bivectorDefect source bivector,
            spacetimeHodgeVector (curvatureDefect source q.connection)⟫) :=
    hdefect.inner ℝ contDiff_const
  have hquadratic :
      ContDiff ℝ ⊤
        (fun bivector : BivectorVector =>
          (1 / 2 : ℝ) * ‖bivectorDefect source bivector‖ ^ 2) :=
    ContDiff.const_smul (R := ℝ) (1 / 2 : ℝ) (hdefect.norm_sq ℝ)
  have hmultiplier :
      ContDiff ℝ ⊤
        (fun bivector : BivectorVector =>
          ⟪q.multiplier,
            bivectorDefect source bivector -
              physicalBivectorDefect source q.tetrad⟫) :=
    contDiff_const.inner ℝ (hdefect.sub contDiff_const)
  simpa [sourceRelativeMasterAction, Configuration.withBivector] using
    (hbf.sub hquadratic).add hmultiplier

theorem sourceRelativeMasterAction_multiplier_contDiff
    (source : Source) (q : Configuration) :
    ContDiff ℝ ⊤
      (fun multiplier =>
        sourceRelativeMasterAction source (q.withMultiplier multiplier)) := by
  have hmultiplier :
      ContDiff ℝ ⊤
        (fun multiplier : BivectorVector =>
          ⟪multiplier,
            bivectorDefect source q.bivector -
              physicalBivectorDefect source q.tetrad⟫) :=
    contDiff_id.inner ℝ contDiff_const
  simpa [sourceRelativeMasterAction, Configuration.withMultiplier] using
    (contDiff_const.sub contDiff_const).add hmultiplier

theorem sourceRelativeMasterAction_tetrad_contDiff
    (source : Source) (q : Configuration) :
    ContDiff ℝ ⊤
      (fun tetrad =>
        sourceRelativeMasterAction source (q.withTetrad tetrad)) := by
  have hphysical :
      ContDiff ℝ ⊤
        (fun tetrad : TetradVector =>
          physicalBivectorDefect source tetrad) :=
    physicalIIPlusMap_contDiff.sub contDiff_const
  have hmultiplier :
      ContDiff ℝ ⊤
        (fun tetrad : TetradVector =>
          ⟪q.multiplier,
            bivectorDefect source q.bivector -
              physicalBivectorDefect source tetrad⟫) :=
    contDiff_const.inner ℝ (contDiff_const.sub hphysical)
  simpa [sourceRelativeMasterAction, Configuration.withTetrad] using
    (contDiff_const.sub contDiff_const).add hmultiplier

def deltaOmega (source : Source) (q : Configuration) :
    ConnectionJet →L[ℝ] ℝ :=
  fderiv ℝ
    (fun connection =>
      sourceRelativeMasterAction source (q.withConnection connection))
    q.connection

def deltaB (source : Source) (q : Configuration) :
    BivectorVector →L[ℝ] ℝ :=
  fderiv ℝ
    (fun bivector =>
      sourceRelativeMasterAction source (q.withBivector bivector))
    q.bivector

def deltaPhi (source : Source) (q : Configuration) :
    BivectorVector →L[ℝ] ℝ :=
  innerSL ℝ
    (bivectorDefect source q.bivector -
      physicalBivectorDefect source q.tetrad)

def deltaE (source : Source) (q : Configuration) :
    TetradVector →L[ℝ] ℝ :=
  fderiv ℝ
    (fun tetrad =>
      sourceRelativeMasterAction source (q.withTetrad tetrad))
    q.tetrad

theorem actual_connection_derivative (source : Source) (q : Configuration) :
    HasFDerivAt
      (fun connection =>
        sourceRelativeMasterAction source (q.withConnection connection))
      (deltaOmega source q) q.connection :=
  ((sourceRelativeMasterAction_connection_contDiff source q).differentiable
      (by simp))
    |>.differentiableAt.hasFDerivAt

theorem actual_bivector_derivative (source : Source) (q : Configuration) :
    HasFDerivAt
      (fun bivector =>
        sourceRelativeMasterAction source (q.withBivector bivector))
      (deltaB source q) q.bivector :=
  ((sourceRelativeMasterAction_bivector_contDiff source q).differentiable
      (by simp))
    |>.differentiableAt.hasFDerivAt

theorem actual_multiplier_derivative (source : Source) (q : Configuration) :
    HasFDerivAt
      (fun multiplier =>
        sourceRelativeMasterAction source (q.withMultiplier multiplier))
      (deltaPhi source q) q.multiplier := by
  have hinner :
      HasFDerivAt
        (fun multiplier : BivectorVector =>
          ⟪multiplier,
            bivectorDefect source q.bivector -
              physicalBivectorDefect source q.tetrad⟫)
        (innerSL ℝ
          (bivectorDefect source q.bivector -
            physicalBivectorDefect source q.tetrad))
        q.multiplier := by
    simpa only [coe_innerSL_apply, real_inner_comm] using
      (innerSL ℝ
        (bivectorDefect source q.bivector -
          physicalBivectorDefect source q.tetrad)).hasFDerivAt
          (x := q.multiplier)
  simpa [sourceRelativeMasterAction, Configuration.withMultiplier, deltaPhi,
    add_assoc] using
      hinner.add_const
        (⟪bivectorDefect source q.bivector,
            spacetimeHodgeVector (curvatureDefect source q.connection)⟫ -
          (1 / 2 : ℝ) * ‖bivectorDefect source q.bivector‖ ^ 2)

theorem actual_tetrad_derivative (source : Source) (q : Configuration) :
    HasFDerivAt
      (fun tetrad =>
        sourceRelativeMasterAction source (q.withTetrad tetrad))
      (deltaE source q) q.tetrad :=
  ((sourceRelativeMasterAction_tetrad_contDiff source q).differentiable
      (by simp))
    |>.differentiableAt.hasFDerivAt

theorem all_four_variations_from_one_sourceRelativeAction
    (source : Source) (q : Configuration) :
    HasFDerivAt
        (fun connection =>
          sourceRelativeMasterAction source (q.withConnection connection))
        (deltaOmega source q) q.connection ∧
      HasFDerivAt
        (fun bivector =>
          sourceRelativeMasterAction source (q.withBivector bivector))
        (deltaB source q) q.bivector ∧
      HasFDerivAt
        (fun multiplier =>
          sourceRelativeMasterAction source (q.withMultiplier multiplier))
        (deltaPhi source q) q.multiplier ∧
      HasFDerivAt
        (fun tetrad =>
          sourceRelativeMasterAction source (q.withTetrad tetrad))
        (deltaE source q) q.tetrad :=
  ⟨actual_connection_derivative source q,
    actual_bivector_derivative source q,
    actual_multiplier_derivative source q,
    actual_tetrad_derivative source q⟩

theorem deltaPhi_eq_zero_iff_relative_simplicity
    (source : Source) (q : Configuration) :
    deltaPhi source q = 0 ↔
      bivectorDefect source q.bivector =
        physicalBivectorDefect source q.tetrad := by
  constructor
  · intro hzero
    have hdefect :
        bivectorDefect source q.bivector -
            physicalBivectorDefect source q.tetrad = 0 := by
      exact (innerSL_inj (𝕜 := ℝ) (E := BivectorVector)).mp (by
        simpa [deltaPhi] using hzero)
    exact sub_eq_zero.mp hdefect
  · intro hequal
    simp [deltaPhi, hequal]

abbrev sourceStationaryConfiguration (source : Source) : Configuration :=
  sourceActionConfiguration source

@[simp] theorem bivectorDefect_sourceBivector (source : Source) :
    bivectorDefect source (sourceBivectorAtOrigin source) = 0 := by
  simp [bivectorDefect]

@[simp] theorem curvatureDefect_sourceConnection (source : Source) :
    curvatureDefect source (sourceConnectionJet source) = 0 := by
  rw [curvatureDefect, nonAbelianCurvature_sourceConnectionJet]
  exact sub_self _

@[simp] theorem spacetimeHodgeVector_zero :
    spacetimeHodgeVector (0 : BivectorVector) = 0 := by
  ext pair
  rcases pair with ⟨internalPair, spacetimePair⟩
  fin_cases spacetimePair <;>
    simp [spacetimeHodgeVector, lorentzianCoframeHodge]

@[simp] theorem sourceStationary_bivectorDefect (source : Source) :
    bivectorDefect source (sourceStationaryConfiguration source).bivector = 0 := by
  simp [bivectorDefect, sourceStationaryConfiguration,
    sourceActionConfiguration]

@[simp] theorem sourceStationary_physicalBivectorDefect (source : Source) :
    physicalBivectorDefect source
        (sourceStationaryConfiguration source).tetrad = 0 :=
  by
    simp [physicalBivectorDefect, sourceStationaryConfiguration,
      sourceActionConfiguration, sourceBivectorAtOrigin]

@[simp] theorem sourceStationary_curvatureDefect (source : Source) :
    curvatureDefect source
        (sourceStationaryConfiguration source).connection = 0 := by
  rw [curvatureDefect, sourceActionConfiguration_curvature_generated]
  exact sub_self _

theorem sourceRelativeAction_withConnection_eq_zero
    (source : Source) (connection : ConnectionJet) :
    sourceRelativeMasterAction source
        ((sourceStationaryConfiguration source).withConnection connection) = 0 := by
  simp [sourceRelativeMasterAction, Configuration.withConnection]

theorem sourceRelativeAction_withMultiplier_eq_zero
    (source : Source) (multiplier : BivectorVector) :
    sourceRelativeMasterAction source
        ((sourceStationaryConfiguration source).withMultiplier multiplier) = 0 := by
  simp [sourceRelativeMasterAction, Configuration.withMultiplier]

theorem sourceRelativeAction_withTetrad_eq_zero
    (source : Source) (tetrad : TetradVector) :
    sourceRelativeMasterAction source
        ((sourceStationaryConfiguration source).withTetrad tetrad) = 0 := by
  simp [sourceRelativeMasterAction, Configuration.withTetrad,
    sourceActionConfiguration]

theorem sourceRelativeAction_withBivector_eq_penalty
    (source : Source) (bivector : BivectorVector) :
    sourceRelativeMasterAction source
        ((sourceStationaryConfiguration source).withBivector bivector) =
      -(1 / 2 : ℝ) *
        ‖bivector - sourceBivectorAtOrigin source‖ ^ 2 := by
  simp [sourceRelativeMasterAction, Configuration.withBivector,
    bivectorDefect, sourceActionConfiguration]

set_option synthInstance.maxHeartbeats 100000 in
theorem sourceStationary_deltaOmega (source : Source) :
    deltaOmega source (sourceStationaryConfiguration source) = 0 := by
  have hzero :
      HasFDerivAt
        (fun connection =>
          sourceRelativeMasterAction source
            ((sourceStationaryConfiguration source).withConnection connection))
        (0 : ConnectionJet →L[ℝ] ℝ)
        (sourceStationaryConfiguration source).connection :=
    (hasFDerivAt_const
      (𝕜 := ℝ)
      (x := (sourceStationaryConfiguration source).connection)
      (c := (0 : ℝ))).congr_of_eventuallyEq
        (Filter.Eventually.of_forall
          (sourceRelativeAction_withConnection_eq_zero source))
  exact (actual_connection_derivative source
    (sourceStationaryConfiguration source)).unique hzero

theorem sourceStationary_deltaB (source : Source) :
    deltaB source (sourceStationaryConfiguration source) = 0 := by
  have hpenalty :
      HasFDerivAt
        (fun bivector : BivectorVector =>
          -(1 / 2 : ℝ) *
            ‖bivector - sourceBivectorAtOrigin source‖ ^ 2)
        (0 : BivectorVector →L[ℝ] ℝ)
        (sourceStationaryConfiguration source).bivector := by
    simpa [sourceStationaryConfiguration, sourceActionConfiguration] using
      (((hasFDerivAt_id
          (𝕜 := ℝ)
          (x := sourceBivectorAtOrigin source)).sub_const
            (sourceBivectorAtOrigin source)).norm_sq.const_mul
        (-(1 / 2 : ℝ)))
  have hzero :
      HasFDerivAt
        (fun bivector =>
          sourceRelativeMasterAction source
            ((sourceStationaryConfiguration source).withBivector bivector))
        (0 : BivectorVector →L[ℝ] ℝ)
        (sourceStationaryConfiguration source).bivector :=
    hpenalty.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun bivector => by
        exact sourceRelativeAction_withBivector_eq_penalty source bivector)
  exact (actual_bivector_derivative source
    (sourceStationaryConfiguration source)).unique hzero

theorem sourceStationary_deltaPhi (source : Source) :
    deltaPhi source (sourceStationaryConfiguration source) = 0 := by
  simp [deltaPhi]

theorem sourceStationary_deltaE (source : Source) :
    deltaE source (sourceStationaryConfiguration source) = 0 := by
  have hzero :
      HasFDerivAt
        (fun tetrad =>
          sourceRelativeMasterAction source
            ((sourceStationaryConfiguration source).withTetrad tetrad))
        (0 : TetradVector →L[ℝ] ℝ)
        (sourceStationaryConfiguration source).tetrad :=
    (hasFDerivAt_const
      (𝕜 := ℝ)
      (x := (sourceStationaryConfiguration source).tetrad)
      (c := (0 : ℝ))).congr_of_eventuallyEq
        (Filter.Eventually.of_forall
          (sourceRelativeAction_withTetrad_eq_zero source))
  exact (actual_tetrad_derivative source
    (sourceStationaryConfiguration source)).unique hzero

structure PhysicalStationaryAtSource (source : Source) : Prop where
  deltaOmega_zero :
    deltaOmega source (sourceStationaryConfiguration source) = 0
  deltaB_zero : deltaB source (sourceStationaryConfiguration source) = 0
  deltaPhi_zero :
    deltaPhi source (sourceStationaryConfiguration source) = 0
  deltaE_zero : deltaE source (sourceStationaryConfiguration source) = 0

theorem source_generates_stationaryFamily (source : Source) :
    PhysicalStationaryAtSource source :=
  ⟨sourceStationary_deltaOmega source, sourceStationary_deltaB source,
    sourceStationary_deltaPhi source, sourceStationary_deltaE source⟩

end
end SaturationMonoid.PhysicsCore.SourceRelativePhysicalStationaryFamily
