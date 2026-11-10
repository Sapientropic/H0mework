import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.PhysicsCore.GeneratedEndpointQuadraticCoframeSource
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.PhysicsCore.PlebanskiFullVariationProvenance
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Quadratic geometry and a source-aligned stationary family

The quadratic-coordinate source already computes a nondegenerate coframe,
metric, Hodge operator, pointwise spin connection, and omega gluing.  This
module adds the missing stationary-family output at an explicitly finite
coordinate strength.

For each source coframe `eχ`, the common first-order action is

`Sχ(A,B,φ) = ⟨B-eχ,A⟩ + ½‖B-eχ‖²
  + (φ/2)(‖B‖²-‖eχ‖²)`.

All four stored residuals are proved to be the actual Mathlib Fréchet
derivatives of this one master/reduced action.  They vanish simultaneously at
`A=0`, `B=eχ`, `φ=0`, `e=eχ`, while every variation channel is nonzero at a
separate probe configuration.  Nondegeneracy of the generated coframe proves
that the stationary tetrad coordinate is not zero.

Boundary: this is a finite-dimensional, source-aligned constrained
first-order model carried by the typed Plebanski variation interface.  The
connection and auxiliary coordinates use the same 16-dimensional Euclidean
carrier and the raw `II+` substitution is the identity.  It does not yet
construct curvature, exterior products, the physical
`B = *(e ∧ e)` substitution, integration, boundary terms, or the continuum
Einstein equations.  Thus it closes the former *pre-stationary* gap only at
the stated candidate strength; it is not a full GR producer.
-/

namespace SaturationMonoid
namespace PhysicsCore
namespace QuadraticGeometryPlebanskiStationaryFamily

open GeneratedEndpointQuadraticCoframeSource
open scoped RealInnerProductSpace

noncomputable section

abbrev TetradCoordinate :=
  EuclideanSpace ℝ (Fin 16)

abbrev TetradCovector := TetradCoordinate →L[ℝ] ℝ
abbrev MultiplierCovector := ℝ →L[ℝ] ℝ

/-- Native constitutive input computed from one source coframe. -/
structure SourceAlignedLaw where
  sourceTetrad : TetradCoordinate

abbrev Configuration :=
  PlebanskiMasterConfiguration TetradCoordinate TetradCoordinate ℝ Unit

/-- One source-aligned finite constrained first-order action. -/
def masterAction (law : SourceAlignedLaw) (q : Configuration) : ℝ :=
  ⟪q.bivector - law.sourceTetrad, q.connection⟫ +
    (1 / 2 : ℝ) * ‖q.bivector - law.sourceTetrad‖ ^ 2 +
      (q.multiplier / 2) *
        (‖q.bivector‖ ^ 2 - ‖law.sourceTetrad‖ ^ 2)

/-- The computed multiplier variation. -/
def deltaPhi
    (law : SourceAlignedLaw) (q : Configuration) : MultiplierCovector :=
  ((‖q.bivector‖ ^ 2 - ‖law.sourceTetrad‖ ^ 2) / 2) •
    ContinuousLinearMap.id ℝ ℝ

/-- Strict finite-coordinate `II+` substitution used by this candidate. -/
def rawSubstitution :
    RawPlebanskiIIPlusSubstitution TetradCoordinate TetradCoordinate where
  tetradWedge := id
  internalBivectorDual := id

/-- The reduced action is computed from the master action, not supplied as an
independent reported value. -/
def reducedAction
    (law : SourceAlignedLaw) (q : Configuration)
    (e : TetradCoordinate) : ℝ :=
  restrictMasterActionByIIPlusSubstitution rawSubstitution masterAction law q e

/-- Smoothness of the three high-dimensional action slices.  Their actual
variations below are defined as `fderiv`, avoiding any dependence on an
implementation-specific normal form for the Euclidean-space inner-product
derivative. -/
theorem masterAction_bivector_contDiff
    (law : SourceAlignedLaw) (q : Configuration) :
    ContDiff ℝ ⊤
      (fun b : TetradCoordinate => masterAction law (q.withBivector b)) := by
  have hdefect :
      ContDiff ℝ ⊤
        (fun b : TetradCoordinate => b - law.sourceTetrad) :=
    contDiff_id.sub contDiff_const
  have hinner :
      ContDiff ℝ ⊤
        (fun b : TetradCoordinate =>
          ⟪b - law.sourceTetrad, q.connection⟫) :=
    hdefect.inner ℝ contDiff_const
  have hpenalty :
      ContDiff ℝ ⊤
        (fun b : TetradCoordinate =>
          (1 / 2 : ℝ) * ‖b - law.sourceTetrad‖ ^ 2) :=
    ContDiff.const_smul (R := ℝ) (1 / 2 : ℝ) (hdefect.norm_sq ℝ)
  have hsimplicity :
      ContDiff ℝ ⊤
        (fun b : TetradCoordinate =>
          (q.multiplier / 2) *
            (‖b‖ ^ 2 - ‖law.sourceTetrad‖ ^ 2)) :=
    ContDiff.const_smul (R := ℝ) (q.multiplier / 2)
      ((contDiff_id.norm_sq ℝ).sub contDiff_const)
  simpa [masterAction, PlebanskiMasterConfiguration.withBivector] using
    (hinner.add hpenalty).add hsimplicity

theorem masterAction_connection_contDiff
    (law : SourceAlignedLaw) (q : Configuration) :
    ContDiff ℝ ⊤
      (fun connection : TetradCoordinate =>
        masterAction law (q.withConnection connection)) := by
  have hinner :
      ContDiff ℝ ⊤
        (fun connection : TetradCoordinate =>
          ⟪q.bivector - law.sourceTetrad, connection⟫) :=
    contDiff_const.inner ℝ contDiff_id
  have hconstant :
      ContDiff ℝ ⊤
        (fun _connection : TetradCoordinate =>
          (1 / 2 : ℝ) * ‖q.bivector - law.sourceTetrad‖ ^ 2 +
            (q.multiplier / 2) *
              (‖q.bivector‖ ^ 2 - ‖law.sourceTetrad‖ ^ 2)) :=
    contDiff_const
  simpa [masterAction, PlebanskiMasterConfiguration.withConnection,
    add_assoc] using
    hinner.add hconstant

theorem reducedAction_tetrad_contDiff
    (law : SourceAlignedLaw) (q : Configuration) :
    ContDiff ℝ ⊤ (fun e : TetradCoordinate => reducedAction law q e) := by
  simpa [reducedAction, rawSubstitution,
    restrictMasterActionByIIPlusSubstitution,
    RawPlebanskiIIPlusSubstitution.gravitationalBivector] using
      masterAction_bivector_contDiff law q

/-- The computed `δB` is the actual Fréchet derivative of the master action. -/
def deltaB (law : SourceAlignedLaw) (q : Configuration) : TetradCovector :=
  fderiv ℝ (fun b : TetradCoordinate => masterAction law (q.withBivector b))
    q.bivector

/-- The computed connection-coordinate variation. -/
def deltaOmega
    (law : SourceAlignedLaw) (q : Configuration) : TetradCovector :=
  fderiv ℝ
    (fun connection : TetradCoordinate =>
      masterAction law (q.withConnection connection)) q.connection

/-- The computed tetrad-coordinate variation of the reduced action. -/
def deltaE
    (law : SourceAlignedLaw) (q : Configuration)
    (e : TetradCoordinate) : TetradCovector :=
  fderiv ℝ (fun tetrad : TetradCoordinate => reducedAction law q tetrad) e

/-! ## Actual Fréchet derivatives -/

theorem actual_bivector_derivative
    (law : SourceAlignedLaw) (q : Configuration) :
    HasFDerivAt
      (fun b : TetradCoordinate => masterAction law (q.withBivector b))
      (deltaB law q) q.bivector :=
  ((masterAction_bivector_contDiff law q).differentiable (by simp))
    |>.differentiableAt.hasFDerivAt

theorem actual_multiplier_derivative
    (law : SourceAlignedLaw) (q : Configuration) :
    HasFDerivAt
      (fun multiplier : ℝ => masterAction law (q.withMultiplier multiplier))
      (deltaPhi law q) q.multiplier := by
  let coefficient : ℝ :=
    (‖q.bivector‖ ^ 2 - ‖law.sourceTetrad‖ ^ 2) / 2
  have hvariable :
      HasFDerivAt
        (fun multiplier : ℝ => coefficient * multiplier)
        (coefficient • ContinuousLinearMap.id ℝ ℝ) q.multiplier :=
    (hasFDerivAt_id (x := q.multiplier)).const_mul coefficient
  simpa [masterAction, PlebanskiMasterConfiguration.withMultiplier,
    deltaPhi, coefficient, div_eq_mul_inv, mul_comm, mul_left_comm,
    mul_assoc, add_comm, add_left_comm, add_assoc] using
      hvariable.add_const
        (⟪q.bivector - law.sourceTetrad, q.connection⟫ +
          (1 / 2 : ℝ) * ‖q.bivector - law.sourceTetrad‖ ^ 2)

theorem actual_connection_derivative
    (law : SourceAlignedLaw) (q : Configuration) :
    HasFDerivAt
      (fun connection : TetradCoordinate =>
        masterAction law (q.withConnection connection))
      (deltaOmega law q) q.connection :=
  ((masterAction_connection_contDiff law q).differentiable (by simp))
    |>.differentiableAt.hasFDerivAt

theorem actual_tetrad_derivative
    (law : SourceAlignedLaw) (q : Configuration) (e : TetradCoordinate) :
    HasFDerivAt
      (fun tetrad : TetradCoordinate => reducedAction law q tetrad)
      (deltaE law q e) e :=
  ((reducedAction_tetrad_contDiff law q).differentiable (by simp))
    |>.differentiableAt.hasFDerivAt

/-! ## One common action system -/

abbrev System :=
  SmoothPlebanskiActionVariationSystem (Scalar := ℝ)
    (Constitutive := SourceAlignedLaw) (Connection := TetradCoordinate)
    (BivectorTwoForm := TetradCoordinate) (Multiplier := ℝ)
    (Matter := Unit) (Tetrad := TetradCoordinate) (ActionValue := ℝ)

def firstVariation :
    PlebanskiFirstVariationOperators SourceAlignedLaw TetradCoordinate
      TetradCoordinate ℝ Unit TetradCoordinate ℝ TetradCovector
      MultiplierCovector TetradCovector TetradCovector where
  deltaBOf := fun _ law q => deltaB law q
  deltaPhiOf := fun _ law q => deltaPhi law q
  deltaOmegaOf := fun _ law q => deltaOmega law q
  deltaEOf := fun _ law q e => deltaE law q e

def system : System where
  masterAction := masterAction
  reducedIIPlusAction := reducedAction
  firstVariation := firstVariation

theorem system_reductionCoherent :
    PlebanskiRawIIPlusReductionCoherent system rawSubstitution :=
  rfl

theorem system_fullFirstVariationCorrect :
    PlebanskiFullFirstVariationCorrect system := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro law q
    simpa [system, firstVariation] using actual_bivector_derivative law q
  · intro law q
    simpa [system, firstVariation] using actual_multiplier_derivative law q
  · intro law q
    simpa [system, firstVariation] using actual_connection_derivative law q
  · intro law q e
    simpa [system, firstVariation] using actual_tetrad_derivative law q e

theorem system_actionProvenanceAdmissible :
    PlebanskiActionProvenanceAdmissible system rawSubstitution :=
  ⟨system_reductionCoherent, system_fullFirstVariationCorrect⟩

def residuals := system.residuals

@[simp] theorem residuals_deltaB
    (law : SourceAlignedLaw) (q : Configuration) :
    residuals.deltaBResidual law q = deltaB law q :=
  rfl

@[simp] theorem residuals_deltaPhi
    (law : SourceAlignedLaw) (q : Configuration) :
    residuals.deltaPhiResidual law q = deltaPhi law q :=
  rfl

@[simp] theorem residuals_deltaOmega
    (law : SourceAlignedLaw) (q : Configuration) :
    residuals.deltaOmegaResidual law q = deltaOmega law q :=
  rfl

@[simp] theorem residuals_deltaE
    (law : SourceAlignedLaw) (q : Configuration) (e : TetradCoordinate) :
    residuals.deltaEAfterIIPlusResidual law q e = deltaE law q e :=
  rfl

/-! ## Source-aligned stationary family -/

def stationaryConfiguration (law : SourceAlignedLaw) : Configuration where
  connection := 0
  bivector := law.sourceTetrad
  multiplier := 0
  matter := ()

theorem stationaryAction_withConnection_eq_zero
    (law : SourceAlignedLaw) (connection : TetradCoordinate) :
    masterAction law
        ((stationaryConfiguration law).withConnection connection) = 0 := by
  simp [masterAction, stationaryConfiguration,
    PlebanskiMasterConfiguration.withConnection]

theorem stationaryAction_withBivector_eq_penalty
    (law : SourceAlignedLaw) (bivector : TetradCoordinate) :
    masterAction law
        ((stationaryConfiguration law).withBivector bivector) =
      (1 / 2 : ℝ) * ‖bivector - law.sourceTetrad‖ ^ 2 := by
  simp [masterAction, stationaryConfiguration,
    PlebanskiMasterConfiguration.withBivector]

theorem stationaryReducedAction_eq_penalty
    (law : SourceAlignedLaw) (tetrad : TetradCoordinate) :
    reducedAction law (stationaryConfiguration law) tetrad =
      (1 / 2 : ℝ) * ‖tetrad - law.sourceTetrad‖ ^ 2 := by
  simp [reducedAction, rawSubstitution,
    restrictMasterActionByIIPlusSubstitution,
    RawPlebanskiIIPlusSubstitution.gravitationalBivector,
    masterAction, stationaryConfiguration,
    PlebanskiMasterConfiguration.withBivector]

theorem stationary_deltaB (law : SourceAlignedLaw) :
    deltaB law (stationaryConfiguration law) = 0 := by
  have hpenalty :
      HasFDerivAt
        (fun bivector : TetradCoordinate =>
          (1 / 2 : ℝ) * ‖bivector - law.sourceTetrad‖ ^ 2)
        (0 : TetradCovector) law.sourceTetrad := by
    simpa using
      (((hasFDerivAt_id (𝕜 := ℝ) (x := law.sourceTetrad)).sub_const
        law.sourceTetrad).norm_sq.const_mul (1 / 2 : ℝ))
  have hzero :
      HasFDerivAt
        (fun bivector : TetradCoordinate =>
          masterAction law
            ((stationaryConfiguration law).withBivector bivector))
        (0 : TetradCovector) law.sourceTetrad :=
    hpenalty.congr_of_eventuallyEq
      (Filter.Eventually.of_forall
        (stationaryAction_withBivector_eq_penalty law))
  exact (actual_bivector_derivative law
    (stationaryConfiguration law)).unique hzero

theorem stationary_deltaPhi (law : SourceAlignedLaw) :
    deltaPhi law (stationaryConfiguration law) = 0 := by
  simp [deltaPhi, stationaryConfiguration]

theorem stationary_deltaOmega (law : SourceAlignedLaw) :
    deltaOmega law (stationaryConfiguration law) = 0 := by
  have hzero :
      HasFDerivAt
        (fun connection : TetradCoordinate =>
          masterAction law
            ((stationaryConfiguration law).withConnection connection))
        (0 : TetradCovector) 0 :=
    (hasFDerivAt_const
      (𝕜 := ℝ) (x := (0 : TetradCoordinate)) (c := (0 : ℝ)))
      |>.congr_of_eventuallyEq
        (Filter.Eventually.of_forall
          (stationaryAction_withConnection_eq_zero law))
  exact (actual_connection_derivative law
    (stationaryConfiguration law)).unique hzero

theorem stationary_deltaE (law : SourceAlignedLaw) :
    deltaE law (stationaryConfiguration law) law.sourceTetrad = 0 := by
  have hpenalty :
      HasFDerivAt
        (fun tetrad : TetradCoordinate =>
          (1 / 2 : ℝ) * ‖tetrad - law.sourceTetrad‖ ^ 2)
        (0 : TetradCovector) law.sourceTetrad := by
    simpa using
      (((hasFDerivAt_id (𝕜 := ℝ) (x := law.sourceTetrad)).sub_const
        law.sourceTetrad).norm_sq.const_mul (1 / 2 : ℝ))
  have hzero :
      HasFDerivAt
        (fun tetrad : TetradCoordinate =>
          reducedAction law (stationaryConfiguration law) tetrad)
        (0 : TetradCovector) law.sourceTetrad :=
    hpenalty.congr_of_eventuallyEq
      (Filter.Eventually.of_forall
        (stationaryReducedAction_eq_penalty law))
  exact (actual_tetrad_derivative law
    (stationaryConfiguration law) law.sourceTetrad).unique hzero

theorem stationary_masterOnShell (law : SourceAlignedLaw) :
    residuals.MasterOnShell law (stationaryConfiguration law) := by
  exact ⟨stationary_deltaB law, stationary_deltaPhi law,
    stationary_deltaOmega law⟩

theorem stationary_deltaEOnShell (law : SourceAlignedLaw) :
    residuals.DeltaEOnShell law (stationaryConfiguration law)
      law.sourceTetrad := by
  exact stationary_deltaE law

/-! ## No identically-zero variation channel -/

def probeVector : TetradCoordinate :=
  EuclideanSpace.basisFun (Fin 16) ℝ 0

theorem probeVector_norm : ‖probeVector‖ = 1 := by
  exact
    (EuclideanSpace.basisFun (Fin 16) ℝ).norm_eq_one 0

theorem innerSL_probeVector_ne_zero : innerSL ℝ probeVector ≠ 0 := by
  intro hzero
  have hvalue :=
    congrArg (fun L : TetradCovector => L probeVector) hzero
  simpa [innerSL_apply_apply, inner_self_eq_norm_sq, probeVector_norm] using
    hvalue

def zeroLaw : SourceAlignedLaw := ⟨0⟩

def deltaBProbeConfiguration : Configuration where
  connection := probeVector
  bivector := 0
  multiplier := 0
  matter := ()

def deltaPhiProbeConfiguration : Configuration where
  connection := 0
  bivector := probeVector
  multiplier := 0
  matter := ()

def deltaOmegaProbeConfiguration : Configuration where
  connection := 0
  bivector := probeVector
  multiplier := 0
  matter := ()

def deltaEProbeConfiguration : Configuration where
  connection := 0
  bivector := 0
  multiplier := 0
  matter := ()

theorem deltaBProbe_action
    (bivector : TetradCoordinate) :
    masterAction zeroLaw
        (deltaBProbeConfiguration.withBivector bivector) =
      ⟪bivector, probeVector⟫ +
        (1 / 2 : ℝ) * ‖bivector‖ ^ 2 := by
  simp [masterAction, zeroLaw, deltaBProbeConfiguration,
    PlebanskiMasterConfiguration.withBivector]

theorem deltaOmegaProbe_action
    (connection : TetradCoordinate) :
    masterAction zeroLaw
        (deltaOmegaProbeConfiguration.withConnection connection) =
      ⟪probeVector, connection⟫ +
        (1 / 2 : ℝ) * ‖probeVector‖ ^ 2 := by
  simp [masterAction, zeroLaw, deltaOmegaProbeConfiguration,
    PlebanskiMasterConfiguration.withConnection]

theorem deltaEProbe_action
    (tetrad : TetradCoordinate) :
    reducedAction zeroLaw deltaEProbeConfiguration tetrad =
      (1 / 2 : ℝ) * ‖tetrad‖ ^ 2 := by
  simp [reducedAction, rawSubstitution,
    restrictMasterActionByIIPlusSubstitution,
    RawPlebanskiIIPlusSubstitution.gravitationalBivector,
    masterAction, zeroLaw, deltaEProbeConfiguration,
    PlebanskiMasterConfiguration.withBivector]

theorem deltaB_not_identically_zero :
    deltaB zeroLaw deltaBProbeConfiguration ≠ 0 := by
  have hlinear :
      HasFDerivAt
        (fun bivector : TetradCoordinate => ⟪bivector, probeVector⟫)
        (innerSL ℝ probeVector) 0 := by
    simpa only [coe_innerSL_apply, real_inner_comm] using
      (innerSL ℝ probeVector).hasFDerivAt
        (x := (0 : TetradCoordinate))
  have hquadratic :
      HasFDerivAt
        (fun bivector : TetradCoordinate =>
          (1 / 2 : ℝ) * ‖bivector‖ ^ 2)
        (0 : TetradCovector) 0 := by
    simpa using
      ((hasStrictFDerivAt_norm_sq (0 : TetradCoordinate)).hasFDerivAt
        |>.const_mul (1 / 2 : ℝ))
  have hprobe :
      HasFDerivAt
        (fun bivector : TetradCoordinate =>
          masterAction zeroLaw
            (deltaBProbeConfiguration.withBivector bivector))
        (innerSL ℝ probeVector) 0 := by
    simpa only [add_zero] using
      (hlinear.add hquadratic).congr_of_eventuallyEq
        (Filter.Eventually.of_forall deltaBProbe_action)
  have heq :
      deltaB zeroLaw deltaBProbeConfiguration = innerSL ℝ probeVector := by
    exact (actual_bivector_derivative zeroLaw deltaBProbeConfiguration).unique
      (by simpa [deltaBProbeConfiguration] using hprobe)
  rw [heq]
  exact innerSL_probeVector_ne_zero

theorem deltaPhi_not_identically_zero :
    deltaPhi zeroLaw deltaPhiProbeConfiguration ≠ 0 := by
  intro hzero
  have hvalue :=
    congrArg (fun L : MultiplierCovector => L 1) hzero
  norm_num [deltaPhi, zeroLaw, deltaPhiProbeConfiguration,
    probeVector_norm] at hvalue

theorem deltaOmega_not_identically_zero :
    deltaOmega zeroLaw deltaOmegaProbeConfiguration ≠ 0 := by
  have hlinear :
      HasFDerivAt
        (fun connection : TetradCoordinate => ⟪probeVector, connection⟫)
        (innerSL ℝ probeVector) 0 :=
    (innerSL ℝ probeVector).hasFDerivAt
      (x := (0 : TetradCoordinate))
  have hprobe :
      HasFDerivAt
        (fun connection : TetradCoordinate =>
          masterAction zeroLaw
            (deltaOmegaProbeConfiguration.withConnection connection))
        (innerSL ℝ probeVector) 0 :=
    (hlinear.add_const ((1 / 2 : ℝ) * ‖probeVector‖ ^ 2))
      |>.congr_of_eventuallyEq
        (Filter.Eventually.of_forall deltaOmegaProbe_action)
  have heq :
      deltaOmega zeroLaw deltaOmegaProbeConfiguration =
        innerSL ℝ probeVector := by
    exact
      (actual_connection_derivative zeroLaw deltaOmegaProbeConfiguration).unique
        (by simpa [deltaOmegaProbeConfiguration] using hprobe)
  rw [heq]
  exact innerSL_probeVector_ne_zero

theorem deltaE_not_identically_zero :
    deltaE zeroLaw deltaEProbeConfiguration probeVector ≠ 0 := by
  have hquadratic :
      HasFDerivAt
        (fun tetrad : TetradCoordinate =>
          (1 / 2 : ℝ) * ‖tetrad‖ ^ 2)
        (innerSL ℝ probeVector) probeVector := by
    have hraw :=
      ((hasStrictFDerivAt_norm_sq probeVector).hasFDerivAt
        |>.const_mul (1 / 2 : ℝ))
    have hscale :
        (1 / 2 : ℝ) • ((2 : Nat) • (innerSL ℝ probeVector)) =
          innerSL ℝ probeVector := by
      ext value
      simp
    exact hscale ▸ hraw
  have hprobe :
      HasFDerivAt
        (fun tetrad : TetradCoordinate =>
          reducedAction zeroLaw deltaEProbeConfiguration tetrad)
        (innerSL ℝ probeVector) probeVector :=
    hquadratic.congr_of_eventuallyEq
      (Filter.Eventually.of_forall deltaEProbe_action)
  have heq :
      deltaE zeroLaw deltaEProbeConfiguration probeVector =
        innerSL ℝ probeVector :=
    (actual_tetrad_derivative zeroLaw deltaEProbeConfiguration probeVector)
      |>.unique hprobe
  rw [heq]
  exact innerSL_probeVector_ne_zero

theorem system_hasNontrivialVariationChannels :
    residuals.HasNontrivialVariationChannels := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨zeroLaw, deltaBProbeConfiguration, by
      simpa only [residuals_deltaB] using deltaB_not_identically_zero⟩
  · exact ⟨zeroLaw, deltaPhiProbeConfiguration, by
      simpa only [residuals_deltaPhi] using deltaPhi_not_identically_zero⟩
  · exact ⟨zeroLaw, deltaOmegaProbeConfiguration, by
      simpa only [residuals_deltaOmega] using deltaOmega_not_identically_zero⟩
  · exact ⟨zeroLaw, deltaEProbeConfiguration, probeVector, by
      simpa only [residuals_deltaE] using deltaE_not_identically_zero⟩

/-! ## Quadratic-source producer -/

/-- A polynomial geometry observation on its native nondegenerate slice. -/
abbrev NondegenerateQuadraticGeometrySource :=
  { observation : GeometryObservation //
    Matrix.det observation.generatedJet.coframe ≠ 0 }

/-- Flatten the generated `4×4` coframe into its finite Euclidean tetrad
coordinate. -/
def tetradVectorOfCoframe
    (coframe : LorentzianCoframe) : TetradCoordinate :=
  WithLp.toLp 2 (fun index : Fin 16 =>
    let pair := finProdFinEquiv.symm index
    coframe pair.1 pair.2)

theorem tetradVectorOfCoframe_ne_zero
    (coframe : LorentzianCoframe)
    (hnondegenerate : Matrix.det coframe ≠ 0) :
    tetradVectorOfCoframe coframe ≠ 0 := by
  intro hzero
  have hflat :
      (fun index : Fin 16 =>
        let pair := finProdFinEquiv.symm index
        coframe pair.1 pair.2) = 0 := by
    simpa [tetradVectorOfCoframe] using hzero
  have hcoframe : coframe = 0 := by
    ext internal coordinate
    have hvalue := congrFun hflat (finProdFinEquiv (internal, coordinate))
    simpa using hvalue
  exact hnondegenerate (by simp [hcoframe])

def lawOfQuadraticGeometry
    (source : NondegenerateQuadraticGeometrySource) :
    SourceAlignedLaw where
  sourceTetrad := tetradVectorOfCoframe source.1.generatedJet.coframe

theorem generatedLaw_sourceTetrad_ne_zero
    (source : NondegenerateQuadraticGeometrySource) :
    (lawOfQuadraticGeometry source).sourceTetrad ≠ 0 :=
  tetradVectorOfCoframe_ne_zero source.1.generatedJet.coframe source.2

/-- Complete output currently generated by one nondegenerate quadratic
geometry source, including its exact finite stationary family member. -/
structure QuadraticGeometryStationaryCandidate where
  coordinateSource : QuadraticCoordinateSource
  observationPoint : LorentzianCoordinatePoint
  jet : PointwiseLorentzianCoframeJet
  jet_generated : jet = coordinateSource.jetAt observationPoint
  jet_nondegenerate : Matrix.det jet.coframe ≠ 0
  geometry : PointwiseLorentzGeometryOutput jet
  law : SourceAlignedLaw
  law_generated : law.sourceTetrad = tetradVectorOfCoframe jet.coframe
  stationaryPoint : Configuration
  stationaryPoint_generated : stationaryPoint = stationaryConfiguration law
  stationaryTetrad : TetradCoordinate
  stationaryTetrad_generated : stationaryTetrad = law.sourceTetrad
  stationaryTetrad_ne_zero : stationaryTetrad ≠ 0
  master_onShell : residuals.MasterOnShell law stationaryPoint
  tetrad_onShell :
    residuals.DeltaEOnShell law stationaryPoint stationaryTetrad

/-- Native producer from polynomial coefficients and a nonzero computed
Jacobian determinant.  No stationary point or action compatibility witness is
accepted from the caller. -/
def stationaryCandidateOf
    (source : NondegenerateQuadraticGeometrySource) :
    QuadraticGeometryStationaryCandidate :=
  let law := lawOfQuadraticGeometry source
  { coordinateSource := source.1.source
    observationPoint := source.1.point
    jet := source.1.generatedJet
    jet_generated := rfl
    jet_nondegenerate := source.2
    geometry :=
      producePointwiseLorentzGeometryFromJet
        source.1.generatedJet source.2
    law := law
    law_generated := rfl
    stationaryPoint := stationaryConfiguration law
    stationaryPoint_generated := rfl
    stationaryTetrad := law.sourceTetrad
    stationaryTetrad_generated := rfl
    stationaryTetrad_ne_zero := generatedLaw_sourceTetrad_ne_zero source
    master_onShell := stationary_masterOnShell law
    tetrad_onShell := stationary_deltaEOnShell law }

/-- Main geometry-axis result at the exact proved strength: the computed jet,
metric, and Hodge data are paired with a nonzero common-action stationary
family member; the common action has four genuine and nontrivial variation
channels. -/
theorem quadraticGeometry_generates_tetradMetricHodgeStationaryFamily
    (source : NondegenerateQuadraticGeometrySource) :
    let candidate := stationaryCandidateOf source
    candidate.jet = source.1.source.jetAt source.1.point ∧
      candidate.geometry.metric = candidate.jet.metric ∧
      candidate.geometry.hodge = lorentzianCoframeHodge ∧
      candidate.stationaryTetrad ≠ 0 ∧
      PlebanskiActionProvenanceAdmissible system rawSubstitution ∧
      residuals.HasNontrivialVariationChannels ∧
      residuals.MasterOnShell candidate.law candidate.stationaryPoint ∧
      residuals.DeltaEOnShell candidate.law candidate.stationaryPoint
        candidate.stationaryTetrad := by
  dsimp only
  exact
    ⟨rfl, rfl, rfl,
      (stationaryCandidateOf source).stationaryTetrad_ne_zero,
      system_actionProvenanceAdmissible,
      system_hasNontrivialVariationChannels,
      (stationaryCandidateOf source).master_onShell,
      (stationaryCandidateOf source).tetrad_onShell⟩

end
end QuadraticGeometryPlebanskiStationaryFamily
end PhysicsCore
end SaturationMonoid
