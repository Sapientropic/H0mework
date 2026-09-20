import H0mework.Physics.GaugeAction.P286GaugeConnectionPointwiseEquation
import H0mework.Physics.Lorentz.LorentzConnectionPointwiseEquation
import H0mework.Physics.Matter.ConjugateMatterVariation
import H0mework.Physics.Matter.MatterPointwiseEquation
import H0mework.Physics.Geometry.ScalarPointwiseEquation
import H0mework.Physics.Coframe.CoframePointwiseEquation

/-!
# S9-C3g1: current Stage-9 joint-shell residual carrier

This module aggregates the nine typed residual channels already derived from
the current Stage-9 action.  It adds no physical field, coupling, boundary
datum, branch selector, or equation receipt.  Its only constructor computes a
pointwise residual from a primitive enriched source and a holonomic
configuration.

The first three slots are the current strong algebraic shell coordinates.  In
particular, `gravityAuxiliary` is the existing triangular residual `F - J B`:
off the simplicity shell it is not the complete auxiliary-field variation.
The pair consisting of the simplicity residual and this triangular residual
is the representation used by the current strong gravity shell.  The later
stationarity-to-zero theorem must therefore eliminate the simplicity
residual first and only then eliminate the gravity-auxiliary residual.

The remaining six slots are the actual pointwise directional/covector
Euler--Lagrange residuals.  Directional families stay as raw function types;
no unproved linearity or continuity package is inserted into the carrier.

Smoothness, nondegeneracy, Lorentz admissibility, Bianchi identities,
integrability, exact lineage, stationarity, standing, and no-third-sink
responsibility remain external predicates or relations.  Full P286 auxiliary
variation already covers the current three equal-coupling blocks, so the
hypercharge-only audit is deliberately not duplicated here.
-/

namespace SaturationMonoid.PhysicsCore.StageNineJointShellResidualCarrier

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineDynamicBreakingVacuum
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNinePlebanskiMultiplierVariation
open StageNineGravityAuxiliaryVariation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeAuxiliaryEquation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineLorentzConnectionVariation
open StageNineLorentzConnectionPointwiseEquation
open StageNineConjugateMatterVariation
open StageNineMatterPointwiseEquation
open StageNineScalarPointwiseEquation
open StageNineCoframeLocalDifferentiability
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory
open DiracExteriorMatterAction

noncomputable section

set_option autoImplicit false

abbrev CurrentSmoothUnifiedSource :=
  StageNineEnrichedProofFreeSource.SmoothUnifiedSource

/-- The three strong algebraic residual coordinates at one spacetime point.

`gravityAuxiliary` is triangular: it becomes the complete strong auxiliary
equation after `gravitySimplicity = 0`. -/
structure CurrentPointwiseAlgebraicResidualCarrier where
  gravitySimplicity : PhysicalBivector
  gravityAuxiliary : PhysicalBivector
  p286GaugeAuxiliary : P286GaugeTwoForm

instance : Zero CurrentPointwiseAlgebraicResidualCarrier where
  zero :=
    { gravitySimplicity := 0
      gravityAuxiliary := 0
      p286GaugeAuxiliary := 0 }

@[simp] theorem zero_algebraic_gravitySimplicity :
    (0 : CurrentPointwiseAlgebraicResidualCarrier).gravitySimplicity = 0 :=
  rfl

@[simp] theorem zero_algebraic_gravityAuxiliary :
    (0 : CurrentPointwiseAlgebraicResidualCarrier).gravityAuxiliary = 0 :=
  rfl

@[simp] theorem zero_algebraic_p286GaugeAuxiliary :
    (0 : CurrentPointwiseAlgebraicResidualCarrier).p286GaugeAuxiliary = 0 :=
  rfl

@[ext] theorem CurrentPointwiseAlgebraicResidualCarrier.ext
    (first second : CurrentPointwiseAlgebraicResidualCarrier)
    (gravitySimplicity : first.gravitySimplicity = second.gravitySimplicity)
    (gravityAuxiliary : first.gravityAuxiliary = second.gravityAuxiliary)
    (p286GaugeAuxiliary :
      first.p286GaugeAuxiliary = second.p286GaugeAuxiliary) :
    first = second := by
  cases first
  cases second
  simp_all

/-- The six pointwise differential/algebraic EL residual coordinates. -/
structure CurrentPointwiseEulerLagrangeResidualCarrier where
  lorentzConnection : LorentzBivectorOneForm → ℝ
  p286GaugeConnection : P286GaugeOneForm → ℝ
  scalar : ScalarCoordinateCarrier → ℝ
  matter : MatterCoordinateCarrier → ℝ
  conjugateMatter : MatterCoordinateCarrier → ℝ
  coframe : LorentzianCoframe →L[ℝ] ℝ

instance : Zero CurrentPointwiseEulerLagrangeResidualCarrier where
  zero :=
    { lorentzConnection := 0
      p286GaugeConnection := 0
      scalar := 0
      matter := 0
      conjugateMatter := 0
      coframe := 0 }

@[simp] theorem zero_eulerLagrange_lorentzConnection :
    (0 : CurrentPointwiseEulerLagrangeResidualCarrier).lorentzConnection = 0 :=
  rfl

@[simp] theorem zero_eulerLagrange_p286GaugeConnection :
    (0 : CurrentPointwiseEulerLagrangeResidualCarrier).p286GaugeConnection = 0 :=
  rfl

@[simp] theorem zero_eulerLagrange_scalar :
    (0 : CurrentPointwiseEulerLagrangeResidualCarrier).scalar = 0 :=
  rfl

@[simp] theorem zero_eulerLagrange_matter :
    (0 : CurrentPointwiseEulerLagrangeResidualCarrier).matter = 0 :=
  rfl

@[simp] theorem zero_eulerLagrange_conjugateMatter :
    (0 : CurrentPointwiseEulerLagrangeResidualCarrier).conjugateMatter = 0 :=
  rfl

@[simp] theorem zero_eulerLagrange_coframe :
    (0 : CurrentPointwiseEulerLagrangeResidualCarrier).coframe = 0 :=
  rfl

@[ext] theorem CurrentPointwiseEulerLagrangeResidualCarrier.ext
    (first second : CurrentPointwiseEulerLagrangeResidualCarrier)
    (lorentzConnection : first.lorentzConnection = second.lorentzConnection)
    (p286GaugeConnection :
      first.p286GaugeConnection = second.p286GaugeConnection)
    (scalar : first.scalar = second.scalar)
    (matter : first.matter = second.matter)
    (conjugateMatter : first.conjugateMatter = second.conjugateMatter)
    (coframe : first.coframe = second.coframe) :
    first = second := by
  cases first
  cases second
  simp_all

/-- The complete current pointwise joint-shell residual carrier. -/
structure CurrentPointwiseJointShellResidualCarrier where
  algebraic : CurrentPointwiseAlgebraicResidualCarrier
  eulerLagrange : CurrentPointwiseEulerLagrangeResidualCarrier

instance : Zero CurrentPointwiseJointShellResidualCarrier where
  zero :=
    { algebraic := 0
      eulerLagrange := 0 }

@[simp] theorem zero_joint_algebraic :
    (0 : CurrentPointwiseJointShellResidualCarrier).algebraic = 0 :=
  rfl

@[simp] theorem zero_joint_eulerLagrange :
    (0 : CurrentPointwiseJointShellResidualCarrier).eulerLagrange = 0 :=
  rfl

@[ext] theorem CurrentPointwiseJointShellResidualCarrier.ext
    (first second : CurrentPointwiseJointShellResidualCarrier)
    (algebraic : first.algebraic = second.algebraic)
    (eulerLagrange : first.eulerLagrange = second.eulerLagrange) :
    first = second := by
  cases first
  cases second
  simp_all

/-- Canonical algebraic residual readout.  It has no residual target or
equation witness argument. -/
def currentPointwiseAlgebraicResidual
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : CurrentPointwiseAlgebraicResidualCarrier where
  gravitySimplicity := generatedGravitySimplicityResidual
    (toContinuumPointField configuration point)
  gravityAuxiliary :=
    holonomicGravityAuxiliaryEquationResidual configuration point
  p286GaugeAuxiliary :=
    holonomicP286GaugeAuxiliaryEquationResidual source configuration point

/-- Canonical pointwise EL residual readout. -/
def currentPointwiseEulerLagrangeResidual
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : CurrentPointwiseEulerLagrangeResidualCarrier where
  lorentzConnection := fun direction =>
    lorentzConnectionEulerLagrangeCoefficient source configuration direction
      point
  p286GaugeConnection := fun direction =>
    p286GaugeConnectionEulerLagrangeCoefficient source configuration direction
      point
  scalar := fun direction =>
    scalarEulerLagrangeDirectionalCoefficient source configuration direction
      point
  matter := fun direction =>
    matterEulerLagrangeDirectionalCoefficient source configuration direction
      point
  conjugateMatter := fun direction =>
    conjugateMatterDirectionalCoefficient source configuration direction point
  coframe := coframeLocalStressCovector source point
    (toContinuumPointField configuration point)

/-- Canonical pointwise joint-shell residual readout. -/
def currentPointwiseJointShellResidual
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : CurrentPointwiseJointShellResidualCarrier where
  algebraic := currentPointwiseAlgebraicResidual source configuration point
  eulerLagrange :=
    currentPointwiseEulerLagrangeResidual source configuration point

/-- The residual section generated by one source/configuration pair. -/
def currentJointShellResidualSection
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    BasePoint → CurrentPointwiseJointShellResidualCarrier :=
  currentPointwiseJointShellResidual source configuration

def OnCurrentPointwiseAlgebraicZeroFiber
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : Prop :=
  currentPointwiseAlgebraicResidual source configuration point = 0

def OnCurrentPointwiseEulerLagrangeZeroFiber
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : Prop :=
  currentPointwiseEulerLagrangeResidual source configuration point = 0

def OnCurrentPointwiseJointShellZeroFiber
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : Prop :=
  currentPointwiseJointShellResidual source configuration point = 0

/-- Global zero fiber of the generated joint residual section. -/
def CurrentJointShellZeroFiber
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  currentJointShellResidualSection source configuration = 0

theorem onCurrentPointwiseJointShellZeroFiber_iff_layers
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    OnCurrentPointwiseJointShellZeroFiber source configuration point ↔
      OnCurrentPointwiseAlgebraicZeroFiber source configuration point ∧
      OnCurrentPointwiseEulerLagrangeZeroFiber source configuration point := by
  constructor
  · intro jointZero
    exact ⟨congrArg CurrentPointwiseJointShellResidualCarrier.algebraic jointZero,
      congrArg CurrentPointwiseJointShellResidualCarrier.eulerLagrange
        jointZero⟩
  · rintro ⟨algebraicZero, eulerLagrangeZero⟩
    exact CurrentPointwiseJointShellResidualCarrier.ext _ _ algebraicZero
      eulerLagrangeZero

theorem onCurrentPointwiseJointShellZeroFiber_iff_components
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    OnCurrentPointwiseJointShellZeroFiber source configuration point ↔
      generatedGravitySimplicityResidual
          (toContinuumPointField configuration point) = 0 ∧
      holonomicGravityAuxiliaryEquationResidual configuration point = 0 ∧
      holonomicP286GaugeAuxiliaryEquationResidual source configuration point =
        0 ∧
      (fun direction => lorentzConnectionEulerLagrangeCoefficient source
        configuration direction point) = 0 ∧
      (fun direction => p286GaugeConnectionEulerLagrangeCoefficient source
        configuration direction point) = 0 ∧
      (fun direction => scalarEulerLagrangeDirectionalCoefficient source
        configuration direction point) = 0 ∧
      (fun direction => matterEulerLagrangeDirectionalCoefficient source
        configuration direction point) = 0 ∧
      (fun direction => conjugateMatterDirectionalCoefficient source
        configuration direction point) = 0 ∧
      coframeLocalStressCovector source point
        (toContinuumPointField configuration point) = 0 := by
  constructor
  · intro jointZero
    have algebraicZero := congrArg
      (fun residual => residual.algebraic) jointZero
    have eulerLagrangeZero := congrArg
      (fun residual => residual.eulerLagrange) jointZero
    have gravitySimplicity := congrArg
      CurrentPointwiseAlgebraicResidualCarrier.gravitySimplicity algebraicZero
    have gravityAuxiliary := congrArg
      CurrentPointwiseAlgebraicResidualCarrier.gravityAuxiliary algebraicZero
    have p286GaugeAuxiliary := congrArg
      CurrentPointwiseAlgebraicResidualCarrier.p286GaugeAuxiliary algebraicZero
    have lorentzConnection := congrArg
      CurrentPointwiseEulerLagrangeResidualCarrier.lorentzConnection
        eulerLagrangeZero
    have p286GaugeConnection := congrArg
      CurrentPointwiseEulerLagrangeResidualCarrier.p286GaugeConnection
        eulerLagrangeZero
    have scalar := congrArg
      CurrentPointwiseEulerLagrangeResidualCarrier.scalar eulerLagrangeZero
    have matter := congrArg
      CurrentPointwiseEulerLagrangeResidualCarrier.matter eulerLagrangeZero
    have conjugateMatter := congrArg
      CurrentPointwiseEulerLagrangeResidualCarrier.conjugateMatter
        eulerLagrangeZero
    have coframe := congrArg
      CurrentPointwiseEulerLagrangeResidualCarrier.coframe eulerLagrangeZero
    simpa [currentPointwiseJointShellResidual,
      currentPointwiseAlgebraicResidual,
      currentPointwiseEulerLagrangeResidual] using
      ⟨gravitySimplicity, gravityAuxiliary, p286GaugeAuxiliary,
        lorentzConnection, p286GaugeConnection, scalar, matter,
        conjugateMatter, coframe⟩
  · rintro ⟨gravitySimplicity, gravityAuxiliary, p286GaugeAuxiliary,
      lorentzConnection, p286GaugeConnection, scalar, matter,
      conjugateMatter, coframe⟩
    apply CurrentPointwiseJointShellResidualCarrier.ext
    · apply CurrentPointwiseAlgebraicResidualCarrier.ext
      · simpa [currentPointwiseJointShellResidual,
          currentPointwiseAlgebraicResidual] using gravitySimplicity
      · simpa [currentPointwiseJointShellResidual,
          currentPointwiseAlgebraicResidual] using gravityAuxiliary
      · simpa [currentPointwiseJointShellResidual,
          currentPointwiseAlgebraicResidual] using p286GaugeAuxiliary
    · apply CurrentPointwiseEulerLagrangeResidualCarrier.ext
      · simpa [currentPointwiseJointShellResidual,
          currentPointwiseEulerLagrangeResidual] using lorentzConnection
      · simpa [currentPointwiseJointShellResidual,
          currentPointwiseEulerLagrangeResidual] using p286GaugeConnection
      · simpa [currentPointwiseJointShellResidual,
          currentPointwiseEulerLagrangeResidual] using scalar
      · simpa [currentPointwiseJointShellResidual,
          currentPointwiseEulerLagrangeResidual] using matter
      · simpa [currentPointwiseJointShellResidual,
          currentPointwiseEulerLagrangeResidual] using conjugateMatter
      · simpa [currentPointwiseJointShellResidual,
          currentPointwiseEulerLagrangeResidual] using coframe

theorem currentJointShellZeroFiber_iff_pointwise
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    CurrentJointShellZeroFiber source configuration ↔
      ∀ point, OnCurrentPointwiseJointShellZeroFiber source configuration point := by
  constructor
  · intro sectionZero point
    exact congrFun sectionZero point
  · intro pointwiseZero
    funext point
    exact pointwiseZero point

end

end SaturationMonoid.PhysicsCore.StageNineJointShellResidualCarrier
