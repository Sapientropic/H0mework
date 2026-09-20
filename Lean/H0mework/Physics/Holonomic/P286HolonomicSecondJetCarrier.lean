import H0mework.Physics.GaugeAction.P286Bianchi
import H0mework.Physics.ConnectionJets.P286ColorCartanQuadraticConnectionJet

/-!
# S9-C3h82a: holonomic P286 connection second-jet carrier

C3h81b derives a source-coadjoint responsibility submodule on the residual
side.  Before asking whether that responsibility is reachable, this module
declares the complete local second-jet domain already owned by the primitive
P286 connection.  A jet is a continuous bilinear map in two base directions,
restricted only by the Schwarz symmetry forced by holonomicity.

The canonical realization is the homogeneous quadratic germ

`eta_H(x) = (1 / 2) • H x x`.

The factor `1 / 2` is fixed by exact Hessian recovery; it is not a coupling,
source value, ansatz knob, branch, or receipt.  The realization has zero value
and first jet at the origin, preserves the background origin curvature, and
remains an actual primitive connection, so the existing off-shell P286
Bianchi theorem applies.  This module does not define an Euler--Lagrange
response, range lift, repair selector, source slot, or stationary producer.
-/

namespace SaturationMonoid.PhysicsCore.StageNineP286HolonomicSecondJetCarrier

open ProofFreeRicherAnholonomicSource
open StageNineHolonomicField
open StageNineP286Bianchi
open StageNineP286ColorCartanQuadraticConnectionJet
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286SourceAffineCurvatureJetNormalForm
open StageNineSourceGeneratedP286AffineConnectionGerm
open SU7MotherLieAlgebra
open scoped ContDiff

noncomputable section

set_option autoImplicit false

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance p286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

/-! ## Symmetric second-jet domain -/

/-- Ambient continuous connection Hessians.  The first two slots are base
derivative directions; the output is the existing P286 connection one-form. -/
abbrev P286ConnectionSecondJetAmbient :=
  BasePoint →L[ℝ] BasePoint →L[ℝ] P286GaugeOneForm

/-- Schwarz-symmetric Hessians of an actual holonomic connection germ. -/
def p286HolonomicConnectionSecondJetSubmodule :
    Submodule ℝ P286ConnectionSecondJetAmbient where
  carrier := { jet | ∀ first second, jet first second = jet second first }
  zero_mem' := by
    intro first second
    rfl
  add_mem' := by
    intro first second firstSymmetric secondSymmetric outer inner
    simp only [add_apply]
    rw [firstSymmetric outer inner, secondSymmetric outer inner]
  smul_mem' := by
    intro parameter jet symmetric outer inner
    simp only [smul_apply]
    rw [symmetric outer inner]

abbrev P286HolonomicConnectionSecondJet :=
  p286HolonomicConnectionSecondJetSubmodule

theorem p286HolonomicConnectionSecondJet_symmetric
    (jet : P286HolonomicConnectionSecondJet)
    (first second : BasePoint) :
    jet.1 first second = jet.1 second first :=
  jet.2 first second

/-! ## Canonical homogeneous-quadratic realization -/

/-- The only realization used by this carrier.  Its normalization is fixed by
the Hessian recovery theorem below. -/
def p286HolonomicSecondJetQuadraticRealization :
    P286HolonomicConnectionSecondJet →ₗ[ℝ]
      (BasePoint → P286GaugeOneForm) where
  toFun jet point := (1 / 2 : ℝ) • jet.1 point point
  map_add' := by
    intro first second
    funext point
    change
      (1 / 2 : ℝ) • ((first.1 + second.1) point point) =
        (1 / 2 : ℝ) • first.1 point point +
          (1 / 2 : ℝ) • second.1 point point
    simp only [add_apply]
    module
  map_smul' := by
    intro parameter jet
    funext point
    change
      (1 / 2 : ℝ) • ((parameter • jet.1) point point) =
        parameter • ((1 / 2 : ℝ) • jet.1 point point)
    simp only [smul_apply]
    module

@[simp] theorem p286HolonomicSecondJetQuadraticRealization_apply
    (jet : P286HolonomicConnectionSecondJet) (point : BasePoint) :
    p286HolonomicSecondJetQuadraticRealization jet point =
      (1 / 2 : ℝ) • jet.1 point point :=
  rfl

theorem p286HolonomicSecondJetQuadraticRealization_hasFDerivAt
    (jet : P286HolonomicConnectionSecondJet) (point : BasePoint) :
    HasFDerivAt (p286HolonomicSecondJetQuadraticRealization jet)
      (jet.1 point) point := by
  have rawDerivative :=
    jet.1.hasFDerivAt_of_bilinear
      (hasFDerivAt_id (x := point))
      (hasFDerivAt_id (x := point))
  have scaledDerivative := rawDerivative.const_smul (1 / 2 : ℝ)
  have derivativeEquality :
      (1 / 2 : ℝ) •
          (jet.1.precompR BasePoint point
              (ContinuousLinearMap.id ℝ BasePoint) +
            jet.1.precompL BasePoint
              (ContinuousLinearMap.id ℝ BasePoint) point) =
        jet.1 point := by
    apply ContinuousLinearMap.ext
    intro direction
    change
      (1 / 2 : ℝ) • (jet.1 point direction + jet.1 direction point) =
        jet.1 point direction
    rw [p286HolonomicConnectionSecondJet_symmetric jet direction point]
    module
  change HasFDerivAt (fun candidate =>
    (1 / 2 : ℝ) • jet.1 candidate candidate) (jet.1 point) point
  rw [← derivativeEquality]
  exact scaledDerivative

theorem p286HolonomicSecondJetQuadraticRealization_contDiff
    (jet : P286HolonomicConnectionSecondJet) :
    ContDiff ℝ ∞ (p286HolonomicSecondJetQuadraticRealization jet) := by
  have quadraticSmooth : ContDiff ℝ ∞ fun point : BasePoint =>
      jet.1 point point :=
    jet.1.contDiff.clm_apply contDiff_id
  change ContDiff ℝ ∞ fun point : BasePoint =>
    (1 / 2 : ℝ) • jet.1 point point
  exact
    (contDiff_const : ContDiff ℝ ∞ fun _ : BasePoint => (1 / 2 : ℝ)).smul
      quadraticSmooth

@[simp] theorem p286HolonomicSecondJetQuadraticRealization_origin
    (jet : P286HolonomicConnectionSecondJet) :
    p286HolonomicSecondJetQuadraticRealization jet 0 = 0 := by
  simp

theorem p286HolonomicSecondJetQuadraticRealization_firstJet_origin
    (jet : P286HolonomicConnectionSecondJet)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (p286HolonomicSecondJetQuadraticRealization jet) 0 direction = 0 := by
  unfold fieldDirectionalDerivative
  rw [(p286HolonomicSecondJetQuadraticRealization_hasFDerivAt jet 0).fderiv]
  simp

theorem p286HolonomicSecondJetQuadraticRealization_variationDerivative_origin
    (jet : P286HolonomicConnectionSecondJet)
    (derivativeDirection formDirection : LorentzianIndex) :
    p286GaugeVariationCoordinateDerivative
        (p286HolonomicSecondJetQuadraticRealization jet) 0
        derivativeDirection formDirection = 0 := by
  let evaluation : P286GaugeOneForm →L[ℝ] P286CoordinateCarrier :=
    ContinuousLinearMap.proj formDirection
  have componentDerivative : HasFDerivAt
      (fun point =>
        evaluation (p286HolonomicSecondJetQuadraticRealization jet point))
      (evaluation.comp (jet.1 0)) 0 := by
    exact evaluation.hasFDerivAt.comp 0
      (p286HolonomicSecondJetQuadraticRealization_hasFDerivAt jet 0)
  unfold p286GaugeVariationCoordinateDerivative fieldDirectionalDerivative
  change
    fderiv ℝ
        (fun point =>
          evaluation (p286HolonomicSecondJetQuadraticRealization jet point))
        0 (coordinateDirection derivativeDirection) = 0
  rw [componentDerivative.fderiv]
  simp [evaluation]

/-- The raw second Fréchet readout of a connection variation at the origin. -/
def p286OriginConnectionSecondFrechetJet
    (variation : BasePoint → P286GaugeOneForm) :
    P286ConnectionSecondJetAmbient :=
  fderiv ℝ (fderiv ℝ variation) 0

/-- Exact Hessian recovery.  This pins the quadratic normalization and makes
the ambient second-jet carrier faithful. -/
theorem p286HolonomicSecondJetQuadraticRealization_secondJet
    (jet : P286HolonomicConnectionSecondJet) :
    p286OriginConnectionSecondFrechetJet
        (p286HolonomicSecondJetQuadraticRealization jet) = jet.1 := by
  unfold p286OriginConnectionSecondFrechetJet
  have firstDerivative :
      fderiv ℝ (p286HolonomicSecondJetQuadraticRealization jet) =
        (jet.1 : BasePoint → BasePoint →L[ℝ] P286GaugeOneForm) := by
    funext point
    exact (p286HolonomicSecondJetQuadraticRealization_hasFDerivAt
      jet point).fderiv
  rw [firstDerivative]
  exact jet.1.hasFDerivAt.fderiv

theorem p286HolonomicSecondJetQuadraticRealization_injective :
    Function.Injective p286HolonomicSecondJetQuadraticRealization := by
  intro first second realizationEquality
  apply Subtype.ext
  have secondJetEquality := congrArg p286OriginConnectionSecondFrechetJet
    realizationEquality
  simpa only [p286HolonomicSecondJetQuadraticRealization_secondJet] using
    secondJetEquality

/-! ## C3h78 positive regression -/

/-- Unit one-form direction underlying the old C3h78 color-Cartan jet. -/
def colorCartanQuadraticUnitOneForm : P286GaugeOneForm :=
  fun formDirection =>
    if formDirection = 0 then colorCartanQuadraticCoordinate else 0

/-- The Hessian of `x₁²` is `2 dx₁ ⊗ dx₁`.  This is a carrier coordinate,
not a physical coefficient or source parameter. -/
def colorCartanQuadraticSecondJetAmbient :
    P286ConnectionSecondJetAmbient :=
  (2 : ℝ) •
    (p286BaseCoordinate 1).smulRight
      ((p286BaseCoordinate 1).smulRight
        colorCartanQuadraticUnitOneForm)

theorem colorCartanQuadraticSecondJetAmbient_symmetric
    (first second : BasePoint) :
    colorCartanQuadraticSecondJetAmbient first second =
      colorCartanQuadraticSecondJetAmbient second first := by
  unfold colorCartanQuadraticSecondJetAmbient
  simp only [smul_apply, ContinuousLinearMap.smulRight_apply,
    p286BaseCoordinate_apply]
  module

def colorCartanQuadraticHolonomicSecondJet :
    P286HolonomicConnectionSecondJet :=
  ⟨colorCartanQuadraticSecondJetAmbient,
    colorCartanQuadraticSecondJetAmbient_symmetric⟩

/-- The general carrier recovers the already validated C3h78 germ exactly. -/
theorem colorCartanQuadraticHolonomicSecondJet_realizes_C3h78 :
    p286HolonomicSecondJetQuadraticRealization
        colorCartanQuadraticHolonomicSecondJet =
      colorCartanQuadraticJet := by
  funext point formDirection
  by_cases directionZero : formDirection = 0
  · subst formDirection
    simp [colorCartanQuadraticHolonomicSecondJet,
      colorCartanQuadraticSecondJetAmbient,
      colorCartanQuadraticUnitOneForm, colorCartanQuadraticJet,
      colorCartanQuadraticCoefficient,
      ContinuousLinearMap.smulRight_apply, p286BaseCoordinate_apply]
    module
  · simp [colorCartanQuadraticHolonomicSecondJet,
      colorCartanQuadraticSecondJetAmbient,
      colorCartanQuadraticUnitOneForm, colorCartanQuadraticJet,
      directionZero, ContinuousLinearMap.smulRight_apply,
      p286BaseCoordinate_apply]

/-! ## Installation into the actual primitive connection -/

/-- Install one classified Hessian into the existing primitive P286
connection.  The real parameter is retained only for later affine response
classification. -/
def installP286HolonomicConnectionSecondJet
    (configuration : StageNineHolonomicConfiguration)
    (jet : P286HolonomicConnectionSecondJet) (parameter : ℝ) :
    StageNineHolonomicConfiguration :=
  varyP286GaugeConnectionCoordinate configuration
    (p286HolonomicSecondJetQuadraticRealization jet) parameter

theorem installP286HolonomicConnectionSecondJet_smooth
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (jet : P286HolonomicConnectionSecondJet) (parameter : ℝ) :
    (installP286HolonomicConnectionSecondJet configuration jet
      parameter).Smooth := by
  exact varyP286GaugeConnectionCoordinate_smooth_of_contDiff configuration
    smooth (p286HolonomicSecondJetQuadraticRealization jet)
      (p286HolonomicSecondJetQuadraticRealization_contDiff jet) parameter

theorem installP286HolonomicConnectionSecondJet_connection_origin
    (configuration : StageNineHolonomicConfiguration)
    (jet : P286HolonomicConnectionSecondJet) (parameter : ℝ) :
    holonomicP286GaugeConnectionCoordinate
        (installP286HolonomicConnectionSecondJet configuration jet parameter)
        0 =
      holonomicP286GaugeConnectionCoordinate configuration 0 := by
  rw [installP286HolonomicConnectionSecondJet,
    holonomicP286GaugeConnectionCoordinate_vary]
  simp

theorem installP286HolonomicConnectionSecondJet_firstJet_origin
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (jet : P286HolonomicConnectionSecondJet) (parameter : ℝ)
    (derivativeDirection formDirection : LorentzianIndex) :
    p286GaugeConnectionCoordinateDerivative
        (installP286HolonomicConnectionSecondJet configuration jet parameter)
        0 derivativeDirection formDirection =
      p286GaugeConnectionCoordinateDerivative configuration 0
        derivativeDirection formDirection := by
  rw [installP286HolonomicConnectionSecondJet,
    p286GaugeConnectionCoordinateDerivative_vary_of_contDiff configuration
      smooth (p286HolonomicSecondJetQuadraticRealization jet)
      (p286HolonomicSecondJetQuadraticRealization_contDiff jet)]
  rw [p286HolonomicSecondJetQuadraticRealization_variationDerivative_origin]
  simp

theorem p286HolonomicSecondJetLinearCurvatureVariation_origin
    (configuration : StageNineHolonomicConfiguration)
    (jet : P286HolonomicConnectionSecondJet) :
    p286GaugeConnectionLinearCurvatureVariation configuration
        (p286HolonomicSecondJetQuadraticRealization jet) 0 = 0 := by
  funext pair
  simp [p286GaugeConnectionLinearCurvatureVariation,
    p286HolonomicSecondJetQuadraticRealization_variationDerivative_origin]

theorem p286HolonomicSecondJetQuadraticCurvatureVariation_origin
    (jet : P286HolonomicConnectionSecondJet) :
    p286GaugeConnectionQuadraticCurvatureVariation
        (p286HolonomicSecondJetQuadraticRealization jet) 0 = 0 := by
  funext pair
  simp [p286GaugeConnectionQuadraticCurvatureVariation]

theorem installP286HolonomicConnectionSecondJet_curvature_origin
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (jet : P286HolonomicConnectionSecondJet) (parameter : ℝ) :
    holonomicP286GaugeCurvatureCoordinate
        (installP286HolonomicConnectionSecondJet configuration jet parameter)
        0 =
      holonomicP286GaugeCurvatureCoordinate configuration 0 := by
  rw [installP286HolonomicConnectionSecondJet,
    holonomicP286GaugeCurvatureCoordinate_expansion_of_contDiff configuration
      smooth (p286HolonomicSecondJetQuadraticRealization jet)
      (p286HolonomicSecondJetQuadraticRealization_contDiff jet)]
  rw [p286HolonomicSecondJetLinearCurvatureVariation_origin,
    p286HolonomicSecondJetQuadraticCurvatureVariation_origin]
  simp

/-- Every installed Hessian remains in the actual primitive-connection
calculus, so its curvature satisfies the existing off-shell Bianchi identity. -/
theorem installP286HolonomicConnectionSecondJet_bianchi
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (jet : P286HolonomicConnectionSecondJet) (parameter : ℝ)
    (point : BasePoint) (first second third : LorentzianIndex) :
    covariantCurvatureDerivative
          (installP286HolonomicConnectionSecondJet configuration jet parameter)
          point first second third +
        covariantCurvatureDerivative
          (installP286HolonomicConnectionSecondJet configuration jet parameter)
          point second third first +
        covariantCurvatureDerivative
          (installP286HolonomicConnectionSecondJet configuration jet parameter)
          point third first second = 0 := by
  exact holonomicP286GaugeCurvature_bianchi
    (installP286HolonomicConnectionSecondJet configuration jet parameter)
    (installP286HolonomicConnectionSecondJet_smooth configuration smooth jet
      parameter)
    point first second third

end

end SaturationMonoid.PhysicsCore.StageNineP286HolonomicSecondJetCarrier
