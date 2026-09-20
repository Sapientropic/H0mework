import H0mework.Physics.CoframeJets.CoframeFirstJet

/-!
# Stage-9 dependency-light coframe second-jet carrier

This module declares the complete holonomic second-jet domain of a primitive
coframe field.  A jet is a continuous bilinear map in two base directions,
restricted only by the Schwarz symmetry forced by holonomicity.

The canonical realization is the homogeneous quadratic germ

`q_H(x) = (1 / 2) • H x x`.

The factor `1 / 2` is fixed by exact Hessian recovery.  Adding this germ to
the existing affine realization preserves the supplied origin value and
complete first jet while installing exactly the supplied symmetric Hessian.

No field equation, residual, target, solution witness, inverse, branch, or
choice enters this carrier.
-/

namespace SaturationMonoid.PhysicsCore.StageNineCoframeHolonomicSecondJetCarrier

open ProofFreeRicherAnholonomicSource
open StageNineCoframeFirstJet
open StageNineHolonomicField
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false

/-! ## Symmetric second-jet domain -/

/-- Ambient continuous coframe Hessians.  The first two slots are base
derivative directions and the output is a complete coframe variation. -/
abbrev CoframeSecondJetAmbient :=
  BasePoint →L[ℝ] BasePoint →L[ℝ] LorentzianCoframe

/-- Schwarz-symmetric Hessians of an actual holonomic coframe germ. -/
def coframeHolonomicSecondJetSubmodule :
    Submodule ℝ CoframeSecondJetAmbient where
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

abbrev CoframeHolonomicSecondJet :=
  coframeHolonomicSecondJetSubmodule

theorem coframeHolonomicSecondJet_symmetric
    (jet : CoframeHolonomicSecondJet)
    (first second : BasePoint) :
    jet.1 first second = jet.1 second first :=
  jet.2 first second

/-! ## Canonical homogeneous-quadratic realization -/

/-- The canonical quadratic realization.  Its normalization is fixed by the
Hessian recovery theorem below. -/
def coframeHolonomicSecondJetQuadraticRealization :
    CoframeHolonomicSecondJet →ₗ[ℝ]
      (BasePoint → LorentzianCoframe) where
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

@[simp] theorem coframeHolonomicSecondJetQuadraticRealization_apply
    (jet : CoframeHolonomicSecondJet) (point : BasePoint) :
    coframeHolonomicSecondJetQuadraticRealization jet point =
      (1 / 2 : ℝ) • jet.1 point point :=
  rfl

theorem coframeHolonomicSecondJetQuadraticRealization_hasFDerivAt
    (jet : CoframeHolonomicSecondJet) (point : BasePoint) :
    HasFDerivAt (coframeHolonomicSecondJetQuadraticRealization jet)
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
    rw [coframeHolonomicSecondJet_symmetric jet direction point]
    module
  change HasFDerivAt (fun candidate =>
    (1 / 2 : ℝ) • jet.1 candidate candidate) (jet.1 point) point
  rw [← derivativeEquality]
  exact scaledDerivative

theorem coframeHolonomicSecondJetQuadraticRealization_contDiff
    (jet : CoframeHolonomicSecondJet) :
    ContDiff ℝ ∞ (coframeHolonomicSecondJetQuadraticRealization jet) := by
  have quadraticSmooth : ContDiff ℝ ∞ fun point : BasePoint =>
      jet.1 point point :=
    jet.1.contDiff.clm_apply contDiff_id
  change ContDiff ℝ ∞ fun point : BasePoint =>
    (1 / 2 : ℝ) • jet.1 point point
  exact
    (contDiff_const : ContDiff ℝ ∞ fun _ : BasePoint => (1 / 2 : ℝ)).smul
      quadraticSmooth

@[simp] theorem coframeHolonomicSecondJetQuadraticRealization_origin
    (jet : CoframeHolonomicSecondJet) :
    coframeHolonomicSecondJetQuadraticRealization jet 0 = 0 := by
  simp

theorem coframeHolonomicSecondJetQuadraticRealization_firstJet_origin
    (jet : CoframeHolonomicSecondJet)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (coframeHolonomicSecondJetQuadraticRealization jet) 0 direction = 0 := by
  unfold fieldDirectionalDerivative
  have derivativeEquality :=
    (coframeHolonomicSecondJetQuadraticRealization_hasFDerivAt jet 0).fderiv
  calc
    _ = jet.1 0 (coordinateDirection direction) :=
      congrArg (fun derivative => derivative (coordinateDirection direction))
        derivativeEquality
    _ = 0 := by simp

/-- The raw second Fréchet readout of a coframe variation at the origin. -/
def coframeOriginSecondFrechetJet
    (variation : BasePoint → LorentzianCoframe) :
    CoframeSecondJetAmbient :=
  fderiv ℝ (fderiv ℝ variation) 0

/-- Exact Hessian recovery pins the quadratic normalization and makes the
second-jet carrier faithful. -/
theorem coframeHolonomicSecondJetQuadraticRealization_secondJet
    (jet : CoframeHolonomicSecondJet) :
    coframeOriginSecondFrechetJet
        (coframeHolonomicSecondJetQuadraticRealization jet) = jet.1 := by
  unfold coframeOriginSecondFrechetJet
  have firstDerivative :
      fderiv ℝ (coframeHolonomicSecondJetQuadraticRealization jet) =
        (jet.1 : BasePoint → BasePoint →L[ℝ] LorentzianCoframe) := by
    funext point
    exact (coframeHolonomicSecondJetQuadraticRealization_hasFDerivAt
      jet point).fderiv
  rw [firstDerivative]
  exact jet.1.hasFDerivAt.fderiv

theorem coframeHolonomicSecondJetQuadraticRealization_injective :
    Function.Injective coframeHolonomicSecondJetQuadraticRealization := by
  intro first second realizationEquality
  apply Subtype.ext
  have secondJetEquality := congrArg coframeOriginSecondFrechetJet
    realizationEquality
  simpa only [coframeHolonomicSecondJetQuadraticRealization_secondJet] using
    secondJetEquality

/-! ## Exact first-plus-second jet realization -/

/-- The complete affine derivative as one continuous coframe-valued linear
map.  This is only a packaging of the already-declared first-jet coordinates. -/
def coframeJetAffineLinear
    (jet : PointwiseLorentzianCoframeJet) :
    BasePoint →L[ℝ] LorentzianCoframe :=
  ContinuousLinearMap.pi fun internal =>
    ContinuousLinearMap.pi fun coordinate =>
      coframeJetAffineComponentLinear jet internal coordinate

@[simp] theorem coframeJetAffineLinear_apply
    (jet : PointwiseLorentzianCoframeJet)
    (point : BasePoint) (internal coordinate : LorentzianIndex) :
    coframeJetAffineLinear jet point internal coordinate =
      coframeJetAffineComponentLinear jet internal coordinate point :=
  rfl

theorem affineCoframeFieldOfJet_hasFDerivAt
    (jet : PointwiseLorentzianCoframeJet) (point : BasePoint) :
    HasFDerivAt (affineCoframeFieldOfJet jet)
      (coframeJetAffineLinear jet) point := by
  rw [show affineCoframeFieldOfJet jet = fun candidate =>
      jet.coframe + coframeJetAffineLinear jet candidate by
    funext candidate internal coordinate
    rfl]
  exact (coframeJetAffineLinear jet).hasFDerivAt.const_add jet.coframe

/-- Canonical field realizing a supplied origin value, complete first jet,
and complete symmetric Hessian simultaneously. -/
def coframeFieldOfFirstAndSecondJet
    (firstJet : PointwiseLorentzianCoframeJet)
    (secondJet : CoframeHolonomicSecondJet) :
    BasePoint → LorentzianCoframe :=
  fun point =>
    affineCoframeFieldOfJet firstJet point +
      coframeHolonomicSecondJetQuadraticRealization secondJet point

theorem coframeFieldOfFirstAndSecondJet_hasFDerivAt
    (firstJet : PointwiseLorentzianCoframeJet)
    (secondJet : CoframeHolonomicSecondJet)
    (point : BasePoint) :
    HasFDerivAt (coframeFieldOfFirstAndSecondJet firstJet secondJet)
      (coframeJetAffineLinear firstJet + secondJet.1 point) point := by
  exact
    (affineCoframeFieldOfJet_hasFDerivAt firstJet point).add
      (coframeHolonomicSecondJetQuadraticRealization_hasFDerivAt
        secondJet point)

@[simp] theorem coframeFieldOfFirstAndSecondJet_origin
    (firstJet : PointwiseLorentzianCoframeJet)
    (secondJet : CoframeHolonomicSecondJet) :
    coframeFieldOfFirstAndSecondJet firstJet secondJet 0 =
      firstJet.coframe := by
  simp [coframeFieldOfFirstAndSecondJet]

/-- The affine-plus-quadratic realization reads back the supplied complete
first jet at the origin. -/
theorem holonomicCoframeFirstJetAt_firstAndSecondJet_origin
    (firstJet : PointwiseLorentzianCoframeJet)
    (secondJet : CoframeHolonomicSecondJet) :
    holonomicCoframeFirstJetAt
        (coframeFieldOfFirstAndSecondJet firstJet secondJet) 0 =
      firstJet := by
  apply coframeJet_eq_of_fields_eq
  · exact coframeFieldOfFirstAndSecondJet_origin firstJet secondJet
  · funext derivativeDirection internal coordinate
    let evaluation : LorentzianCoframe →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj coordinate :
          (LorentzianIndex → ℝ) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.proj internal :
          LorentzianCoframe →L[ℝ] (LorentzianIndex → ℝ))
    have componentDerivative : HasFDerivAt
        (fun point =>
          evaluation
            (coframeFieldOfFirstAndSecondJet firstJet secondJet point))
        (evaluation.comp
          (coframeJetAffineLinear firstJet + secondJet.1 0)) 0 := by
      exact evaluation.hasFDerivAt.comp 0
        (coframeFieldOfFirstAndSecondJet_hasFDerivAt
          firstJet secondJet 0)
    unfold holonomicCoframeFirstJetAt
    change
      fderiv ℝ
          (fun point =>
            evaluation
              (coframeFieldOfFirstAndSecondJet firstJet secondJet point))
          0 (coordinateDirection derivativeDirection) =
        firstJet.derivative derivativeDirection internal coordinate
    rw [componentDerivative.fderiv]
    simp only [ContinuousLinearMap.comp_apply, map_zero, add_zero]
    change
      coframeJetAffineComponentLinear firstJet internal coordinate
          (coordinateDirection derivativeDirection) =
        firstJet.derivative derivativeDirection internal coordinate
    exact coframeJetAffineComponentLinear_coordinateDirection
      firstJet derivativeDirection internal coordinate

/-- Subtracting the retained affine first-jet field recovers exactly the
canonical quadratic increment.  This states the second-jet write without
requiring an additional operator-norm topology on the matrix-valued first
Fréchet derivative. -/
theorem coframeFieldOfFirstAndSecondJet_quadraticIncrement
    (firstJet : PointwiseLorentzianCoframeJet)
    (secondJet : CoframeHolonomicSecondJet) :
    (fun point =>
      coframeFieldOfFirstAndSecondJet firstJet secondJet point -
        affineCoframeFieldOfJet firstJet point) =
      coframeHolonomicSecondJetQuadraticRealization secondJet := by
  funext point
  simp [coframeFieldOfFirstAndSecondJet]

/-- Exact second-jet recovery of the installed nonlinear increment.  The
affine origin value and first jet have already been read back above. -/
theorem coframeFieldOfFirstAndSecondJet_quadraticIncrement_secondJet
    (firstJet : PointwiseLorentzianCoframeJet)
    (secondJet : CoframeHolonomicSecondJet) :
    coframeOriginSecondFrechetJet
        (fun point =>
          coframeFieldOfFirstAndSecondJet firstJet secondJet point -
            affineCoframeFieldOfJet firstJet point) =
      secondJet.1 := by
  rw [coframeFieldOfFirstAndSecondJet_quadraticIncrement]
  exact coframeHolonomicSecondJetQuadraticRealization_secondJet secondJet

end

end SaturationMonoid.PhysicsCore.StageNineCoframeHolonomicSecondJetCarrier
