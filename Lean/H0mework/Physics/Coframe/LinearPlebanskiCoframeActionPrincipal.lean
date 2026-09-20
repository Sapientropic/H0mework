import H0mework.Physics.Coframe.CoframeSectorStress
import H0mework.Physics.Cartan.CartanTangentSimplicityResponse

/-!
# S9-C3h150: linear Plebanski coframe action principal

The historical squared simplicity density has zero first coframe response on
its own shell.  The existing Plebanski action grammar instead uses the linear
constraint

`⟨λ, ⋆(B - II⁺(e))⟩`.

This module computes that actual finite-dimensional coframe principal at the
identity coframe.  For a coframe stress covector `T`, the four-dimensional
trace reversal

`k = (1 / 2) Tᵀ - (1 / 6) tr(T) I`

canonically generates the multiplier `λ = ⋆ᵢ D II⁺(I)[k]`.  The resulting
linear Plebanski path derivative is exactly `-T` in every coframe direction.

The construction accepts neither a residual nor a principal inverse, target
endpoint, range witness, branch receipt, coefficient, or source parameter.
It is an action-owned algebraic mechanism; the next producer may apply it to
stress read from an already generated actual configuration.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineLinearPlebanskiCoframeActionPrincipal

open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineCartanTangentSimplicityResponse
open StageNineGlobalIntegratedAction

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

/-! ## Finite coframe basis and trace reversal -/

/-- Coordinate basis of the real `4 × 4` coframe carrier. -/
def coframeCoordinateDirection
    (row column : Fin 4) : LorentzianCoframe :=
  Matrix.single row column (1 : ℝ)

/-- Four-dimensional trace reversal forced by the linear Plebanski
coframe principal. -/
def linearPlebanskiTraceReverse
    (stressCoordinates : LorentzianCoframe) : LorentzianCoframe :=
  Matrix.of fun row column =>
    (1 / 2 : ℝ) * stressCoordinates column row -
      (1 / 6 * ∑ index : LorentzianIndex,
        stressCoordinates index index) * (1 : LorentzianCoframe) row column

/-- The simplicity multiplier generated from one coframe response. -/
def linearPlebanskiMultiplierOfCoframeResponse
    (coframeResponse : LorentzianCoframe) : PhysicalBivector :=
  internalBivectorDual
    (physicalIIPlusCoframeTangent
      (1 : LorentzianCoframe) coframeResponse)

/-- Spacetime Hodge operator at the identity coframe, applied independently
in every internal bivector coordinate. -/
def identityCoframeSpacetimeHodge
    (bivector : PhysicalBivector) : PhysicalBivector :=
  fun internalPair => lorentzianCoframeHodge (bivector internalPair)

/-! ## Actual action principal -/

/-- The coframe principal read directly from the linear Plebanski density. -/
def linearPlebanskiCoframePrincipalValue
    (coframeResponse variation : LorentzianCoframe) : ℝ :=
  -gravityCoordinatePairing
    (linearPlebanskiMultiplierOfCoframeResponse coframeResponse)
    (identityCoframeSpacetimeHodge
      (physicalIIPlusCoframeTangent
        (1 : LorentzianCoframe) variation))

/-- Explicit finite-coordinate form of the same principal. -/
def linearPlebanskiCoframePrincipalLinear
    (response : LorentzianCoframe) :
    LorentzianCoframe →ₗ[ℝ] ℝ where
  toFun := fun variation =>
    ∑ row : Fin 4, ∑ column : Fin 4,
      (-2 * (response column row -
        (if row = column then Matrix.trace response else 0))) *
          variation row column
  map_add' := by
    intro first second
    simp only [Matrix.add_apply]
    simp_rw [mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro scalar variation
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro row _
    apply Finset.sum_congr rfl
    intro column _
    ring

/-- Continuous-linear coframe principal used by the stress interface. -/
def linearPlebanskiCoframePrincipal
    (response : LorentzianCoframe) :
    LorentzianCoframe →L[ℝ] ℝ :=
  (linearPlebanskiCoframePrincipalLinear response).toContinuousLinearMap

theorem linearPlebanskiCoframePrincipalValue_eq_principal
    (response variation : LorentzianCoframe) :
    linearPlebanskiCoframePrincipalValue response variation =
      linearPlebanskiCoframePrincipal response variation := by
  simp [linearPlebanskiCoframePrincipalValue,
    linearPlebanskiMultiplierOfCoframeResponse,
    identityCoframeSpacetimeHodge,
    linearPlebanskiCoframePrincipal,
    linearPlebanskiCoframePrincipalLinear,
    gravityCoordinatePairing, physicalIIPlusCoframeTangent,
    coframeWedgeTangent, internalBivectorDual,
    lorentzianCoframeHodge, lorentzianTwoFormSign,
    minkowskiInternalSign, pairFirst, pairSecond, Matrix.trace,
    Matrix.one_apply, Fin.sum_univ_six, Fin.sum_univ_four]
  ring

theorem linearPlebanskiCoframePrincipal_coordinateDirection
    (response : LorentzianCoframe)
    (row column : Fin 4) :
    linearPlebanskiCoframePrincipal response
        (coframeCoordinateDirection row column) =
      -2 * (response column row -
        (if row = column then Matrix.trace response else 0)) := by
  fin_cases row <;> fin_cases column <;>
    simp [linearPlebanskiCoframePrincipal,
      linearPlebanskiCoframePrincipalLinear,
      coframeCoordinateDirection, Matrix.trace, Fin.sum_univ_four]

theorem linearPlebanskiTraceReverse_normalizes_coordinateDirection
    (stressCoordinates : LorentzianCoframe)
    (row column : Fin 4) :
    linearPlebanskiCoframePrincipal
        (linearPlebanskiTraceReverse stressCoordinates)
        (coframeCoordinateDirection row column) =
      -stressCoordinates row column := by
  rw [linearPlebanskiCoframePrincipal_coordinateDirection]
  fin_cases row <;> fin_cases column <;>
    simp [linearPlebanskiTraceReverse, Matrix.trace,
      Fin.sum_univ_four] <;>
    ring

theorem coframe_eq_sum_coordinateDirections
    (coframe : LorentzianCoframe) :
    coframe =
      ∑ row : Fin 4, ∑ column : Fin 4,
        coframe row column • coframeCoordinateDirection row column := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [coframeCoordinateDirection, Fin.sum_univ_four]

theorem coframeCovector_eq_iff_coordinateDirections
    (first second : LorentzianCoframe →L[ℝ] ℝ) :
    first = second ↔
      ∀ row column,
        first (coframeCoordinateDirection row column) =
          second (coframeCoordinateDirection row column) := by
  constructor
  · intro equality row column
    rw [equality]
  · intro coordinateEquality
    ext coframe
    rw [coframe_eq_sum_coordinateDirections coframe]
    simp only [map_sum, map_smul]
    simp_rw [coordinateEquality]

/-- Faithful `4 × 4` coordinates of a coframe covector. -/
def coframeCovectorCoordinates
    (stress : LorentzianCoframe →L[ℝ] ℝ) : LorentzianCoframe :=
  Matrix.of fun row column =>
    stress (coframeCoordinateDirection row column)

/-- Canonical response generated from a complete coframe stress covector. -/
def linearPlebanskiCoframeResponseOfStress
    (stress : LorentzianCoframe →L[ℝ] ℝ) : LorentzianCoframe :=
  linearPlebanskiTraceReverse (coframeCovectorCoordinates stress)

/-- Full-covector normalization: the generated multiplier principal is
exactly the negative of the supplied action stress. -/
theorem linearPlebanskiCoframePrincipal_response_eq_neg
    (stress : LorentzianCoframe →L[ℝ] ℝ) :
    linearPlebanskiCoframePrincipal
        (linearPlebanskiCoframeResponseOfStress stress) =
      -stress := by
  apply (coframeCovector_eq_iff_coordinateDirections _ _).2
  intro row column
  rw [show
      linearPlebanskiCoframeResponseOfStress stress =
        linearPlebanskiTraceReverse
          (coframeCovectorCoordinates stress) by
      rfl,
    linearPlebanskiTraceReverse_normalizes_coordinateDirection]
  simp [coframeCovectorCoordinates]

/-! ## Exact action-path derivative -/

/-- Identity-coordinate form of the existing linear Plebanski simplicity
density. -/
def linearPlebanskiSimplicityDensity
    (auxiliary multiplier : PhysicalBivector)
    (coframe : LorentzianCoframe) : ℝ :=
  gravityCoordinatePairing multiplier
    (identityCoframeSpacetimeHodge
      (auxiliary - physicalIIPlusBivector coframe))

def linearPlebanskiCoframeQuadraticRemainder
    (response variation : LorentzianCoframe) : ℝ :=
  -gravityCoordinatePairing
    (linearPlebanskiMultiplierOfCoframeResponse response)
    (identityCoframeSpacetimeHodge
      (physicalIIPlusBivector variation))

theorem physicalIIPlus_affine_path
    (parameter : ℝ)
    (variation : LorentzianCoframe) :
    physicalIIPlusBivector
        ((1 : LorentzianCoframe) + parameter • variation) =
      physicalIIPlusBivector (1 : LorentzianCoframe) +
        parameter •
          physicalIIPlusCoframeTangent
            (1 : LorentzianCoframe) variation +
        parameter ^ 2 • physicalIIPlusBivector variation := by
  funext internalPair spacetimePair
  fin_cases internalPair <;> fin_cases spacetimePair <;>
    simp [physicalIIPlusBivector, physicalIIPlusCoframeTangent,
      coframeWedgeTangent, coframeWedge, internalBivectorDual,
      lorentzianCoframeHodge, pairFirst, pairSecond,
      Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply] <;>
    ring

theorem linearPlebanskiSimplicityDensity_path_expansion
    (response variation : LorentzianCoframe)
    (parameter : ℝ) :
    linearPlebanskiSimplicityDensity
        (physicalIIPlusBivector (1 : LorentzianCoframe))
        (linearPlebanskiMultiplierOfCoframeResponse response)
        ((1 : LorentzianCoframe) + parameter • variation) =
      linearPlebanskiCoframePrincipalValue response variation *
          parameter +
        linearPlebanskiCoframeQuadraticRemainder response variation *
          parameter ^ 2 := by
  rw [linearPlebanskiSimplicityDensity,
    physicalIIPlus_affine_path]
  simp [linearPlebanskiCoframePrincipalValue,
    linearPlebanskiCoframeQuadraticRemainder,
    gravityCoordinatePairing, identityCoframeSpacetimeHodge,
    Fin.sum_univ_six]
  ring

/-- Actual derivative of the linear Plebanski density along every coframe
direction.  The density is differentiated after the multiplier has been
generated, not used to select the response. -/
theorem linearPlebanskiSimplicityDensity_path_hasDerivAt
    (response variation : LorentzianCoframe) :
    HasDerivAt
      (fun parameter : ℝ =>
        linearPlebanskiSimplicityDensity
          (physicalIIPlusBivector (1 : LorentzianCoframe))
          (linearPlebanskiMultiplierOfCoframeResponse response)
          ((1 : LorentzianCoframe) + parameter • variation))
      (linearPlebanskiCoframePrincipalValue response variation)
      0 := by
  have identityDerivative := hasDerivAt_id (x := (0 : ℝ))
  have polynomial :=
    (identityDerivative.const_mul
      (linearPlebanskiCoframePrincipalValue response variation)).add
    ((identityDerivative.pow 2).const_mul
      (linearPlebanskiCoframeQuadraticRemainder response variation))
  have formulaEventually : Filter.EventuallyEq (nhds (0 : ℝ))
      (fun parameter : ℝ =>
        linearPlebanskiSimplicityDensity
          (physicalIIPlusBivector (1 : LorentzianCoframe))
          (linearPlebanskiMultiplierOfCoframeResponse response)
          ((1 : LorentzianCoframe) + parameter • variation))
      (fun parameter : ℝ =>
        linearPlebanskiCoframePrincipalValue response variation *
            parameter +
          linearPlebanskiCoframeQuadraticRemainder response variation *
            parameter ^ 2) :=
    Filter.Eventually.of_forall
      (linearPlebanskiSimplicityDensity_path_expansion
        response variation)
  have exactDerivative :=
    polynomial.congr_of_eventuallyEq formulaEventually
  simpa using exactDerivative

/-- Applying the action-generated response to any stress covector cancels
that complete stress in every variation direction. -/
theorem linearPlebanskiSimplicityDensity_response_path_hasDerivAt
    (stress : LorentzianCoframe →L[ℝ] ℝ)
    (variation : LorentzianCoframe) :
    HasDerivAt
      (fun parameter : ℝ =>
        linearPlebanskiSimplicityDensity
          (physicalIIPlusBivector (1 : LorentzianCoframe))
          (linearPlebanskiMultiplierOfCoframeResponse
            (linearPlebanskiCoframeResponseOfStress stress))
          ((1 : LorentzianCoframe) + parameter • variation))
      (-stress variation)
      0 := by
  have derivative :=
    linearPlebanskiSimplicityDensity_path_hasDerivAt
      (linearPlebanskiCoframeResponseOfStress stress) variation
  rw [linearPlebanskiCoframePrincipalValue_eq_principal]
    at derivative
  have principalEquality :=
    DFunLike.congr_fun
      (linearPlebanskiCoframePrincipal_response_eq_neg stress)
      variation
  simpa [principalEquality] using derivative

end

end
  SaturationMonoid.PhysicsCore.StageNineLinearPlebanskiCoframeActionPrincipal
