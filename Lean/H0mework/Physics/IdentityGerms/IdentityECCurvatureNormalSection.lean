import H0mework.Physics.Holonomic.HolonomicGravityCurvatureVarianceNormalization
import H0mework.Physics.Coframe.LinearPlebanskiCoframeActionPrincipal
import H0mework.Physics.Geometry.TopologicalFourFormPairing

/-!
# Identity-contact EC curvature normal section for the repaired root

The repaired Dirac-dual form-native action makes the coframe equation linear
in the *actual curvature* while the coframe and the matter fields are held at
one contact.  This module constructs the corresponding normalization-locked
right inverse at the identity coframe.

The historical linear-Plebanski response is used only as a finite-dimensional
coordinate equivalence.  The theorem
`identityDiracDualECPrincipal_eq_linearPlebanski` proves directly that its
coordinate formula is the current metric-free topological pairing, with the
current sign and variance conventions.  No historical action, stationary
actual, field equation, residual value, endpoint, branch, or inverse witness
is imported as physical authority.

For a current raw curvature `F`, the unobserved part is retained as

```text
F_ker = F - S (O F),
```

where `O` is the current EC observation and `S` is the canonical normal
section.  A new observed load is therefore installed by

```text
F_target = F_ker + S q.
```

The final two theorems prove both the requested observation and exact kernel
retention.  Thus the construction transports responsibility carried by the
current curvature instead of silently replacing it by a chosen normal
representative.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECCurvatureNormalSection

open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineCartanTangentSimplicityResponse
open StageNineCoframeTwoFormPairing
open StageNineGlobalIntegratedAction
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineLinearPlebanskiCoframeActionPrincipal
open StageNineTopologicalFourFormPairing

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Current-root EC observation -/

private theorem physicalIIPlusCoframeTangent_add
    (coframe first second : LorentzianCoframe) :
    physicalIIPlusCoframeTangent coframe (first + second) =
      physicalIIPlusCoframeTangent coframe first +
        physicalIIPlusCoframeTangent coframe second := by
  funext internalPair spacetimePair
  fin_cases internalPair <;> fin_cases spacetimePair <;>
    simp [physicalIIPlusCoframeTangent, coframeWedgeTangent,
      internalBivectorDual, lorentzianCoframeHodge,
      pairFirst, pairSecond] <;>
    ring

private theorem physicalIIPlusCoframeTangent_smul
    (coframe variation : LorentzianCoframe) (parameter : ℝ) :
    physicalIIPlusCoframeTangent coframe (parameter • variation) =
      parameter • physicalIIPlusCoframeTangent coframe variation := by
  funext internalPair spacetimePair
  fin_cases internalPair <;> fin_cases spacetimePair <;>
    simp [physicalIIPlusCoframeTangent, coframeWedgeTangent,
      internalBivectorDual, lorentzianCoframeHodge,
      pairFirst, pairSecond] <;>
    ring

/-- Linear coframe covector read from one raw lowered curvature at the
identity coframe.  Variance normalization is applied exactly once before the
metric-free spacetime wedge. -/
def identityDiracDualECCurvatureObservation
    (rawCurvature : PhysicalBivector) :
    LorentzianCoframe →L[ℝ] ℝ :=
  ({ toFun := fun variation =>
      gravityTopologicalWedgeCoefficient
        (physicalIIPlusCoframeTangent (1 : LorentzianCoframe) variation)
        (gravityInternalPairVarianceNormalization rawCurvature)
     map_add' := by
       intro first second
       rw [physicalIIPlusCoframeTangent_add,
         gravityTopologicalWedgeCoefficient_add_left]
     map_smul' := by
       intro parameter variation
       rw [physicalIIPlusCoframeTangent_smul,
         gravityTopologicalWedgeCoefficient_smul_left]
       rfl } : LorentzianCoframe →ₗ[ℝ] ℝ).toContinuousLinearMap

theorem identityDiracDualECCurvatureObservation_add
    (first second : PhysicalBivector) :
    identityDiracDualECCurvatureObservation (first + second) =
      identityDiracDualECCurvatureObservation first +
        identityDiracDualECCurvatureObservation second := by
  apply ContinuousLinearMap.ext
  intro variation
  change
    gravityTopologicalWedgeCoefficient
        (physicalIIPlusCoframeTangent (1 : LorentzianCoframe) variation)
        (gravityInternalPairVarianceNormalization (first + second)) =
      gravityTopologicalWedgeCoefficient
          (physicalIIPlusCoframeTangent (1 : LorentzianCoframe) variation)
          (gravityInternalPairVarianceNormalization first) +
        gravityTopologicalWedgeCoefficient
          (physicalIIPlusCoframeTangent (1 : LorentzianCoframe) variation)
          (gravityInternalPairVarianceNormalization second)
  rw [map_add, gravityTopologicalWedgeCoefficient_add_right]

theorem identityDiracDualECCurvatureObservation_sub
    (first second : PhysicalBivector) :
    identityDiracDualECCurvatureObservation (first - second) =
      identityDiracDualECCurvatureObservation first -
        identityDiracDualECCurvatureObservation second := by
  apply ContinuousLinearMap.ext
  intro variation
  change
    gravityTopologicalWedgeCoefficient
        (physicalIIPlusCoframeTangent (1 : LorentzianCoframe) variation)
        (gravityInternalPairVarianceNormalization (first - second)) =
      gravityTopologicalWedgeCoefficient
          (physicalIIPlusCoframeTangent (1 : LorentzianCoframe) variation)
          (gravityInternalPairVarianceNormalization first) -
        gravityTopologicalWedgeCoefficient
          (physicalIIPlusCoframeTangent (1 : LorentzianCoframe) variation)
          (gravityInternalPairVarianceNormalization second)
  rw [map_sub]
  rw [show
      gravityInternalPairVarianceNormalization first -
          gravityInternalPairVarianceNormalization second =
        gravityInternalPairVarianceNormalization first +
          (-1 : ℝ) •
            gravityInternalPairVarianceNormalization second by
      module]
  rw [gravityTopologicalWedgeCoefficient_add_right,
    gravityTopologicalWedgeCoefficient_smul_right]
  ring

/-! ## Authoritative topological seam and normal section -/

/-- The old sixteen-coordinate principal is exactly the repaired root's
topological EC pairing at the identity contact.  This theorem is the action-
jurisdiction seam: only the representation formula is reused. -/
theorem identityDiracDualECPrincipal_eq_linearPlebanski
    (response variation : LorentzianCoframe) :
    gravityTopologicalWedgeCoefficient
        (physicalIIPlusCoframeTangent (1 : LorentzianCoframe) variation)
        (linearPlebanskiMultiplierOfCoframeResponse response) =
      linearPlebanskiCoframePrincipal response variation := by
  rw [← linearPlebanskiCoframePrincipalValue_eq_principal]
  unfold linearPlebanskiCoframePrincipalValue
  have seam :=
    gravityCoframePairing_one_spacetimeHodge_eq_neg_topological
      (linearPlebanskiMultiplierOfCoframeResponse response)
      (physicalIIPlusCoframeTangent (1 : LorentzianCoframe) variation)
  rw [gravityCoframePairing_one_eq_coordinate,
    gravitySpacetimeHodge_one_eq_fixed] at seam
  change
    gravityCoordinatePairing
        (linearPlebanskiMultiplierOfCoframeResponse response)
        (identityCoframeSpacetimeHodge
          (physicalIIPlusCoframeTangent (1 : LorentzianCoframe) variation)) =
      -gravityTopologicalWedgeCoefficient
        (linearPlebanskiMultiplierOfCoframeResponse response)
        (physicalIIPlusCoframeTangent (1 : LorentzianCoframe) variation)
    at seam
  rw [gravityTopologicalWedgeCoefficient_symmetric]
  linarith

/-- Canonical raw-curvature normal section of the current EC observation.
The input is a coframe covector; no curvature, inverse, representative, or
kernel witness is supplied. -/
def identityDiracDualECCurvatureNormalSection
    (observation : LorentzianCoframe →L[ℝ] ℝ) :
    PhysicalBivector :=
  gravityInternalPairVarianceNormalization
    (linearPlebanskiMultiplierOfCoframeResponse
      (linearPlebanskiCoframeResponseOfStress (-observation)))

/-- Exact `(01,01)` coordinate of the identity-contact EC normal section.
Only the four diagonal coframe-covector coordinates contribute. -/
theorem identityDiracDualECCurvatureNormalSection_zero_zero
    (observation : LorentzianCoframe →L[ℝ] ℝ) :
    identityDiracDualECCurvatureNormalSection observation 0 0 =
      -(observation (coframeCoordinateDirection 0 0) +
          observation (coframeCoordinateDirection 1 1)) / 6 +
        (observation (coframeCoordinateDirection 2 2) +
          observation (coframeCoordinateDirection 3 3)) / 3 := by
  simp [identityDiracDualECCurvatureNormalSection,
    linearPlebanskiCoframeResponseOfStress,
    linearPlebanskiTraceReverse, coframeCovectorCoordinates,
    linearPlebanskiMultiplierOfCoframeResponse,
    gravityInternalPairVarianceNormalization,
    physicalIIPlusCoframeTangent, coframeWedgeTangent,
    internalBivectorDual, lorentzianCoframeHodge,
    lorentzianTwoFormSign,
    coframeCoordinateDirection, pairFirst, pairSecond,
    Matrix.one_apply, Fin.sum_univ_four]
  ring

/-- **Positive normal-section frontier.**  The section is a genuine right
inverse of the repaired root's metric-free EC observation. -/
theorem identityDiracDualECCurvatureObservation_normalSection
    (observation : LorentzianCoframe →L[ℝ] ℝ) :
    identityDiracDualECCurvatureObservation
        (identityDiracDualECCurvatureNormalSection observation) =
      observation := by
  apply ContinuousLinearMap.ext
  intro variation
  change
    gravityTopologicalWedgeCoefficient
        (physicalIIPlusCoframeTangent (1 : LorentzianCoframe) variation)
        (gravityInternalPairVarianceNormalization
          (gravityInternalPairVarianceNormalization
            (linearPlebanskiMultiplierOfCoframeResponse
              (linearPlebanskiCoframeResponseOfStress (-observation))))) =
      observation variation
  rw [gravityInternalPairVarianceNormalization_involutive]
  rw [identityDiracDualECPrincipal_eq_linearPlebanski]
  have normalized := DFunLike.congr_fun
    (linearPlebanskiCoframePrincipal_response_eq_neg (-observation))
    variation
  simpa using normalized

/-- The action-normalized section is faithful: its generated curvature
increment determines exactly one coframe covector.  This rules out a hidden
branch choice inside the normal carrier. -/
theorem identityDiracDualECCurvatureNormalSection_injective :
    Function.Injective identityDiracDualECCurvatureNormalSection := by
  intro first second equality
  have observed := congrArg identityDiracDualECCurvatureObservation equality
  simpa only [identityDiracDualECCurvatureObservation_normalSection]
    using observed

/-! ## Faithful current-kernel transport -/

/-- The part of a current raw curvature not observed by the identity-contact
EC coframe equation.  It is computed from the current curvature itself. -/
def identityDiracDualECCurvatureKernelPart
    (rawCurvature : PhysicalBivector) : PhysicalBivector :=
  rawCurvature -
    identityDiracDualECCurvatureNormalSection
      (identityDiracDualECCurvatureObservation rawCurvature)

theorem identityDiracDualECCurvatureObservation_kernelPart
    (rawCurvature : PhysicalBivector) :
    identityDiracDualECCurvatureObservation
        (identityDiracDualECCurvatureKernelPart rawCurvature) =
      0 := by
  rw [identityDiracDualECCurvatureKernelPart,
    identityDiracDualECCurvatureObservation_sub,
    identityDiracDualECCurvatureObservation_normalSection]
  abel

/-- Replace only the observed EC component and retain the complete current
kernel component. -/
def identityDiracDualECCurvatureTarget
    (current : PhysicalBivector)
    (observation : LorentzianCoframe →L[ℝ] ℝ) :
    PhysicalBivector :=
  identityDiracDualECCurvatureKernelPart current +
    identityDiracDualECCurvatureNormalSection observation

/-- Exact `(01,01)` coordinate of the identity-contact target, retaining the
raw kernel and replacing only the four-diagonal observed component. -/
theorem identityDiracDualECCurvatureTarget_zero_zero
    (current : PhysicalBivector)
    (observation : LorentzianCoframe →L[ℝ] ℝ) :
    identityDiracDualECCurvatureTarget current observation 0 0 =
      current 0 0 -
        (-(identityDiracDualECCurvatureObservation current
              (coframeCoordinateDirection 0 0) +
            identityDiracDualECCurvatureObservation current
              (coframeCoordinateDirection 1 1)) / 6 +
          (identityDiracDualECCurvatureObservation current
              (coframeCoordinateDirection 2 2) +
            identityDiracDualECCurvatureObservation current
              (coframeCoordinateDirection 3 3)) / 3) +
        (-(observation (coframeCoordinateDirection 0 0) +
            observation (coframeCoordinateDirection 1 1)) / 6 +
          (observation (coframeCoordinateDirection 2 2) +
            observation (coframeCoordinateDirection 3 3)) / 3) := by
  unfold identityDiracDualECCurvatureTarget
    identityDiracDualECCurvatureKernelPart
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [identityDiracDualECCurvatureNormalSection_zero_zero,
    identityDiracDualECCurvatureNormalSection_zero_zero]

theorem identityDiracDualECCurvatureObservation_target
    (current : PhysicalBivector)
    (observation : LorentzianCoframe →L[ℝ] ℝ) :
    identityDiracDualECCurvatureObservation
        (identityDiracDualECCurvatureTarget current observation) =
      observation := by
  rw [identityDiracDualECCurvatureTarget,
    identityDiracDualECCurvatureObservation_add,
    identityDiracDualECCurvatureObservation_kernelPart,
    identityDiracDualECCurvatureObservation_normalSection,
    zero_add]

/-- Updating the observed load cannot erase or alter the current curvature's
unobserved responsibility. -/
theorem identityDiracDualECCurvatureKernelPart_target
    (current : PhysicalBivector)
    (observation : LorentzianCoframe →L[ℝ] ℝ) :
    identityDiracDualECCurvatureKernelPart
        (identityDiracDualECCurvatureTarget current observation) =
      identityDiracDualECCurvatureKernelPart current := by
  unfold identityDiracDualECCurvatureKernelPart
  rw [identityDiracDualECCurvatureObservation_target]
  change
    (identityDiracDualECCurvatureKernelPart current +
        identityDiracDualECCurvatureNormalSection observation) -
        identityDiracDualECCurvatureNormalSection observation =
      identityDiracDualECCurvatureKernelPart current
  abel

/-- **Branch-free target uniqueness.**  Once the current action-normal kernel
responsibility and the requested EC observation are fixed, there is exactly
one target.  Neither a quotient representative nor a branch receipt is an
input. -/
theorem identityDiracDualECCurvatureTarget_unique
    (current candidate : PhysicalBivector)
    (observation : LorentzianCoframe →L[ℝ] ℝ)
    (hObservation :
      identityDiracDualECCurvatureObservation candidate = observation)
    (hKernel :
      identityDiracDualECCurvatureKernelPart candidate =
        identityDiracDualECCurvatureKernelPart current) :
    candidate =
      identityDiracDualECCurvatureTarget current observation := by
  calc
    candidate =
        identityDiracDualECCurvatureKernelPart candidate +
          identityDiracDualECCurvatureNormalSection
            (identityDiracDualECCurvatureObservation candidate) := by
      unfold identityDiracDualECCurvatureKernelPart
      abel
    _ = identityDiracDualECCurvatureKernelPart current +
          identityDiracDualECCurvatureNormalSection observation := by
      rw [hKernel, hObservation]
    _ = identityDiracDualECCurvatureTarget current observation := rfl

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECCurvatureNormalSection
