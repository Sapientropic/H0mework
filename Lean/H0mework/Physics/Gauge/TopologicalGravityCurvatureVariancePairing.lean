import H0mework.Physics.Geometry.TopologicalFourFormPairing
import H0mework.Physics.Holonomic.HolonomicGravityCurvatureVarianceNormalization

/-!
# Topological gravity pairing with the historical curvature variance

`PhysicalBivector` is the contravariant internal-bivector carrier used by the
Stage-9 gravity auxiliary field and by the topological wedge pairing.  The
historical holonomic curvature readout instead stores its internal pair in
lowered coordinates.  COV-1 supplies the unique raise/lower equivalence.

This module locks the seam: the lowered curvature passes through that
equivalence exactly once before entering the same-variance topological
pairing.  The resulting expression is definitionally equivalent to a mixed
contraction with no additional internal sign.  Variance is therefore derived
from the typed producer and is not a caller-selected convention.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineTopologicalGravityCurvatureVariancePairing

open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineGlobalIntegratedAction
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineTopologicalFourFormPairing

noncomputable section

set_option autoImplicit false

/-- Mixed-variance topological coefficient: the first argument is
contravariant and the second is the historical lowered curvature readout. -/
def gravityTopologicalMixedWedgeCoefficient
    (contravariant lowered : PhysicalBivector) : ℝ :=
  ∑ internalPair : Fin 6,
    orientedTwoFormWedgeCoefficient
      (contravariant internalPair) (lowered internalPair)

/-- Authoritative gravity BF coefficient obtained by raising the historical
curvature exactly once and then using the same-variance pairing. -/
def gravityTopologicalBFCoefficient
    (auxiliary loweredCurvature : PhysicalBivector) : ℝ :=
  gravityTopologicalWedgeCoefficient auxiliary
    (gravityInternalPairVarianceNormalization loweredCurvature)

private theorem internalPairVarianceSign_sq (pair : Fin 6) :
    lorentzianTwoFormSign pair ^ 2 = 1 := by
  fin_cases pair <;>
    simp (disch := decide) [lorentzianTwoFormSign, minkowskiInternalSign,
      pairFirst, pairSecond]

private theorem internalPairVarianceSign_zero :
    lorentzianTwoFormSign (0 : Fin 6) = -1 := by
  simp (disch := decide) [lorentzianTwoFormSign,
    minkowskiInternalSign, pairFirst, pairSecond]

private theorem internalPairVarianceSign_three :
    lorentzianTwoFormSign (3 : Fin 6) = 1 := by
  simp (disch := decide) [lorentzianTwoFormSign,
    minkowskiInternalSign, pairFirst, pairSecond]

/-- Exact once-only variance seam. -/
theorem gravityTopologicalBFCoefficient_eq_mixed
    (auxiliary loweredCurvature : PhysicalBivector) :
    gravityTopologicalBFCoefficient auxiliary loweredCurvature =
      gravityTopologicalMixedWedgeCoefficient auxiliary loweredCurvature := by
  unfold gravityTopologicalBFCoefficient
    gravityTopologicalWedgeCoefficient
    gravityTopologicalMixedWedgeCoefficient
  apply Finset.sum_congr rfl
  intro internalPair _
  change
    lorentzianTwoFormSign internalPair *
        orientedTwoFormWedgeCoefficient (auxiliary internalPair)
          (lorentzianTwoFormSign internalPair •
            loweredCurvature internalPair) =
      orientedTwoFormWedgeCoefficient (auxiliary internalPair)
        (loweredCurvature internalPair)
  rw [orientedTwoFormWedgeCoefficient_smul_right]
  have square := internalPairVarianceSign_sq internalPair
  calc
    lorentzianTwoFormSign internalPair *
        (lorentzianTwoFormSign internalPair *
          orientedTwoFormWedgeCoefficient (auxiliary internalPair)
            (loweredCurvature internalPair)) =
      lorentzianTwoFormSign internalPair ^ 2 *
        orientedTwoFormWedgeCoefficient (auxiliary internalPair)
          (loweredCurvature internalPair) := by ring
    _ = orientedTwoFormWedgeCoefficient (auxiliary internalPair)
        (loweredCurvature internalPair) := by rw [square]; ring

theorem gravityTopologicalBFCoefficient_add_left
    (first second loweredCurvature : PhysicalBivector) :
    gravityTopologicalBFCoefficient (first + second) loweredCurvature =
      gravityTopologicalBFCoefficient first loweredCurvature +
        gravityTopologicalBFCoefficient second loweredCurvature := by
  unfold gravityTopologicalBFCoefficient
  exact gravityTopologicalWedgeCoefficient_add_left first second _

theorem gravityTopologicalBFCoefficient_smul_left
    (parameter : ℝ) (auxiliary loweredCurvature : PhysicalBivector) :
    gravityTopologicalBFCoefficient (parameter • auxiliary) loweredCurvature =
      parameter *
        gravityTopologicalBFCoefficient auxiliary loweredCurvature := by
  unfold gravityTopologicalBFCoefficient
  exact gravityTopologicalWedgeCoefficient_smul_left parameter auxiliary _

theorem gravityTopologicalBFCoefficient_add_right
    (auxiliary first second : PhysicalBivector) :
    gravityTopologicalBFCoefficient auxiliary (first + second) =
      gravityTopologicalBFCoefficient auxiliary first +
        gravityTopologicalBFCoefficient auxiliary second := by
  unfold gravityTopologicalBFCoefficient
  rw [map_add, gravityTopologicalWedgeCoefficient_add_right]

theorem gravityTopologicalBFCoefficient_smul_right
    (parameter : ℝ) (auxiliary loweredCurvature : PhysicalBivector) :
    gravityTopologicalBFCoefficient auxiliary
        (parameter • loweredCurvature) =
      parameter *
        gravityTopologicalBFCoefficient auxiliary loweredCurvature := by
  unfold gravityTopologicalBFCoefficient
  rw [map_smul, gravityTopologicalWedgeCoefficient_smul_right]

theorem gravityTopologicalMixedWedgeCoefficient_single_right
    (first : PhysicalBivector) (internalPair : Fin 6)
    (form : GaugeTwoForm) :
    gravityTopologicalMixedWedgeCoefficient first
        (singleInternalPhysicalBivector internalPair form) =
      orientedTwoFormWedgeCoefficient (first internalPair) form := by
  classical
  unfold gravityTopologicalMixedWedgeCoefficient
    singleInternalPhysicalBivector
  rw [Finset.sum_eq_single internalPair]
  · simp
  · intro candidate _ candidate_ne
    simp [candidate_ne]
  · simp

/-- A timelike internal coordinate detects omission of COV-1 normalization. -/
theorem timelike_variance_normalization_is_not_optional :
    gravityTopologicalBFCoefficient
        (singleInternalPhysicalBivector 0 (twoFormCoordinateBasis 0))
        (singleInternalPhysicalBivector 0 (twoFormCoordinateBasis 3)) = 1 ∧
      gravityTopologicalWedgeCoefficient
        (singleInternalPhysicalBivector 0 (twoFormCoordinateBasis 0))
        (singleInternalPhysicalBivector 0 (twoFormCoordinateBasis 3)) = -1 := by
  constructor
  · rw [gravityTopologicalBFCoefficient_eq_mixed]
    rw [gravityTopologicalMixedWedgeCoefficient_single_right]
    change orientedTwoFormWedgeCoefficient
      (twoFormCoordinateBasis 0) (twoFormCoordinateBasis 3) = 1
    exact orientedTwoFormWedgeCoefficient_basis_zero_three
  · rw [gravityTopologicalWedgeCoefficient_single_right]
    change lorentzianTwoFormSign 0 *
      orientedTwoFormWedgeCoefficient (twoFormCoordinateBasis 0)
        (twoFormCoordinateBasis 3) = -1
    rw [orientedTwoFormWedgeCoefficient_basis_zero_three,
      internalPairVarianceSign_zero]
    norm_num

/-- A spatial internal coordinate is the positive control: its variance sign
is `+1`, so normalization preserves the coordinate value. -/
theorem spatial_variance_normalization_positive_control :
    gravityTopologicalBFCoefficient
        (singleInternalPhysicalBivector 3 (twoFormCoordinateBasis 0))
        (singleInternalPhysicalBivector 3 (twoFormCoordinateBasis 3)) = 1 ∧
      gravityTopologicalWedgeCoefficient
        (singleInternalPhysicalBivector 3 (twoFormCoordinateBasis 0))
        (singleInternalPhysicalBivector 3 (twoFormCoordinateBasis 3)) = 1 := by
  constructor
  · rw [gravityTopologicalBFCoefficient_eq_mixed]
    rw [gravityTopologicalMixedWedgeCoefficient_single_right]
    change orientedTwoFormWedgeCoefficient
      (twoFormCoordinateBasis 0) (twoFormCoordinateBasis 3) = 1
    exact orientedTwoFormWedgeCoefficient_basis_zero_three
  · rw [gravityTopologicalWedgeCoefficient_single_right]
    change lorentzianTwoFormSign 3 *
      orientedTwoFormWedgeCoefficient (twoFormCoordinateBasis 0)
        (twoFormCoordinateBasis 3) = 1
    rw [orientedTwoFormWedgeCoefficient_basis_zero_three,
      internalPairVarianceSign_three]
    norm_num

end

end SaturationMonoid.PhysicsCore.StageNineTopologicalGravityCurvatureVariancePairing
