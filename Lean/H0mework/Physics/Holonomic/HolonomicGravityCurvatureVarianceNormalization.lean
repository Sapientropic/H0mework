import H0mework.Physics.Geometry.GravityBianchi

/-!
# S9-J0-COV-1: holonomic gravity-curvature variance normalization

The existing `holonomicGravityCurvature` readout records the canonical
internal pair as the Minkowski-lowered component `F_IJ` of the actual mixed
curvature `F^I_J`.  This module supplies the canonical finite-dimensional
identification between lowered and contravariant internal-pair coordinates:
multiply each internal pair by its induced Lorentzian sign.

The same map is its own inverse, so it is the single authority for both
raising and lowering.  The corrected readout remains derived from the actual
primitive holonomic connection; no curvature, variance choice, shell,
covariance, or action-invariance certificate is accepted as input.

This is only typed readout infrastructure.  It does not define a local gauge
transformation, claim Spin covariance, modify `toContinuumPointField`, or
change any candidate action.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineHolonomicGravityCurvatureVarianceNormalization

open ProofFreeRicherAnholonomicSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineGravityBianchi

noncomputable section

private theorem internalPairVarianceSign_sq (pair : Fin 6) :
    lorentzianTwoFormSign pair ^ 2 = 1 := by
  fin_cases pair <;>
    norm_num [lorentzianTwoFormSign, minkowskiInternalSign,
      pairFirst, pairSecond] <;> simp

private theorem minkowskiInternalSign_sq
    (index : LorentzianIndex) :
    minkowskiInternalSign index ^ 2 = 1 := by
  fin_cases index <;>
    norm_num [minkowskiInternalSign]

/-- The canonical internal-pair variance identification.  Multiplication by
the induced Lorentzian pair sign raises two internal indices and, because the
same sign squares to one, the same map lowers them again. -/
def gravityInternalPairVarianceNormalization :
    PhysicalBivector ≃ₗ[ℝ] PhysicalBivector where
  toFun := fun bivector internalPair spacetimePair =>
    lorentzianTwoFormSign internalPair *
      bivector internalPair spacetimePair
  invFun := fun bivector internalPair spacetimePair =>
    lorentzianTwoFormSign internalPair *
      bivector internalPair spacetimePair
  left_inv := by
    intro bivector
    funext internalPair spacetimePair
    change
      lorentzianTwoFormSign internalPair *
          (lorentzianTwoFormSign internalPair *
            bivector internalPair spacetimePair) =
        bivector internalPair spacetimePair
    rw [← mul_assoc]
    rw [show
      lorentzianTwoFormSign internalPair *
          lorentzianTwoFormSign internalPair = 1 by
        simpa [pow_two] using internalPairVarianceSign_sq internalPair]
    simp
  right_inv := by
    intro bivector
    funext internalPair spacetimePair
    change
      lorentzianTwoFormSign internalPair *
          (lorentzianTwoFormSign internalPair *
            bivector internalPair spacetimePair) =
        bivector internalPair spacetimePair
    rw [← mul_assoc]
    rw [show
      lorentzianTwoFormSign internalPair *
          lorentzianTwoFormSign internalPair = 1 by
        simpa [pow_two] using internalPairVarianceSign_sq internalPair]
    simp
  map_add' := by
    intro first second
    funext internalPair spacetimePair
    change
      lorentzianTwoFormSign internalPair *
          (first internalPair spacetimePair +
            second internalPair spacetimePair) =
        lorentzianTwoFormSign internalPair *
            first internalPair spacetimePair +
          lorentzianTwoFormSign internalPair *
            second internalPair spacetimePair
    ring
  map_smul' := by
    intro parameter bivector
    funext internalPair spacetimePair
    change
      lorentzianTwoFormSign internalPair *
          (parameter * bivector internalPair spacetimePair) =
        parameter *
          (lorentzianTwoFormSign internalPair *
            bivector internalPair spacetimePair)
    ring

@[simp] theorem gravityInternalPairVarianceNormalization_apply
    (bivector : PhysicalBivector)
    (internalPair spacetimePair : Fin 6) :
    gravityInternalPairVarianceNormalization bivector
        internalPair spacetimePair =
      lorentzianTwoFormSign internalPair *
        bivector internalPair spacetimePair :=
  rfl

@[simp] theorem gravityInternalPairVarianceNormalization_involutive
    (bivector : PhysicalBivector) :
    gravityInternalPairVarianceNormalization
        (gravityInternalPairVarianceNormalization bivector) =
      bivector :=
  gravityInternalPairVarianceNormalization.left_inv bivector

theorem gravityInternalPairVarianceNormalization_injective :
    Function.Injective gravityInternalPairVarianceNormalization :=
  gravityInternalPairVarianceNormalization.injective

@[simp] theorem gravityInternalPairVarianceNormalization_eq_zero_iff
    (bivector : PhysicalBivector) :
    gravityInternalPairVarianceNormalization bivector = 0 ↔
      bivector = 0 := by
  constructor
  · intro normalizedZero
    apply gravityInternalPairVarianceNormalization.injective
    simpa using normalizedZero
  · rintro rfl
    exact map_zero gravityInternalPairVarianceNormalization

/-- Lorentzian variance normalization is not a disguised identity map.  The
timelike-spacelike internal pair changes sign on the constant unit probe. -/
theorem gravityInternalPairVarianceNormalization_nontrivial :
    ∃ bivector : PhysicalBivector,
      gravityInternalPairVarianceNormalization bivector ≠ bivector := by
  refine ⟨fun _ _ => 1, ?_⟩
  intro equality
  have coordinateEquality := congrFun (congrFun equality 0) 0
  norm_num [gravityInternalPairVarianceNormalization,
    lorentzianTwoFormSign, minkowskiInternalSign, pairFirst, pairSecond] at coordinateEquality

/-- Contravariant internal-pair readout of the actual holonomic gravity
curvature.  It is computed from the existing lowered readout rather than
stored as another curvature field. -/
def holonomicContravariantGravityCurvature
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : PhysicalBivector :=
  gravityInternalPairVarianceNormalization
    (holonomicGravityCurvature configuration point)

@[simp] theorem holonomicContravariantGravityCurvature_apply
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (internalPair spacetimePair : Fin 6) :
    holonomicContravariantGravityCurvature configuration point
        internalPair spacetimePair =
      lorentzianTwoFormSign internalPair *
        holonomicGravityCurvature configuration point
          internalPair spacetimePair :=
  rfl

/-- Applying the same variance authority recovers the original lowered
holonomic curvature exactly. -/
@[simp] theorem
    gravityInternalPairVarianceNormalization_contravariantCurvature
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    gravityInternalPairVarianceNormalization
        (holonomicContravariantGravityCurvature configuration point) =
      holonomicGravityCurvature configuration point :=
  gravityInternalPairVarianceNormalization_involutive _

@[simp] theorem holonomicContravariantGravityCurvature_eq_zero_iff
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicContravariantGravityCurvature configuration point = 0 ↔
      holonomicGravityCurvature configuration point = 0 :=
  gravityInternalPairVarianceNormalization_eq_zero_iff _

/-- Component bridge to the faithful ordered mixed curvature.  The historical
readout lowers the first index; normalization raises both internal indices,
leaving exactly the metric sign on the second mixed index. -/
theorem holonomicContravariantGravityCurvature_canonicalPair_eq_ordered
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (point : BasePoint)
    (internalPair spacetimePair : Fin 6) :
    holonomicContravariantGravityCurvature configuration point
        internalPair spacetimePair =
      minkowskiInternalSign (pairSecond internalPair) *
        orderedMixedCurvature configuration point
          (pairFirst spacetimePair) (pairSecond spacetimePair)
          (pairFirst internalPair, pairSecond internalPair) := by
  rw [holonomicContravariantGravityCurvature_apply,
    orderedMixedCurvature_canonicalPair_eq_holonomic configuration smooth]
  unfold lorentzianTwoFormSign
  calc
    (minkowskiInternalSign (pairFirst internalPair) *
        minkowskiInternalSign (pairSecond internalPair)) *
        (minkowskiInternalSign (pairFirst internalPair) *
          orderedMixedCurvature configuration point
            (pairFirst spacetimePair) (pairSecond spacetimePair)
            (pairFirst internalPair, pairSecond internalPair)) =
      minkowskiInternalSign (pairFirst internalPair) ^ 2 *
        minkowskiInternalSign (pairSecond internalPair) *
          orderedMixedCurvature configuration point
            (pairFirst spacetimePair) (pairSecond spacetimePair)
            (pairFirst internalPair, pairSecond internalPair) := by ring
    _ =
      minkowskiInternalSign (pairSecond internalPair) *
        orderedMixedCurvature configuration point
          (pairFirst spacetimePair) (pairSecond spacetimePair)
          (pairFirst internalPair, pairSecond internalPair) := by
      rw [minkowskiInternalSign_sq]
      ring

end

end
  SaturationMonoid.PhysicsCore.StageNineHolonomicGravityCurvatureVarianceNormalization
