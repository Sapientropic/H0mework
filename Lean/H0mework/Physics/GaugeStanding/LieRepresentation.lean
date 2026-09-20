import H0mework.Physics.Exterior.ExteriorMotherLieRepresentation
import H0mework.Physics.GaugeAction.P286BracketCalculus
import H0mework.Physics.GaugeAction.P286GaugeConnectionVariationDensity

/-!
# S9-C: linked active P286 Lie representation

The exterior mother bracket constructed at the algebraic representation layer
is transported here through the three actual charged carriers used by the
linked P286 variation:

* the scalar coordinate carrier;
* the exterior-spinor product carrier;
* the Dirac-indexed exterior carrier.

The final coordinate theorem specializes the scalar law to the faithful P286
coordinate bracket.  These are direct representation readouts.  No source,
Ward identity, jet, stationarity law, residual equation, supplied receipt, or
target equality is accepted at a theorem mouth.
-/

open SaturationMonoid

namespace
  SaturationMonoid.PhysicsCore.StageNineP286LinkedActiveLieRepresentation

open DiracExteriorMatterAction
open StageNineDynamicBreakingVacuum
open StageNineExteriorMotherLieRepresentation
open StageNineHolonomicField
open StageNineP286BracketCalculus
open StageNineP286GaugeConnectionVariationDensity
open SU7ExteriorMatterRepresentation
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false

/-- The degree-four exterior bracket descends through the actual scalar
coordinate equivalence. -/
theorem scalarMotherLieAction_bracket
    (first second : SU7MotherLieMatrix)
    (scalar : ScalarCoordinateCarrier) :
    scalarMotherLieAction (suLieBracket first second) scalar =
      scalarMotherLieAction first
          (scalarMotherLieAction second scalar) -
        scalarMotherLieAction second
          (scalarMotherLieAction first scalar) := by
  have exteriorBracket :=
    LinearMap.congr_fun
      (exteriorMotherLieAction_bracket 4 first second)
      (scalarCoordinateEquiv.symm scalar)
  simpa [scalarMotherLieAction, LinearMap.comp_apply] using
    congrArg scalarCoordinateEquiv exteriorBracket

/-- The product of the degree-six, degree-two, and degree-four actual
exterior actions carries the mother bracket to the endomorphism commutator. -/
theorem exteriorSpinorMotherLieAction_bracket
    (first second : SU7MotherLieMatrix) :
    exteriorSpinorMotherLieAction (suLieBracket first second) =
      exteriorSpinorMotherLieAction first ∘ₗ
          exteriorSpinorMotherLieAction second -
        exteriorSpinorMotherLieAction second ∘ₗ
          exteriorSpinorMotherLieAction first := by
  apply LinearMap.ext
  intro field
  apply Prod.ext
  · change
      exteriorMotherLieAction 6 (suLieBracket first second) field.1 =
        exteriorMotherLieAction 6 first
            (exteriorMotherLieAction 6 second field.1) -
          exteriorMotherLieAction 6 second
            (exteriorMotherLieAction 6 first field.1)
    exact LinearMap.congr_fun
      (exteriorMotherLieAction_bracket 6 first second) field.1
  · apply Prod.ext
    · change
        exteriorMotherLieAction 2 (suLieBracket first second) field.2.1 =
          exteriorMotherLieAction 2 first
              (exteriorMotherLieAction 2 second field.2.1) -
            exteriorMotherLieAction 2 second
              (exteriorMotherLieAction 2 first field.2.1)
      exact LinearMap.congr_fun
        (exteriorMotherLieAction_bracket 2 first second) field.2.1
    · change
        exteriorMotherLieAction 4 (suLieBracket first second) field.2.2 =
          exteriorMotherLieAction 4 first
              (exteriorMotherLieAction 4 second field.2.2) -
            exteriorMotherLieAction 4 second
              (exteriorMotherLieAction 4 first field.2.2)
      exact LinearMap.congr_fun
        (exteriorMotherLieAction_bracket 4 first second) field.2.2

/-- Applying the same exterior-spinor action independently at every Dirac
index preserves the bracket law. -/
theorem diracExteriorMotherLieAction_bracket
    (first second : SU7MotherLieMatrix) :
    diracExteriorMotherLieAction (suLieBracket first second) =
      diracExteriorMotherLieAction first ∘ₗ
          diracExteriorMotherLieAction second -
        diracExteriorMotherLieAction second ∘ₗ
          diracExteriorMotherLieAction first := by
  apply LinearMap.ext
  intro field
  funext spin
  change
    exteriorSpinorMotherLieAction (suLieBracket first second) (field spin) =
      exteriorSpinorMotherLieAction first
          (exteriorSpinorMotherLieAction second (field spin)) -
        exteriorSpinorMotherLieAction second
          (exteriorSpinorMotherLieAction first (field spin))
  exact LinearMap.congr_fun
    (exteriorSpinorMotherLieAction_bracket first second) (field spin)

/-- Direct P286-coordinate specialization needed by the linked scalar jet:
the faithful coordinate bracket acts by the commutator of the two actual
scalar actions. -/
theorem scalarP286ActionBilinear_coordinateBracket
    (epsilon connection : P286CoordinateCarrier)
    (scalar : ScalarCoordinateCarrier) :
    scalarP286ActionBilinear (coordinateBracket epsilon connection) scalar =
      scalarP286ActionBilinear epsilon
          (scalarP286ActionBilinear connection scalar) -
        scalarP286ActionBilinear connection
          (scalarP286ActionBilinear epsilon scalar) := by
  change
    scalarMotherLieAction
        (p286LieBlockEmbed
          (p286CoordinateEquiv.symm
            (coordinateBracket epsilon connection))) scalar =
      scalarMotherLieAction
          (p286LieBlockEmbed (p286CoordinateEquiv.symm epsilon))
          (scalarMotherLieAction
            (p286LieBlockEmbed (p286CoordinateEquiv.symm connection))
            scalar) -
        scalarMotherLieAction
          (p286LieBlockEmbed (p286CoordinateEquiv.symm connection))
          (scalarMotherLieAction
            (p286LieBlockEmbed (p286CoordinateEquiv.symm epsilon))
            scalar)
  rw [coordinateBracket, p286CoordinateEquiv.symm_apply_apply,
    p286LieBlockEmbed_bracket]
  exact scalarMotherLieAction_bracket
    (p286LieBlockEmbed (p286CoordinateEquiv.symm epsilon))
    (p286LieBlockEmbed (p286CoordinateEquiv.symm connection))
    scalar

end

end SaturationMonoid.PhysicsCore.StageNineP286LinkedActiveLieRepresentation
