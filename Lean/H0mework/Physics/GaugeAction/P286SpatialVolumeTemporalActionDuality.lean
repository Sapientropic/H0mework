import H0mework.Physics.GaugeAction.P286CanonicalDiagonalActionPrincipal
import H0mework.Physics.Cauchy.P286ActionCauchySplit
import H0mework.Physics.GaugeAction.TopologicalP286GaugeThreeFormDuality

/-!
# Spatial-volume / temporal P286 action duality

The metric-free P286 wedge pairing sends a three-form supported on the
canonical spatial-volume triple `123` to the faithful action-pairing dual of
the temporal one-form with the same internal charge.  Its inverse therefore
recovers that temporal one-form without a sign branch or normalization choice.

The same calculation is exposed for all four components, so every generated
three-form has an explicit branch-free occurrence one-form under the faithful
action pairing.  This module is a structural transporter between two already
generated action carriers.  It does not select an internal charge or consume
a residual.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineP286SpatialVolumeTemporalActionDuality

open ProofFreeRicherAnholonomicSource
open StageNineP286ActionCauchySplit
open StageNineP286CanonicalDiagonalActionPrincipal
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineHolonomicField
open StageNineTopologicalFourFormPairing
open StageNineTopologicalLorentzThreeFormDuality
open StageNineTopologicalP286GaugeThreeFormDuality
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

/-- Complete metric-free W13 conversion from a three-form to the faithful
occurrence one-form selected by the P286 action pairing. -/
def p286GaugeThreeFormOccurrenceOneFormNormalForm
    (threeForm : P286GaugeThreeForm) : P286GaugeOneForm :=
  fun direction =>
    oneWedgeThreeSign direction •
      threeForm (missingTripleOfOneForm direction)

theorem p286GaugeThreeFormWedgeDual_eq_pairingDual_occurrenceOneForm
    (threeForm : P286GaugeThreeForm) :
    p286GaugeThreeFormWedgeLinearDual threeForm =
      p286GaugeOneFormPairingDual
        (p286GaugeThreeFormOccurrenceOneFormNormalForm threeForm) := by
  apply LinearMap.ext
  intro oneForm
  change
    (∑ direction : LorentzianIndex,
      oneWedgeThreeSign direction *
        p286CoordinateLiePairing (oneForm direction)
          (threeForm (missingTripleOfOneForm direction))) =
      ∑ direction : LorentzianIndex,
        p286CoordinateLiePairing
          (oneWedgeThreeSign direction •
            threeForm (missingTripleOfOneForm direction))
          (oneForm direction)
  apply Finset.sum_congr rfl
  intro direction _
  rw [p286CoordinateLiePairing_smul_left,
    p286CoordinateLiePairing_symmetric]

/-- The faithful action-pairing inverse reads every oriented three-form
component with the W13 sign fixed by the spacetime convention. -/
theorem p286PairingInverse_wedgeDual_allComponents
    (threeForm : P286GaugeThreeForm) :
    p286GaugeOneFormPairingEquiv.symm
        (p286GaugeThreeFormWedgeLinearDual threeForm) =
      p286GaugeThreeFormOccurrenceOneFormNormalForm threeForm := by
  rw [p286GaugeThreeFormWedgeDual_eq_pairingDual_occurrenceOneForm]
  change
    p286GaugeOneFormPairingEquiv.symm
        (p286GaugeOneFormPairingEquiv
          (p286GaugeThreeFormOccurrenceOneFormNormalForm threeForm)) = _
  exact p286GaugeOneFormPairingEquiv.symm_apply_apply _

/-- P286 three-form supported in the canonical spatial volume triple `123`. -/
def p286SpatialVolumeGaugeThreeForm
    (charge : P286CoordinateCarrier) : P286GaugeThreeForm :=
  Pi.single 3 charge

/-- Metric-free wedge duality sends the spatial volume three-form to the
positive pairing dual of the temporal one-form with the same charge. -/
theorem p286SpatialVolumeGaugeThreeForm_wedgeDual
    (charge : P286CoordinateCarrier) :
    p286GaugeThreeFormWedgeLinearDual
        (p286SpatialVolumeGaugeThreeForm charge) =
      p286GaugeOneFormPairingDual
        (p286TemporalGaugeOneForm charge) := by
  apply LinearMap.ext
  intro direction
  classical
  simp [p286GaugeThreeFormWedgeLinearDual,
    p286GaugeOneFormThreeFormWedgeCoefficient,
    p286GaugeOneFormPairingDual,
    p286SpatialVolumeGaugeThreeForm,
    p286TemporalGaugeOneForm,
    canonicalLorentzianTimeDirection,
    oneWedgeThreeSign, missingTripleOfOneForm,
    Fin.sum_univ_four]
  exact p286CoordinateLiePairing_symmetric _ _

/-- The inverse action pairing therefore recovers the temporal one-form
without a branch or normalization choice. -/
theorem p286PairingInverse_spatialVolumeWedgeDual
    (charge : P286CoordinateCarrier) :
    p286GaugeOneFormPairingEquiv.symm
        (p286GaugeThreeFormWedgeLinearDual
          (p286SpatialVolumeGaugeThreeForm charge)) =
      p286TemporalGaugeOneForm charge := by
  apply p286GaugeOneFormPairingEquiv.injective
  rw [p286GaugeOneFormPairingEquiv.apply_symm_apply]
  exact p286SpatialVolumeGaugeThreeForm_wedgeDual charge

end

end
  SaturationMonoid.PhysicsCore.StageNineP286SpatialVolumeTemporalActionDuality
