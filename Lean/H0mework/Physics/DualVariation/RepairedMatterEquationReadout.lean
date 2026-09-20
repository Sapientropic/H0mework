import H0mework.Physics.DualVariation.MotherAction
import H0mework.Physics.DualVariation.RepairedMatterResponseOperator

/-!
# Repaired matter action-law readout

This dependency-light module connects the repaired temporal action law to
the primitive Dirac-dual matter Euler vector.  It is a readout only: the
action-generated response remains owned by
`StageNineDiracDualFormNativeRepairedMatterResponseOperator`.

Keeping this implication here prevents generic joint producers from
importing a fixed P506 spatial-section development merely to read the matter
equation.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeRepairedMatterEquationReadout

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineDiracDualYukawaLocalSpinDensity
open StageNineDiracKineticLocalSpinDensity
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineMatterCovariantDerivativeAffine
open StageNineMatterVariation
open StageNineP286ActionCauchySplit
open StageNineP286GaugeConnectionVariationDensity

noncomputable section

set_option autoImplicit false

/-- The repaired temporal action law is exactly the primitive Dirac-dual
matter equation in canonical chart coordinates.  It consumes an already
generated action law and constructs no response. -/
theorem generatedContinuumDiracDualMatterVector_zero_of_repairedActionLaw
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (actionLaw :
      HolonomicDiracDualCurrentCoframeMatterTimeActionLaw configuration point
        (holonomicMatterCovariantDerivative configuration point
          canonicalLorentzianTimeDirection)) :
    generatedContinuumDiracDualMatterVector source 0 point
        (toContinuumPointField configuration point) =
      0 := by
  unfold generatedContinuumDiracDualMatterVector
    generatedContinuumMatterKineticVector
    generatedContinuumDiracDualYukawaVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
  simp only [toContinuumPointField,
    matterDerivativeFrameRelative_zeroChart,
    matterFrameRelative_zeroChart,
    scalarFrameRelativeCoordinates_zeroChart]
  unfold HolonomicDiracDualCurrentCoframeMatterTimeActionLaw at actionLaw
  unfold CurrentCoframeMatterTemporalActionLaw at actionLaw
  unfold currentCoframeMatterTemporalPrincipal at actionLaw
  unfold holonomicDiracDualCurrentCoframeMatterKnownVector at actionLaw
  simpa [canonicalLorentzianTimeDirection, Fin.sum_univ_four,
    Fin.sum_univ_three, add_assoc] using actionLaw

/-- The repaired current-coframe action law is exactly the zero fiber of the
primitive Dirac vector of the same mother action.  The reverse direction is
needed by Cauchy compilers that start from an actual candidate section rather
than from a previously generated response. -/
theorem
    holonomicDiracDualCurrentCoframeMatterTimeActionLaw_iff_generatedContinuumDiracDualMatterVector_zero
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    HolonomicDiracDualCurrentCoframeMatterTimeActionLaw configuration point
        (holonomicMatterCovariantDerivative configuration point
          canonicalLorentzianTimeDirection) ↔
      generatedContinuumDiracDualMatterVector source 0 point
        (toContinuumPointField configuration point) = 0 := by
  constructor
  · exact generatedContinuumDiracDualMatterVector_zero_of_repairedActionLaw
      source configuration point
  · intro vectorZero
    unfold generatedContinuumDiracDualMatterVector
      generatedContinuumMatterKineticVector
      generatedContinuumDiracDualYukawaVector
      matterCovariantDerivativeVariationVector
      matterCovariantDerivativeKineticSum at vectorZero
    simp only [toContinuumPointField,
      matterDerivativeFrameRelative_zeroChart,
      matterFrameRelative_zeroChart,
      scalarFrameRelativeCoordinates_zeroChart] at vectorZero
    unfold HolonomicDiracDualCurrentCoframeMatterTimeActionLaw
      CurrentCoframeMatterTemporalActionLaw
      currentCoframeMatterTemporalPrincipal
      holonomicDiracDualCurrentCoframeMatterKnownVector
    simpa [canonicalLorentzianTimeDirection, Fin.sum_univ_four,
      Fin.sum_univ_three, add_assoc] using vectorZero

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeRepairedMatterEquationReadout
