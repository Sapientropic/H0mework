import H0mework.NavierStokes.SourceEstimates.WholeKineticDecay
import H0mework.NavierStokes.WholeReceipt.PrefixReceipt
import H0mework.NavierStokes.Accumulation.StandingPaidMediumState

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.WholeKineticDecay

open Set
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientStandingPaidMediumState

/-- The original finite-prefix compiler supplies every hypothesis of the whole-receipt decay law. -/
theorem prefix_kinetic_le_exp {nu : Viscosity} (initial : GeneratedWholeRestartCurrent nu)
    (physicalStage : Nat) (actual : Icc (0 : Real) (WholePrefixState.duration initial physicalStage)) :
    puncturedWholeVorticityKineticMass ((WholePrefixReceipt.receipt initial physicalStage).wholePath actual) ≤
      puncturedWholeVorticityKineticMass initial.initialState *
        Real.exp (-2 * nu.coeff * (2 * Real.pi) ^ 2 * actual.1) :=
  kinetic_le_exp (WholePrefixReceipt.receipt initial physicalStage) actual

/-- This is the fixed raw16 source's own whole NS path, on its unchanged cumulative physical clock. -/
theorem fixed_prefix_kinetic_le_exp (physicalStage : Nat)
    (actual : Icc (0 : Real) (WholePrefixState.duration concreteCounterexampleInitial physicalStage)) :
    puncturedWholeVorticityKineticMass
        ((WholePrefixReceipt.receipt concreteCounterexampleInitial physicalStage).wholePath actual) ≤
      puncturedWholeVorticityKineticMass concreteCounterexampleInitial.initialState *
        Real.exp (-2 * concreteCounterexampleViscosity.coeff * (2 * Real.pi) ^ 2 * actual.1) :=
  prefix_kinetic_le_exp concreteCounterexampleInitial physicalStage actual

end SaturationMonoid.NavierStokes.WholeKineticDecay
