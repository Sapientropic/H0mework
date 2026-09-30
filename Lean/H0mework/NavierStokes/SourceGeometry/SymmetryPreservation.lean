import H0mework.NavierStokes.SourceGeometry.SymmetryReceipt

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.SourceEvenFrequency

open Set
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness

noncomputable section

private theorem path_eq_of_initial_eq {viscosity : Viscosity} {time : ℝ}
    {leftInitial rightInitial : ComplexVorticityHilbertState} (same : leftInitial = rightInitial)
    (left : WholeContinuousMildSerrinReceipt viscosity leftInitial time)
    (right : WholeContinuousMildSerrinReceipt viscosity rightInitial time) :
    left.wholePath = right.wholePath := by
  subst rightInitial
  exact wholeContinuousMildSerrin_sameInitial_unique left right

theorem receipt_on_even_lattice {viscosity : Viscosity} {initial : ComplexVorticityHilbertState} {time : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt viscosity initial time)
    (source : OnEvenLattice initial) (actual : Icc (0 : ℝ) time) :
    OnEvenLattice (receipt.wholePath actual) := by
  have same := path_eq_of_initial_eq (shift_fixed_of_even source) (receiptShift receipt) receipt
  exact even_of_shift_fixed (congrArg (fun path => path actual) same)

end
end SaturationMonoid.NavierStokes.SourceEvenFrequency
