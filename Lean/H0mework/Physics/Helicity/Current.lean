import H0mework.Physics.Helicity.Source
import H0mework.Physics.SpinPair.GaugeCurrent

/-! The same covariant magnetic curl is paired with the already generated
matter current. This keeps the source Yang--Mills balance in the helicity
producer, rather than treating B·curl B as an unrelated matrix invariant. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Helicity

open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineP286GaugeAuxiliaryVariation SU7MotherLieAlgebra
open Stage9C.Material.SpinPair

noncomputable section

def currentRead (point : BasePoint) (axis : Fin 3) (probe : P286LieBlockData) : ℝ :=
  (spinPairCurrentComplex axis.succ probe (upperDualPhase point) (lowerDualPhase point)
    (upperPhase point) (lowerPhase point)).re

theorem covariantCurl_current (point : BasePoint) (axis : Fin 3) (probe : P286LieBlockData) :
    p286LiePairing (covariantCurl point axis) probe =
      sourceCoupling * lapse ^ 2 * currentRead point axis probe := by
  rw [covariantCurl_eq, p286LiePairing_smul_left, currentRead, actual_spinPairCurrent_spatial,
    gauge_cubic_balance]
  ring

theorem currentRead_magnetic (point : BasePoint) (axis : Fin 3) :
    currentRead point axis (magnetic point axis) = -2 * spinScale * gaugeScale ^ 2 := by
  rw [currentRead, actual_spinPairCurrent_spatial, magnetic_eq,
    p286LiePairing_smul_right, sourceColorP286Generator_pairing_self]
  ring

theorem value_from_actual_current (point : BasePoint) :
    value point = (-sourceCoupling * lapse ^ 2 *
      ∑ axis : Fin 3, currentRead point axis (magnetic point axis) : ℝ) := by
  rw [value_eq]
  congr 1
  simp_rw [currentRead_magnetic]
  norm_num
  have balance := gauge_cubic_balance
  nlinarith [congrArg (fun t : ℝ => 3 * gaugeScale ^ 2 * t) balance]

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Helicity
