import H0mework.Physics.Dirac.DiracExteriorMatterAction

/-!
# P286--Dirac adjoint coefficient material

The primal spinor and its Dirac adjoint are generated from one four-component
coefficient carrier.  Finite Dirac algebra then makes every vector-current
coordinate real.  This module contains no spacetime field, equation,
settlement, root event or completed calculation trace.
-/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore
namespace StageNineP286DiracAdjointCoefficientMaterial

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open SU7ExteriorMatterGaugeCovariantJet

noncomputable section

/-- Common P286 coefficient material for the four Dirac spin slots. -/
def p286SpinMatter (coefficient : Fin 4 → ℂ) :
    DiracExteriorMatterCarrier :=
  fun spin => coefficient spin • p286HyperchargeMatterProbe

/-- Canonical coefficient readout from the occupied hypercharge coordinate.
It is a dependent readout of an actual matter carrier, not a supplied
coefficient history. -/
def p286SpinCoefficient (matter : DiracExteriorMatterCarrier) : Fin 4 → ℂ :=
  fun spin => hyperchargeDegreeTwoMatterCoordinate (matter spin)

@[simp] theorem p286SpinCoefficient_p286SpinMatter
    (coefficient : Fin 4 → ℂ) :
    p286SpinCoefficient (p286SpinMatter coefficient) = coefficient := by
  funext spin
  simp [p286SpinCoefficient, p286SpinMatter,
    p286HyperchargeMatterProbe, hyperchargeDegreeTwoMatterCoordinate]

theorem p286SpinMatter_injective : Function.Injective p286SpinMatter :=
  Function.LeftInverse.injective p286SpinCoefficient_p286SpinMatter

/-- Hypercharge coordinate dual at one Dirac spin slot. -/
def p286SpinCoordinate (spin : Fin 4) :
    Module.Dual ℂ DiracExteriorMatterCarrier where
  toFun matter := hyperchargeDegreeTwoMatterCoordinate (matter spin)
  map_add' first second := by simp
  map_smul' scalar matter := by simp

/-- Dirac adjoint generated from the same four coefficient functions. -/
def p286SpinAdjoint (coefficient : Fin 4 → ℂ) :
    Module.Dual ℂ DiracExteriorMatterCarrier :=
  (starRingEnd ℂ (coefficient 2)) • p286SpinCoordinate 0 +
    (starRingEnd ℂ (coefficient 3)) • p286SpinCoordinate 1 +
    (starRingEnd ℂ (coefficient 0)) • p286SpinCoordinate 2 +
    (starRingEnd ℂ (coefficient 1)) • p286SpinCoordinate 3

/-- A primal carrier and adjoint dual are two restrictions of one canonical
P286 coefficient material.  The coefficient is read from the primal field,
so the proposition contains no existential choice. -/
def P286DiracPaired
    (matter : DiracExteriorMatterCarrier)
    (adjoint : Module.Dual ℂ DiracExteriorMatterCarrier) : Prop :=
  matter = p286SpinMatter (p286SpinCoefficient matter) ∧
    adjoint = p286SpinAdjoint (p286SpinCoefficient matter)

/-- Canonical off-material primal residue. -/
def p286PrimalResidual (matter : DiracExteriorMatterCarrier) :
    DiracExteriorMatterCarrier :=
  matter - p286SpinMatter (p286SpinCoefficient matter)

/-- Canonical adjoint residue after the primal coefficient has been fixed. -/
def p286AdjointResidual
    (matter : DiracExteriorMatterCarrier)
    (adjoint : Module.Dual ℂ DiracExteriorMatterCarrier) :
    Module.Dual ℂ DiracExteriorMatterCarrier :=
  adjoint - p286SpinAdjoint (p286SpinCoefficient matter)

theorem p286DiracPaired_iff_residuals_zero
    (matter : DiracExteriorMatterCarrier)
    (adjoint : Module.Dual ℂ DiracExteriorMatterCarrier) :
    P286DiracPaired matter adjoint ↔
      p286PrimalResidual matter = 0 ∧
        p286AdjointResidual matter adjoint = 0 := by
  simp [P286DiracPaired, p286PrimalResidual, p286AdjointResidual,
    sub_eq_zero]

@[simp] theorem p286DiracPaired_material
    (coefficient : Fin 4 → ℂ) :
    P286DiracPaired
      (p286SpinMatter coefficient) (p286SpinAdjoint coefficient) := by
  simp [P286DiracPaired]

/-- A common P286 coefficient history generates a real Dirac-vector current.
The target is a finite algebraic normal form, not an assumed current law. -/
theorem p286SpinAdjoint_diracCurrent_real
    (coefficient : Fin 4 → ℂ)
    (direction : LorentzianIndex) :
    (p286SpinAdjoint coefficient
      (diracMatrixMatterAction (diracGamma direction)
        (p286SpinMatter coefficient))).im = 0 := by
  fin_cases direction <;>
    simp [p286SpinMatter, p286SpinAdjoint, p286SpinCoordinate,
      diracMatrixMatterAction, diracGamma, diracGammaZero,
      diracGammaOne, diracGammaTwo, diracGammaThree,
      p286HyperchargeMatterProbe, hyperchargeDegreeTwoMatterCoordinate,
      Fin.sum_univ_four, Complex.mul_im] <;>
    ring

/-- Any actual primal/adjoint pair carried by the common P286 material has a
real Dirac-vector current in every Lorentz direction. -/
theorem P286DiracPaired.diracCurrent_real
    {matter : DiracExteriorMatterCarrier}
    {adjoint : Module.Dual ℂ DiracExteriorMatterCarrier}
    (paired : P286DiracPaired matter adjoint)
    (direction : LorentzianIndex) :
    (adjoint
      (diracMatrixMatterAction (diracGamma direction) matter)).im = 0 := by
  rw [paired.1, paired.2]
  exact p286SpinAdjoint_diracCurrent_real
    (p286SpinCoefficient matter) direction

/-- Two source fields carried by the same P286 material class generate a real
Hermitian cross current.  This is the finite algebraic eliminator needed by
the temporal primitive calculation; no zero current is supplied. -/
theorem P286DiracPaired.primitiveCross_real
    {carryMatter primitiveMatter : DiracExteriorMatterCarrier}
    {carryAdjoint primitiveAdjoint :
      Module.Dual ℂ DiracExteriorMatterCarrier}
    (carryPaired : P286DiracPaired carryMatter carryAdjoint)
    (primitivePaired : P286DiracPaired primitiveMatter primitiveAdjoint)
    (direction : LorentzianIndex) :
    (carryAdjoint
          (diracMatrixMatterAction (diracGamma direction) primitiveMatter) +
        primitiveAdjoint
          (diracMatrixMatterAction (diracGamma direction) carryMatter) +
        primitiveAdjoint
          (diracMatrixMatterAction (diracGamma direction)
            primitiveMatter)).im = 0 := by
  rw [carryPaired.1, carryPaired.2,
    primitivePaired.1, primitivePaired.2]
  fin_cases direction <;>
    simp [p286SpinMatter, p286SpinAdjoint, p286SpinCoordinate,
      diracMatrixMatterAction, diracGamma, diracGammaZero,
      diracGammaOne, diracGammaTwo, diracGammaThree,
      p286HyperchargeMatterProbe, hyperchargeDegreeTwoMatterCoordinate,
      Fin.sum_univ_four, Complex.mul_im] <;>
    ring

end
end StageNineP286DiracAdjointCoefficientMaterial
end SaturationMonoid.PhysicsCore
