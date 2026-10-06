import H0mework.Physics.Matter.SU7ExteriorMatterRestriction
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! Actual exterior characters of the source scalar--Canonical contractions.
The full nonabelian kernel and differential source maps are generated from
the original action by `em-identification/composite.py`. The coefficient laws
below preserve both elementary legs of that generated field. -/
set_option autoImplicit false
noncomputable section
namespace SaturationMonoid.PhysicsCore.LowEnergy.Electromagnetic.Identification.Composite

open SU7MotherLieAlgebra SU7ExteriorMatterRestriction

private def color (c : Fin 3) : SU7MotherIndex := Sum.inl c
private def weak (w : Fin 2) : SU7MotherIndex := Sum.inr (Sum.inl w)
private def plus : SU7MotherIndex := Sum.inr (Sum.inr (Sum.inl 0))
private def minus : SU7MotherIndex := Sum.inr (Sum.inr (Sum.inr 0))

private def pair (c : Fin 3) : Finset SU7MotherIndex :=
  if c = 0 then {color 1, color 2}
  else if c = 1 then {color 0, color 2} else {color 0, color 1}

private def scalarSubset (channel : Fin 2) (c : Fin 3) : Finset SU7MotherIndex :=
  pair c ∪ if channel = 0 then {weak 0, weak 1} else {plus, minus}

def scalarBasis (channel : Fin 2) (c : Fin 3) : ExteriorBasisIndex 4 :=
  ⟨scalarSubset channel c, by
    change (scalarSubset channel c).card = 4
    fin_cases channel <;> fin_cases c <;> decide⟩

def matterBasis (c : Fin 3) : ExteriorBasisIndex 2 :=
  ⟨{color c, plus}, by
    change ({color c, plus} : Finset SU7MotherIndex).card = 2
    fin_cases c <;> decide⟩

theorem scalar_weight (channel : Fin 2) (c : Fin 3) :
    exteriorHyperchargeWeight (scalarBasis channel c) = 0 := by
  fin_cases channel <;> fin_cases c <;> decide

theorem matter_weight (c : Fin 3) :
    exteriorHyperchargeWeight (matterBasis c) = 1 := by
  fin_cases c <;> decide

theorem scalar_character (z : Circle) (channel : Fin 2) (c : Fin 3) :
    p286RestrictedExteriorRepresentation 4 (p286HyperchargeElement z)
      (su7ExteriorBasis 4 (scalarBasis channel c)) =
      su7ExteriorBasis 4 (scalarBasis channel c) := by
  rw [p286RestrictedHypercharge_exterior_basis_weight, scalar_weight]
  simp

theorem matter_character (z : Circle) (c : Fin 3) :
    p286RestrictedExteriorRepresentation 2 (p286HyperchargeElement z)
      (su7ExteriorBasis 2 (matterBasis c)) =
      (z : ℂ) • su7ExteriorBasis 2 (matterBasis c) := by
  rw [p286RestrictedHypercharge_exterior_basis_weight, matter_weight]
  simp

/-- One signed summand; the actual contraction is the generated sum of three. -/
def first (phi0 phi1 psi0 psi1 : ℂ) : ℂ := phi0*psi1+phi1*psi0
def second (phi0 phi1 phi2 psi0 psi1 psi2 : ℂ) : ℂ :=
  phi0*psi2+phi1*psi1+phi2*psi0

theorem second_split (phi0 phi1 phi2 psi0 psi1 psi2 : ℂ) :
    second phi0 phi1 phi2 psi0 psi1 psi2 =
      first phi0 phi2 psi0 psi2+phi1*psi1 := by
  unfold second first
  ring

/-- The physical derivative includes the derivative of the scalar leg. -/
theorem covariant_product (phi psi dphi dpsi A qphi qpsi : ℂ) :
    first phi dphi psi dpsi+A*(qphi+qpsi)*(phi*psi) =
      (dphi+A*qphi*phi)*psi+phi*(dpsi+A*qpsi*psi) := by
  unfold first
  ring

end SaturationMonoid.PhysicsCore.LowEnergy.Electromagnetic.Identification.Composite
