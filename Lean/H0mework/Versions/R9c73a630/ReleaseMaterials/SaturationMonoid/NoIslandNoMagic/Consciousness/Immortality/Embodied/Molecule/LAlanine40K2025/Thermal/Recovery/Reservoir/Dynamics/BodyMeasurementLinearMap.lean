import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Dynamics.TensorIncidence
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Measurement

open scoped Matrix
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def receiveLinear (tau : Matrix ι ι ℂ) :
    Matrix (ι × κ) (ι × κ) ℂ →ₗ[ℂ] Matrix ((ι × ι) × κ) ((ι × ι) × κ) ℂ where
  toFun rho := Incidence.receivedJoint rho tau
  map_add' left right := by
    ext i j
    change (left _ _ + right _ _) * tau _ _ = left _ _ * tau _ _ + right _ _ * tau _ _
    ring
  map_smul' c rho := by
    ext i j
    change (c * rho _ _) * tau _ _ = c * (rho _ _ * tau _ _)
    ring

def bodyReadLinear :
    Matrix ((ι × ι) × κ) ((ι × ι) × κ) ℂ →ₗ[ℂ] Matrix (ι × κ) (ι × κ) ℂ where
  toFun := Incidence.bodyRead
  map_add' left right := by
    ext i j
    change (∑ r, (left _ _ + right _ _)) = (∑ r, left _ _) + ∑ r, right _ _
    exact Finset.sum_add_distrib
  map_smul' c rho := by
    ext i j
    change (∑ r, c * rho _ _) = c * ∑ r, rho _ _
    exact (Finset.mul_sum _ _ _).symm

def pulseBodyLinear (tau : Matrix ι ι ℂ)
    (U : Matrix.unitaryGroup ((ι × ι) × κ) ℂ) :
    Matrix (ι × κ) (ι × κ) ℂ →ₗ[ℂ] Matrix (ι × κ) (ι × κ) ℂ :=
  bodyReadLinear.comp ((Quantum.conjugation U).comp (receiveLinear tau))

theorem pulseBodyLinear_apply (tau : Matrix ι ι ℂ)
    (U : Matrix.unitaryGroup ((ι × ι) × κ) ℂ) (rho : Matrix (ι × κ) (ι × κ) ℂ) :
    pulseBodyLinear tau U rho = Incidence.bodyRead (Quantum.conjugation U (Incidence.receivedJoint rho tau)) := rfl

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem receiveLinear_star (tau : Matrix ι ι ℂ) (hermitian : tau.IsHermitian)
    (rho : Matrix (ι × κ) (ι × κ) ℂ) :
    receiveLinear tau (star rho) = star (receiveLinear tau rho) := by
  ext i j
  change star (rho (j.1.1,j.2) (i.1.1,i.2)) * tau i.1.2 j.1.2 =
    star (rho (j.1.1,j.2) (i.1.1,i.2) * tau j.1.2 i.1.2)
  have same : star (tau j.1.2 i.1.2) = tau i.1.2 j.1.2 := congrFun (congrFun hermitian.eq _) _
  rw [star_mul, same, mul_comm]

omit [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem bodyReadLinear_star (rho : Matrix ((ι × ι) × κ) ((ι × ι) × κ) ℂ) :
    bodyReadLinear (star rho) = star (bodyReadLinear rho) := by
  ext i j
  change (∑ r : ι, star (rho ((j.1,r),j.2) ((i.1,r),i.2))) =
    star (∑ r : ι, rho ((j.1,r),j.2) ((i.1,r),i.2))
  exact (map_sum (starRingEnd ℂ) _ _).symm

theorem pulseBodyLinear_star (tau : Matrix ι ι ℂ) (hermitian : tau.IsHermitian)
    (U : Matrix.unitaryGroup ((ι × ι) × κ) ℂ) (rho : Matrix (ι × κ) (ι × κ) ℂ) :
    pulseBodyLinear tau U (star rho) = star (pulseBodyLinear tau U rho) := by
  change bodyReadLinear (Quantum.conjugation U (receiveLinear tau (star rho))) = _
  rw [receiveLinear_star tau hermitian]
  change bodyReadLinear (Unitary.conjStarAlgAut ℂ _ U (star _)) = _
  rw [map_star, bodyReadLinear_star]
  rfl

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Measurement
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
