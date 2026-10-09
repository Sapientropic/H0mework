import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Dynamics.RetainedBodyLift

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Incidence

open Collision
open scoped Matrix ComplexOrder
noncomputable section

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def bodyObservable (O : Matrix (ι × κ) (ι × κ) ℂ) : Matrix ((ι × ι) × κ) ((ι × ι) × κ) ℂ :=
  (Matrix.kronecker O (1 : Matrix ι ι ℂ)).submatrix bodyReservoir bodyReservoir

omit [DecidableEq ι] [DecidableEq κ] in
theorem regroup_energy (O rho : Matrix ((ι × κ) × ι) ((ι × κ) × ι) ℂ) :
    energy (O.submatrix bodyReservoir bodyReservoir) (rho.submatrix bodyReservoir bodyReservoir) =
      energy O rho := by
  unfold energy
  rw [Matrix.submatrix_mul_equiv]
  exact congrArg Complex.re (Equiv.sum_comp (bodyReservoir (ι := ι) (κ := κ)) (fun i => (O * rho) i i))

theorem bodyObservable_energy (O : Matrix (ι × κ) (ι × κ) ℂ)
    (joint : Matrix ((ι × ι) × κ) ((ι × ι) × κ) ℂ) :
    energy (bodyObservable O) joint = energy O (bodyRead joint) := by
  let old := joint.submatrix bodyReservoir.symm bodyReservoir.symm
  have restore : old.submatrix bodyReservoir bodyReservoir = joint := by ext i j; rfl
  have read := regroup_energy (Matrix.kronecker O (1 : Matrix ι ι ℂ)) old
  rw [restore] at read
  change energy (bodyObservable O) joint = _ at read
  rw [read]
  have reduced := Powered.Dynamics.jointEnergy_real_eq_reduced O (0 : Matrix ι ι ℂ) old
  simpa [energy, Matrix.kronecker, old, bodyRead] using reduced

def donorObservable (H : Matrix ι ι ℂ) : Matrix ((ι × ι) × κ) ((ι × ι) × κ) ℂ :=
  Matrix.kronecker (Matrix.kronecker (1 : Matrix ι ι ℂ) H) (1 : Matrix κ κ ℂ)

theorem donorObservable_energy (H : Matrix ι ι ℂ)
    (joint : Matrix ((ι × ι) × κ) ((ι × ι) × κ) ℂ) :
    energy (donorObservable H) joint =
      energy H (Collision.bathReduce (Powered.Dynamics.systemReduce joint)) := by
  have outer := Powered.Dynamics.jointEnergy_real_eq_reduced (Matrix.kronecker (1 : Matrix ι ι ℂ) H)
    (0 : Matrix κ κ ℂ) joint
  have outerRead : energy (donorObservable H) joint = energy (Matrix.kronecker (1 : Matrix ι ι ℂ) H)
      (Powered.Dynamics.systemReduce joint) := by
    simpa [donorObservable, energy, Matrix.kronecker] using outer
  rw [outerRead]
  have inner := Powered.Dynamics.jointEnergy_real_eq_reduced (0 : Matrix ι ι ℂ) H
    (Powered.Dynamics.systemReduce joint)
  simpa [energy, Matrix.kronecker, Powered.Dynamics.controllerReduce, Collision.bathReduce] using inner

theorem body_and_donor_energy (O : Matrix (ι × κ) (ι × κ) ℂ) (H : Matrix ι ι ℂ)
    (joint : Matrix ((ι × ι) × κ) ((ι × ι) × κ) ℂ) :
    energy (bodyObservable O + donorObservable H) joint = energy O (bodyRead joint) +
      energy H (Collision.bathReduce (Powered.Dynamics.systemReduce joint)) := by
  calc
    _ = energy (bodyObservable O) joint + energy (donorObservable H) joint := by
      simp only [energy, Matrix.add_mul, Matrix.trace_add, Complex.add_re]
    _ = _ := by rw [bodyObservable_energy, donorObservable_energy]

open scoped Matrix.Norms.L2Operator in
theorem exp_regroup (A : Matrix ((ι × κ) × ι) ((ι × κ) × ι) ℂ) :
    NormedSpace.exp (A.submatrix bodyReservoir bodyReservoir) =
      (NormedSpace.exp A).submatrix bodyReservoir bodyReservoir := by
  let : NormedAlgebra ℚ (Matrix ((ι × κ) × ι) ((ι × κ) × ι) ℂ) := .restrictScalars ℚ ℂ _
  let map := Matrix.reindexAlgEquiv ℂ ℂ (bodyReservoir (ι := ι) (κ := κ)).symm
  have continuous : Continuous map := map.toLinearMap.continuous_of_finiteDimensional
  exact (NormedSpace.map_exp map continuous A).symm

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Incidence
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
