import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Source.SourceGeneratedReservoirFlow

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Incidence

open Powered.Dynamics
open scoped Matrix ComplexOrder
noncomputable section

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Two tensor associations of one body/environment/reservoir occurrence. -/
def bodyReservoir : ((ι × ι) × κ) ≃ ((ι × κ) × ι) where
  toFun x := ((x.1.1, x.2), x.1.2)
  invFun x := ((x.1.1, x.2), x.1.2)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

def receivedJoint (body : Matrix (ι × κ) (ι × κ) ℂ) (reservoir : Matrix ι ι ℂ) :
    Matrix ((ι × ι) × κ) ((ι × ι) × κ) ℂ :=
  (Matrix.kronecker body reservoir).submatrix bodyReservoir bodyReservoir

def bodyRead (joint : Matrix ((ι × ι) × κ) ((ι × ι) × κ) ℂ) : Matrix (ι × κ) (ι × κ) ℂ :=
  systemReduce (joint.submatrix bodyReservoir.symm bodyReservoir.symm)

theorem receivedJoint_positive (body : Matrix (ι × κ) (ι × κ) ℂ) (reservoir : Matrix ι ι ℂ)
    (bodyPositive : body.PosSemidef) (reservoirPositive : reservoir.PosSemidef) :
    (receivedJoint body reservoir).PosSemidef := (bodyPositive.kronecker reservoirPositive).submatrix _

theorem receivedJoint_trace (body : Matrix (ι × κ) (ι × κ) ℂ) (reservoir : Matrix ι ι ℂ) :
    (receivedJoint body reservoir).trace = body.trace * reservoir.trace := by
  exact (Equiv.sum_comp (bodyReservoir (ι := ι) (κ := κ))
    (fun i => (Matrix.kronecker body reservoir) i i)).trans (Matrix.trace_kronecker body reservoir)

omit [Fintype κ] in
theorem receivedJoint_body (body : Matrix (ι × κ) (ι × κ) ℂ) (reservoir : Matrix ι ι ℂ)
    (normalized : reservoir.trace = 1) : bodyRead (receivedJoint body reservoir) = body := by
  have restore : (receivedJoint body reservoir).submatrix bodyReservoir.symm bodyReservoir.symm =
      Matrix.kronecker body reservoir := by ext i j; rfl
  rw [bodyRead, restore, systemReduce_tensor, normalized, one_smul]

omit [Fintype ι] in
theorem receivedJoint_pair (body : Matrix (ι × κ) (ι × κ) ℂ) (reservoir : Matrix ι ι ℂ) :
    systemReduce (receivedJoint body reservoir) = Matrix.kronecker (systemReduce body) reservoir := by
  ext i j
  change (∑ e, body (i.1, e) (j.1, e) * reservoir i.2 j.2) =
    (∑ e, body (i.1, e) (j.1, e)) * reservoir i.2 j.2
  rw [Finset.sum_mul]

omit [Fintype κ] in
theorem receivedJoint_environment (body : Matrix (ι × κ) (ι × κ) ℂ) (reservoir : Matrix ι ι ℂ)
    (normalized : reservoir.trace = 1) :
    controllerReduce (receivedJoint body reservoir) = controllerReduce body := by
  ext e f
  change (∑ i : ι × ι, body (i.1, e) (i.1, f) * reservoir i.2 i.2) = ∑ i, body (i, e) (i, f)
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  change (∑ i, body (i, e) (i, f) * reservoir.trace) = _
  rw [normalized]
  simp

omit [Fintype κ] in
theorem bodyRead_positive (joint : Matrix ((ι × ι) × κ) ((ι × ι) × κ) ℂ)
    (positive : joint.PosSemidef) : (bodyRead joint).PosSemidef :=
  systemReduce_posSemidef _ (positive.submatrix _)

theorem bodyRead_trace (joint : Matrix ((ι × ι) × κ) ((ι × ι) × κ) ℂ) :
    (bodyRead joint).trace = joint.trace := by
  rw [bodyRead, systemReduce_trace]
  exact Equiv.sum_comp (bodyReservoir (ι := ι) (κ := κ)).symm (fun i => joint i i)

theorem bodyRead_pc (joint : Matrix ((ι × ι) × κ) ((ι × ι) × κ) ℂ) :
    systemReduce (bodyRead joint) = Collision.systemReduce (systemReduce joint) := by
  ext i j
  change (∑ e : κ, ∑ r : ι, joint ((i, r), e) ((j, r), e)) =
    ∑ r : ι, ∑ e : κ, joint ((i, r), e) ((j, r), e)
  rw [Finset.sum_comm]

omit [Fintype κ] in
theorem bodyRead_environment (joint : Matrix ((ι × ι) × κ) ((ι × ι) × κ) ℂ) :
    controllerReduce (bodyRead joint) = controllerReduce joint := by
  ext e f
  change (∑ i : ι, ∑ r : ι, joint ((i, r), e) ((i, r), f)) =
    ∑ ir : ι × ι, joint (ir, e) (ir, f)
  rw [Fintype.sum_prod_type]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Incidence
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
