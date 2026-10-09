import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MolecularFrame.Payment

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1MolecularFrame
noncomputable section
open CPS1ElectronicSource CPS1ElectronicEvolution
open scoped Matrix InnerProductSpace BigOperators
variable {frame : CPS1Recycling.Frame}

def Material.action (state : Material frame) : SpinSpace →L[ℂ] SpinSpace :=
  ∑ first, ∑ second, state.hamiltonian first second •
    (innerSL ℂ (FiniteNormed.field (𝕜 := ℂ) (rawField state.reference) second)).smulRight
      (FiniteNormed.field (𝕜 := ℂ) (rawField state.reference) first)

theorem material_action_fields (state : Material frame)
    (occupied : Matrix (MolecularIndex state.reference) (ElectronIndex state.reference.geometry) ℂ)
    (slot : ElectronIndex state.reference.geometry) :
    state.action (fields (FiniteNormed.field (𝕜 := ℂ) (rawField state.reference)) occupied slot) =
      fields (FiniteNormed.field (𝕜 := ℂ) (rawField state.reference)) (state.hamiltonian * occupied) slot := by
  simp only [Material.action,sum_apply,smul_apply,ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply,fields,(FiniteNormed.field_orthonormal (rawField state.reference)).inner_right_fintype,
    Matrix.mul_apply,smul_smul,Finset.sum_smul]

theorem generated_midpoint (state : Material frame) (time : ℝ) (slot : ElectronIndex state.reference.geometry) :
    let before := state.currentFields slot
    let after := fields (FiniteNormed.field (𝕜 := ℂ) (rawField state.reference))
      (occupiedUpdate state.hamiltonian (time/2) state.occupied) slot
    after + (Complex.I * ((time/2 : ℝ) : ℂ)) • state.action after =
      before - (Complex.I * ((time/2 : ℝ) : ℂ)) • state.action before := by
  dsimp only
  have matrix := congrArg (fun operator => operator * state.occupied)
    (actual_equation state.hamiltonian (material_hamiltonian_hermitian state) (time/2))
  have paid : occupiedUpdate state.hamiltonian (time/2) state.occupied +
      (Complex.I * ((time/2 : ℝ) : ℂ)) •
        (state.hamiltonian * occupiedUpdate state.hamiltonian (time/2) state.occupied) =
      state.occupied - (Complex.I * ((time/2 : ℝ) : ℂ)) • (state.hamiltonian * state.occupied) := by
    simpa only [denominator,generator,Matrix.add_mul,Matrix.sub_mul,Matrix.one_mul,Matrix.smul_mul,
      Matrix.mul_assoc,occupiedUpdate] using matrix
  have continuous := congrArg (fun occupied =>
    fields (FiniteNormed.field (𝕜 := ℂ) (rawField state.reference)) occupied slot) paid
  rw [CPS1ElectronicSource.fields_add,CPS1ElectronicSource.fields_sub,
    CPS1ElectronicSource.fields_smul,CPS1ElectronicSource.fields_smul] at continuous
  change _ + _ = fields (FiniteNormed.field (𝕜 := ℂ) (rawField state.reference)) state.occupied slot -
    (Complex.I * ((time/2 : ℝ) : ℂ)) •
      state.action (fields (FiniteNormed.field (𝕜 := ℂ) (rawField state.reference)) state.occupied slot)
  rw [material_action_fields,material_action_fields]
  exact continuous

theorem actual_midpoint (state next : Material frame) (time : ℝ)
    (actual : state.pulse? time = .ok next) :
    let after := fields (FiniteNormed.field (𝕜 := ℂ) (rawField state.reference))
      (occupiedUpdate state.hamiltonian (time/2) state.occupied)
    HEq next.currentFields after ∧ ∀ slot : ElectronIndex state.reference.geometry,
      after slot + (Complex.I * ((time/2 : ℝ) : ℂ)) • state.action (after slot) =
        state.currentFields slot - (Complex.I * ((time/2 : ℝ) : ℂ)) • state.action (state.currentFields slot) := by
  obtain ⟨same,_,_,_⟩ := pulse_outcome state next time actual
  rw [same]
  exact ⟨HEq.rfl,generated_midpoint state time⟩

theorem material_charge (state : Material frame) (generated : Good state)
    (chart : Point → SaturationMonoid.PhysicsCore.ProofFreeRicherAnholonomicSource.BasePoint) :
    (∫ x, Native.charge (ContinuousCharge.weights state.currentFields x) (chart x)) =
      -(electronCount frame state.reference.geometry.originJoint : ℂ) :=
  ContinuousCharge.generated_total _ (material_fields state generated) chart

end
end CPS1MolecularFrame
