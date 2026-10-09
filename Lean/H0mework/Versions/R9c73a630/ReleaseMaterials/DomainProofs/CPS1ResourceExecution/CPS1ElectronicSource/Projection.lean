import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Accounting
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Evolution.Consumer
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Evolution.Particles

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1ElectronicSource
noncomputable section
open scoped Matrix InnerProductSpace
open CPS1ElectronicEvolution
variable {frame : CPS1Recycling.Frame}

def projectedAction (state : State frame) : SpinSpace →ₗ[ℂ] SpinSpace where
  toFun field := ∑ i, (∑ j, state.hamiltonian i j * inner ℂ (basis state.geometry j) field) • basis state.geometry i
  map_add' first second := by
    simp only [inner_add_right,mul_add,Finset.sum_add_distrib,add_smul]
  map_smul' scalar field := by
    simp only [inner_smul_right,RingHom.id_apply]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_smul]
    apply congrArg (fun coefficient : ℂ => coefficient • basis state.geometry i)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

theorem projected_fields (state : State frame)
    (occupied : Matrix (SpinIndex state.geometry) (ElectronIndex state.geometry) ℂ)
    (slot : ElectronIndex state.geometry) :
    projectedAction state (fields (basis state.geometry) occupied slot) =
      fields (basis state.geometry) (state.hamiltonian * occupied) slot := by
  change (∑ i, (∑ j, state.hamiltonian i j *
      inner ℂ (basis state.geometry j) (fields (basis state.geometry) occupied slot)) • basis state.geometry i) = _
  simp only [fields,(Source.basis_orthonormal state.geometry).inner_right_fintype,Matrix.mul_apply]

theorem projected_basis (state : State frame) (first second : SpinIndex state.geometry) :
    inner ℂ (basis state.geometry first) (projectedAction state (basis state.geometry second)) =
      state.hamiltonian first second := by
  change inner ℂ (basis state.geometry first)
      (∑ i, (∑ j, state.hamiltonian i j *
        inner ℂ (basis state.geometry j) (basis state.geometry second)) • basis state.geometry i) = _
  rw [(Source.basis_orthonormal state.geometry).inner_right_fintype]
  simp only [orthonormal_iff_ite.mp (Source.basis_orthonormal state.geometry),mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,if_true]

theorem fields_add {n m E : Type*} [Fintype n] [DecidableEq n]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (basis : n → E) (first second : Matrix n m ℂ) (slot : m) :
    fields basis (first+second) slot = fields basis first slot + fields basis second slot := by
  simp only [fields,Matrix.add_apply,add_smul,Finset.sum_add_distrib]

theorem fields_sub {n m E : Type*} [Fintype n] [DecidableEq n]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (basis : n → E) (first second : Matrix n m ℂ) (slot : m) :
    fields basis (first-second) slot = fields basis first slot-fields basis second slot := by
  simp only [fields,Matrix.sub_apply,sub_smul,Finset.sum_sub_distrib]

theorem fields_smul {n m E : Type*} [Fintype n] [DecidableEq n]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (basis : n → E) (scalar : ℂ) (occupied : Matrix n m ℂ) (slot : m) :
    fields basis (scalar • occupied) slot = scalar • fields basis occupied slot := by
  simp only [fields,Matrix.smul_apply,smul_eq_mul,mul_smul,Finset.smul_sum]

theorem projected_midpoint (state : State frame) (time : ℝ) (slot : ElectronIndex state.geometry) :
    let updated := occupiedUpdate state.hamiltonian (time/2) state.occupied
    let before := fields (basis state.geometry) state.occupied slot
    let after := fields (basis state.geometry) updated slot
    after + (Complex.I * ((time/2 : ℝ) : ℂ)) • projectedAction state after =
      before - (Complex.I * ((time/2 : ℝ) : ℂ)) • projectedAction state before := by
  dsimp only
  let updated := occupiedUpdate state.hamiltonian (time/2) state.occupied
  have matrix : updated + (Complex.I * ((time/2 : ℝ) : ℂ)) • (state.hamiltonian * updated) =
      state.occupied - (Complex.I * ((time/2 : ℝ) : ℂ)) • (state.hamiltonian * state.occupied) := by
    have equation := congrArg (fun operator => operator * state.occupied)
      (actual_equation state.hamiltonian (source_hamiltonian_hermitian state) (time/2))
    simpa only [denominator,generator,Matrix.add_mul,Matrix.sub_mul,Matrix.one_mul,Matrix.smul_mul,
      Matrix.mul_assoc,occupiedUpdate,updated] using equation
  have continuous := congrArg (fun occupied => fields (basis state.geometry) occupied slot) matrix
  rw [fields_add,fields_sub,fields_smul,fields_smul] at continuous
  rw [projected_fields,projected_fields]
  exact continuous

theorem same_native_net_charge (state : State frame) (generated : Consumer.Good state)
    (chart : Point → SaturationMonoid.PhysicsCore.ProofFreeRicherAnholonomicSource.BasePoint) :
    (SourceCharge.nuclearCharge (CPS1EnzymeBath.Joint.particles frame state.geometry.originJoint) : ℂ) +
      (∫ x, Native.charge (ContinuousCharge.weights (Consumer.occupiedFields state) x) (chart x)) =
      (CPS1EnzymeBath.Joint.charge frame state.geometry.originJoint : ℂ) := by
  rw [Consumer.source_charge state generated chart]
  have count : electronCount frame state.geometry.originJoint =
      SourceCharge.electronCount (CPS1EnzymeBath.Joint.particles frame state.geometry.originJoint) := rfl
  rw [count]
  have source := SourceCharge.same_current_charge frame state.geometry.originJoint
  rw [CPS1EnzymeBath.Joint.particle_charge] at source
  exact_mod_cast source

end
end CPS1ElectronicSource
