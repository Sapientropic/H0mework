import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.Energy
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.Energy

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CPS1SameEventFunction
noncomputable section
open CPS1ElectronicSource CPS1ReactiveField.Carried CPS1AtomicDynamics
open scoped BigOperators InnerProductSpace Matrix

theorem external_kernel_differentiable (state : Snapshot) (p q : state.PrimitiveIndex)
    (spin : Bool) (position : Point) :
    DifferentiableAt ℝ (fun next => state.nuclearIntegral p q spin next) position := by
  unfold Snapshot.nuclearIntegral
  by_cases matching : (state.primitive p).spin = spin ∧ (state.primitive q).spin = spin
  · simp only [if_pos matching]
    let selected := fun next : Point => ![(state.primitive p).centre,(state.primitive q).centre,next]
    have smooth : DifferentiableAt ℝ selected position := by
      apply differentiableAt_pi.mpr
      intro index
      fin_cases index
      · exact differentiableAt_const _
      · exact differentiableAt_const _
      · exact differentiableAt_id
    exact (CPS1Deformation.multicentre_nuclear_hasFDerivAt
      (state.primitive p).mode (state.primitive q).mode 0 0 (selected position)).differentiableAt.comp position smooth
  · simp only [if_neg matching]
    exact differentiableAt_const 0

theorem electron_external_differentiable (state : Snapshot) (charge : ℝ) (position : Point) :
    DifferentiableAt ℝ (electronExternal state charge) position := by
  unfold electronExternal
  apply Complex.reCLM.differentiableAt.comp position
  apply DifferentiableAt.fun_sum
  intro electron _
  apply DifferentiableAt.const_mul
  apply DifferentiableAt.fun_sum
  intro spin _
  apply DifferentiableAt.fun_sum
  intro p _
  apply DifferentiableAt.fun_sum
  intro q _
  exact (external_kernel_differentiable state p q spin position).const_mul _

theorem nuclear_external_differentiable (state : Snapshot) (charge : ℝ) (position : Point)
    (separated : ∀ old ∈ state.nuclei, euclideanPoint position ≠ old.row.position) :
    DifferentiableAt ℝ (nuclearExternal state charge) position := by
  exact CPS1Deformation.differentiable_list_sum state.nuclei
    (fun old next => Coulomb.pairEnergy charge (old.particle.charge : ℝ)
      (euclideanPoint next) old.row.position) position
    (fun old held => ((Coulomb.pair_energy_derivative charge (old.particle.charge : ℝ)
      (euclideanPoint position) old.row.position (separated old held)).comp position
        CPS1Deformation.pointDifferential.hasFDerivAt).differentiableAt)

theorem external_energy_differentiable (state : Snapshot) (charge : ℝ) (position : Point)
    (separated : ∀ old ∈ state.nuclei, euclideanPoint position ≠ old.row.position) :
    DifferentiableAt ℝ (externalEnergy state charge) position :=
  (nuclear_external_differentiable state charge position separated).add
    (electron_external_differentiable state charge position)

theorem source_energy_direction (state : Snapshot) (node : Body.Node) (axis : Fin 3)
    (separated : ∀ old ∈ state.nuclei, node.row.position ≠ old.row.position) :
    HasDerivAt (fun time : ℝ => externalEnergy state (node.particle.charge : ℝ)
      ((fun coordinate => node.row.position coordinate) + time • Pi.single axis 1))
      (-(externalForce state node axis)) 0 := by
  have differentiable := external_energy_differentiable state (node.particle.charge : ℝ)
    (fun coordinate => node.row.position coordinate) separated
  let current : Point := fun coordinate => node.row.position coordinate
  let direction : Point := Pi.single axis 1
  have path : HasDerivAt (fun time : ℝ => current+time • direction) direction 0 := by
    simpa only [one_smul,id_eq,zero_add] using!
      (hasDerivAt_const (0 : ℝ) current).add ((hasDerivAt_id (0 : ℝ)).smul_const direction)
  have mother : HasFDerivAt (externalEnergy state (node.particle.charge : ℝ))
      (fderiv ℝ (externalEnergy state (node.particle.charge : ℝ)) current)
      (current+(0 : ℝ) • direction) := by
    simpa only [zero_smul,add_zero,current] using differentiable.hasFDerivAt
  have generated := mother.comp_hasDerivAt 0 path
  simpa only [externalForce,euclideanPoint,neg_neg,current,direction,Function.comp_apply] using! generated

end
end CPS1SameEventFunction
