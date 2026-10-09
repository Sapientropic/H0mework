import H0mework.Physics.LowEnergy.LightKernel.Graph
import H0mework.Physics.LowEnergy.LightKernel.Jet
import H0mework.Physics.LowEnergy.LightKernel.Characteristic
import H0mework.Physics.LowEnergy.LightKernel.Metric

set_option autoImplicit false
open SaturationMonoid.PhysicsCore.LowEnergy.LightKernel
open scoped Matrix
namespace LightKernelConsumer
noncomputable section

theorem source_phase_coordinates :
    first 1*ᵥ(![0,1,0,0,0] : Fin 5 → ℂ)=0 ∧
    first 1*ᵥ(![0,0,0,1,0] : Fin 5 → ℂ)=0 := by
  constructor <;> apply (source_first_kernel _).mpr <;> exact ⟨rfl,rfl⟩

theorem first_order_pair_nontrivial :
    first 1*ᵥ(![0,0,1,0,0] : Fin 5 → ℂ)≠0 := by
  intro zero
  have pair := (source_first_kernel _).mp zero
  exact one_ne_zero (show (1 : ℂ)=0 from pair.1)

theorem actual_metric_leg :
    core 1 1*ᵥmetricSolution 1 1=metricSource 1 ∧
      dotProduct (metricReader 1) (![0,0,1] : Fin 3 → ℂ)≠0 :=
  ⟨source_metric_solution 1 1 (by norm_num),source_axial_visible 1 (by norm_num)⟩

theorem actual_degree_eight :
    (blockPencil (2 : ℂ) 2).det=2^8*(rayReduced 1 1 2).det ∧ characteristic 1 1≠0 := by
  simpa using And.intro (ray_determinant_factor 1 1 2) first_characteristic_nonzero

theorem actual_quadratic_frequency :
    (quadraticReduced (5*Complex.I/6) 0).det=0 := by
  rw [quadratic_initial_determinant,quadratic_frequency_pair.1,mul_zero]

theorem actual_metric_source_and_contact :
    metricContact+dotProduct (metricReader 1) (metricSolution 1 1)/
      (SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse : ℂ)=metricLeading 1 1 :=
  original_metric_response 1 1 (by norm_num)

theorem actual_light_graph (A G : Matrix (Fin 56) (Fin 56) ℂ)
    (B : Matrix (Fin 56) (Fin 5) ℂ) (C : Matrix (Fin 5) (Fin 56) ℂ)
    (D : Matrix (Fin 5) (Fin 5) ℂ) (left : G*A=1) (right : A*G=1)
    (zeroSchur : D-C*G*B=0) (v : (Fin 56 ⊕ Fin 5) → ℂ) :
    (Matrix.fromBlocks A B C D*ᵥv=0 ↔ v=zeroGraph G B (fun i => v (.inr i))) := by
  constructor
  · exact kernel_is_zeroGraph A G B C D left v
  · intro same
    rw [same]
    exact zeroGraph_kernel A G B C D right zeroSchur _

end
end LightKernelConsumer

#print axioms LightKernelConsumer.source_phase_coordinates
#print axioms LightKernelConsumer.first_order_pair_nontrivial
#print axioms LightKernelConsumer.actual_metric_leg
#print axioms LightKernelConsumer.actual_degree_eight
#print axioms LightKernelConsumer.actual_quadratic_frequency
#print axioms LightKernelConsumer.actual_metric_source_and_contact
#print axioms LightKernelConsumer.actual_light_graph
