import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Evolution.Response
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Evolution.Fields
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CPS1ElectronicEvolution.ContinuousCharge
open MeasureTheory
open scoped InnerProductSpace
noncomputable section
variable {X slots : Type*} [MeasurableSpace X] {measure : Measure X} [Fintype slots]

abbrev SpinSpace := PiLp 2 (fun _ : Bool => Lp ℂ 2 measure)

def weights (orbitals : slots → SpinSpace (measure := measure)) (x : X) (index : slots × Bool) : ℂ :=
  orbitals index.1 index.2 x

theorem component_integrable (orbital : SpinSpace (measure := measure)) (spin : Bool) :
    Integrable (fun x => star (orbital spin x) * orbital spin x) measure := by
  simpa only [RCLike.inner_apply,RCLike.star_def,mul_comm] using
    L2.integrable_inner (𝕜 := ℂ) (orbital spin) (orbital spin)

theorem component_integral (orbital : SpinSpace (measure := measure)) (spin : Bool) :
    (∫ x, star (orbital spin x) * orbital spin x ∂measure) =
      inner ℂ (orbital spin) (orbital spin) := by
  simp only [L2.inner_def,RCLike.inner_apply,RCLike.star_def,mul_comm]

theorem complete_integral (orbitals : slots → SpinSpace (measure := measure)) :
    (∫ x, Native.density (weights orbitals x) ∂measure) =
      ∑ slot, inner ℂ (orbitals slot) (orbitals slot) := by
  simp only [Native.density,weights,Fintype.sum_prod_type]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro slot _
    rw [integral_finsetSum]
    · simp only [component_integral,PiLp.inner_apply]
    · intro spin _
      exact component_integrable (orbitals slot) spin
  · intro slot _
    exact integrable_finsetSum _ (fun spin _ => component_integrable (orbitals slot) spin)

theorem normalized_total {count : Nat}
    (orbitals : Fin count → SpinSpace (measure := measure)) (orthogonal : Orthonormal ℂ orbitals) :
    (∫ x, Native.density (weights orbitals x) ∂measure) = (count : ℂ) := by
  rw [complete_integral]
  simp only [orthonormal_iff_ite.mp orthogonal,if_true,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,mul_one]

theorem generated_total {count : Nat}
    (orbitals : Fin count → SpinSpace (measure := measure)) (orthogonal : Orthonormal ℂ orbitals)
    (chart : X → SaturationMonoid.PhysicsCore.ProofFreeRicherAnholonomicSource.BasePoint) :
    (∫ x, Native.charge (weights orbitals x) (chart x) ∂measure) = -(count : ℂ) := by
  simp only [Native.complete_charge]
  rw [integral_neg,normalized_total orbitals orthogonal]

end
end CPS1ElectronicEvolution.ContinuousCharge
