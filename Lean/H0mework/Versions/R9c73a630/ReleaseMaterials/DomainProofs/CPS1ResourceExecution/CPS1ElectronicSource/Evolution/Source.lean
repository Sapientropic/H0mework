import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Orbitals
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Evolution.Continuation
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Evolution.Charge

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace CPS1ElectronicEvolution.Source
noncomputable section
open CPS1ElectronicSource
open scoped InnerProductSpace Matrix
variable {frame : CPS1Recycling.Frame}

theorem basis_orthonormal (geometry : Geometry frame) :
    Orthonormal ℂ (basis geometry) := by
  apply orthonormal_iff_ite.mpr
  rintro ⟨i,spin⟩ ⟨j,otherSpin⟩
  have spatial := orthonormal_iff_ite.mp
    (normalized_orthonormal (0 : Point) (spatialModes frame geometry.originJoint)) i j
  cases spin <;> cases otherSpin <;>
    simp [basis,PiLp.inner_apply,PiLp.single_apply]
  all_goals exact spatial

theorem occupiedIndex_injective (geometry : Geometry frame) :
    Function.Injective (occupiedIndex geometry) := by
  intro first second same
  have quotient : first.val/2 = second.val/2 :=
    congrArg (fun index : SpinIndex geometry => index.1.val) same
  have spin : decide (first.val%2=1) = decide (second.val%2=1) :=
    congrArg (fun index : SpinIndex geometry => index.2) same
  have odd : (first.val%2=1) ↔ (second.val%2=1) := by
    exact of_decide_eq_true (show decide ((first.val%2=1) ↔ (second.val%2=1)) = true by simp [spin])
  apply Fin.ext
  omega

theorem source_occupation (geometry : Geometry frame) :
    (occupation geometry).conjTranspose * occupation geometry = 1 := by
  ext first second
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,occupation,apply_ite star,star_one,star_zero,
    ite_mul,one_mul,zero_mul]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  simp only [(occupiedIndex_injective geometry).eq_iff,Matrix.one_apply]

def initialFields (geometry : Geometry frame) : ElectronIndex geometry → SpinSpace :=
  fields (basis geometry) (occupation geometry)

theorem initial_orthonormal (geometry : Geometry frame) : Orthonormal ℂ (initialFields geometry) :=
  occupied_fields _ (basis_orthonormal geometry) _ (source_occupation geometry)

theorem initial_slater (geometry : Geometry frame) :
    slaterDual (initialFields geometry) (slater (initialFields geometry)) = 1 :=
  slater_normalized _ (initial_orthonormal geometry)

theorem initial_charge (geometry : Geometry frame)
    (chart : Point → SaturationMonoid.PhysicsCore.ProofFreeRicherAnholonomicSource.BasePoint) :
    (∫ x, Native.charge (ContinuousCharge.weights (initialFields geometry) x) (chart x)) =
      -(electronCount frame geometry.originJoint : ℂ) :=
  ContinuousCharge.generated_total _ (initial_orthonormal geometry) chart

end
end CPS1ElectronicEvolution.Source
