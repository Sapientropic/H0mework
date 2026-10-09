import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MolecularFrame.Fields
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MolecularFrame.Normed
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Evolution.Consumer

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1MolecularFrame
noncomputable section
open CPS1ElectronicSource
open scoped Matrix InnerProductSpace
variable {frame : CPS1Recycling.Frame}

theorem nucleus_rank_lower (state : CPS1ElectronicSource.State frame) (nuclear : NuclearIndex state) :
    2 * spatialModes frame state.geometry.originJoint ≤ FiniteNormed.rank (𝕜 := ℂ) (rawField state) := by
  have lower := FiniteNormed.independent_subfamily_rank_le (𝕜 := ℂ) (rawField state)
    (fun index : ModeIndex state × Bool => ((nuclear,index.1),index.2))
    (nucleus_fields_independent state nuclear)
  simpa only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,ModeIndex,Nat.mul_comm] using lower

theorem generated_enough (state : CPS1ElectronicSource.State frame) (nuclear : NuclearIndex state) :
    electronCount frame state.geometry.originJoint ≤ FiniteNormed.rank (𝕜 := ℂ) (rawField state) := by
  have lower := nucleus_rank_lower state nuclear
  have count : electronCount frame state.geometry.originJoint ≤ 2 * spatialModes frame state.geometry.originJoint := by
    unfold spatialModes
    omega
  exact count.trans lower

def initialIndex (state : CPS1ElectronicSource.State frame)
    (enough : electronCount frame state.geometry.originJoint ≤ FiniteNormed.rank (𝕜 := ℂ) (rawField state))
    (slot : ElectronIndex state.geometry) : FiniteNormed.Index (𝕜 := ℂ) (rawField state) :=
  (Fintype.equivFin _).symm ⟨slot.val,lt_of_lt_of_le slot.isLt enough⟩

def initialOccupation (state : CPS1ElectronicSource.State frame)
    (enough : electronCount frame state.geometry.originJoint ≤ FiniteNormed.rank (𝕜 := ℂ) (rawField state)) :
    Matrix (FiniteNormed.Index (𝕜 := ℂ) (rawField state)) (ElectronIndex state.geometry) ℂ := by
  classical
  exact fun index slot => if index = initialIndex state enough slot then 1 else 0

theorem initial_index_injective (state : CPS1ElectronicSource.State frame)
    (enough : electronCount frame state.geometry.originJoint ≤ FiniteNormed.rank (𝕜 := ℂ) (rawField state)) :
    Function.Injective (initialIndex state enough) := by
  intro first second same
  have ordered := (Fintype.equivFin _).symm.injective same
  have values : first.val = second.val := congrArg
    (fun index : Fin (FiniteNormed.rank (𝕜 := ℂ) (rawField state)) => index.val) ordered
  exact Fin.ext values

theorem initial_occupation_gram (state : CPS1ElectronicSource.State frame)
    (enough : electronCount frame state.geometry.originJoint ≤ FiniteNormed.rank (𝕜 := ℂ) (rawField state)) :
    (initialOccupation state enough).conjTranspose * initialOccupation state enough = 1 := by
  classical
  ext first second
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,initialOccupation,apply_ite star,star_one,star_zero,
    ite_mul,one_mul,zero_mul]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  simp only [(initial_index_injective state enough).eq_iff,Matrix.one_apply]

end
end CPS1MolecularFrame
