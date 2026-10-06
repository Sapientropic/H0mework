import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationMoyalGroupedSource
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumMoyalCounts
open PreparationVacuumCanonicalMoyal
open scoped BigOperators

def slotIndex (s : Slot) : Fin 200 :=
  if s.2 then Fin.natAdd 100 s.1 else Fin.castAdd 100 s.1

theorem slotIndex_rawSlot (s : Fin 200) : slotIndex (rawSlot s)=s := by
  refine Fin.addCases (m:=100) (n:=100) ?_ ?_ s
  · intro i
    rw [rawSlot_q]
    rfl
  · intro i
    rw [rawSlot_p]
    rfl

theorem rawSlot_slotIndex (s : Slot) : rawSlot (slotIndex s)=s := by
  rcases s with ⟨i,b⟩
  cases b
  · exact rawSlot_q i
  · exact rawSlot_p i

def slotIndexEquiv : Slot ≃ Fin 200 where
  toFun := slotIndex
  invFun := rawSlot
  left_inv := rawSlot_slotIndex
  right_inv := slotIndex_rawSlot

def wordCounts {r : ℕ} (w : Word r) : Fin 200 →₀ ℕ :=
  ∑ i : Fin r,Finsupp.single (slotIndex (w i)) 1

def wordAlpha {r : ℕ} (w : Word r) : Multiindex := fun s => wordCounts w s

theorem wordAlpha_count {r : ℕ} (w : Word r) (s : Fin 200) :
    wordAlpha w s=(Finset.univ.filter (fun i : Fin r => slotIndex (w i)=s)).card := by
  classical
  simp only [wordAlpha,wordCounts,Finsupp.finsetSum_apply,Finsupp.single_apply]
  rw [Finset.card_eq_sum_ones,Finset.sum_filter]

theorem wordAlpha_total {r : ℕ} (w : Word r) : ∑ s : Fin 200,wordAlpha w s=r := by
  classical
  simp only [wordAlpha,wordCounts,Finsupp.finsetSum_apply]
  rw [Finset.sum_comm]
  simp

theorem wordAlpha_original {r : ℕ} (w : Word r) : wordAlpha w∈originalMultiindices r :=
  (originalMultiindices_mem r _).mpr (wordAlpha_total w)

theorem slotIndex_swap (s : Slot) : slotIndex (slotSwap s)=rawSwap (slotIndex s) := by
  rcases s with ⟨i,b⟩
  cases b
  · exact (rawSwap_q i).symm
  · exact (rawSwap_p i).symm

theorem wordAlpha_swap {r : ℕ} (w : Word r) :
    wordAlpha (wordSwap r w)=opposite (wordAlpha w) := by
  classical
  funext s
  rw [wordAlpha_count]
  change _=wordAlpha w (rawSwap s)
  rw [wordAlpha_count]
  congr 1
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  change slotIndex (slotSwap (w i))=s ↔ slotIndex (w i)=rawSwap s
  rw [slotIndex_swap]
  constructor
  · intro h
    simpa only [rawSwap_involution] using congrArg rawSwap h
  · intro h
    rw [h,rawSwap_involution]

def wordFiber (r : ℕ) (alpha : Multiindex) : Finset (Word r) :=
  Finset.univ.filter (fun w => wordAlpha w=alpha)

theorem contraction_word_partition (r : ℕ) (f g : Symbol) (zp : Phase) :
    contraction r f g zp=∑ alpha∈originalMultiindices r,
      ∑ w∈wordFiber r alpha,wordSign w*jet r f w zp*jet r g (wordSwap r w) zp := by
  classical
  unfold contraction wordFiber
  symm
  exact Finset.sum_fiberwise_of_maps_to (fun w _ => wordAlpha_original w) _

end LowEnergy.PreparationVacuumMoyalCounts
