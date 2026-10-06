import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationMoyalSourceLeaves
import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.Data.List.OfFn

set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumCanonicalMoyal
open PreparationActualFactor
open scoped BigOperators

abbrev Multiindex := Fin 200 → ℕ

def rawSlot (s : Fin 200) : Slot :=
  if h : s.val<100 then (⟨s.val,h⟩,false) else (⟨s.val-100,by omega⟩,true)

def rawSwap (s : Fin 200) : Fin 200 :=
  if h : s.val<100 then ⟨s.val+100,by omega⟩ else ⟨s.val-100,by omega⟩

def opposite (alpha : Multiindex) : Multiindex := fun s => alpha (rawSwap s)

def canonicalWord (alpha : Multiindex) : List Slot :=
  (List.ofFn fun s : Fin 200 => List.replicate (alpha s) (rawSlot s)).flatten

def canonicalJet (alpha : Multiindex) (f : Symbol) (zp : Phase) : ℝ :=
  let word := canonicalWord alpha
  iteratedFDeriv ℝ word.length f zp (fun i => slotDirection (word.get i))

def originalMultiindices (r : ℕ) : Finset Multiindex := Finset.Nat.antidiagonalTuple 200 r

def groupedWeight (r : ℕ) (alpha : Multiindex) : ℂ :=
  (Complex.I/2)^r*(-1 : ℂ)^(∑ i : Fin 100,alpha (Fin.natAdd 100 i))/
    ∏ s : Fin 200,(alpha s).factorial

-- Exactly the grouped SourceEvaluator.moyal_differential carrier and weight:
-- alpha contains q-left,p-left; opposite alpha contains p-right,q-right.
def groupedCoefficient (r : ℕ) (f g : Symbol) (zp : Phase) : ℂ :=
  ∑ alpha ∈ originalMultiindices r,
    groupedWeight r alpha*(canonicalJet alpha f zp : ℂ)*
      (canonicalJet (opposite alpha) g zp : ℂ)

def originalGroupedN0Coefficient (r : ℕ) (d e : Fin 3) (j k : Fin 14) : Phase → ℂ :=
  groupedCoefficient r (originalLeaf d j) (originalLeaf e k)

def originalFinitePrefix (depth : ℕ) (d e : Fin 3) (j k : Fin 14) (zp : Phase) : ℂ :=
  ∑ r ∈ Finset.range (depth+1),originalGroupedN0Coefficient r d e j k zp

theorem rawSwap_q (i : Fin 100) : rawSwap (Fin.castAdd 100 i)=Fin.natAdd 100 i := by
  apply Fin.ext
  simp [rawSwap]

theorem rawSwap_p (i : Fin 100) : rawSwap (Fin.natAdd 100 i)=Fin.castAdd 100 i := by
  apply Fin.ext
  simp [rawSwap]

theorem rawSlot_q (i : Fin 100) : rawSlot (Fin.castAdd 100 i)=(i,false) := by
  unfold rawSlot
  simp

theorem rawSlot_p (i : Fin 100) : rawSlot (Fin.natAdd 100 i)=(i,true) := by
  unfold rawSlot
  simp

theorem rawSwap_involution (s : Fin 200) : rawSwap (rawSwap s)=s := by
  refine Fin.addCases (m:=100) (n:=100) ?_ ?_ s
  · intro i
    rw [rawSwap_q,rawSwap_p]
  · intro i
    rw [rawSwap_p,rawSwap_q]

theorem rawSlot_swap (s : Fin 200) : rawSlot (rawSwap s)=slotSwap (rawSlot s) := by
  refine Fin.addCases (m:=100) (n:=100) ?_ ?_ s
  · intro i
    rw [rawSwap_q,rawSlot_p,rawSlot_q]
    rfl
  · intro i
    rw [rawSwap_p,rawSlot_q,rawSlot_p]
    rfl

theorem originalMultiindices_mem (r : ℕ) (alpha : Multiindex) :
    alpha∈originalMultiindices r ↔ ∑ s : Fin 200,alpha s=r :=
  Finset.Nat.mem_antidiagonalTuple

theorem canonicalWord_length (alpha : Multiindex) :
    (canonicalWord alpha).length=∑ s : Fin 200,alpha s := by
  have generic (n : ℕ) (a : Fin n → ℕ) (v : Fin n → Slot) :
      (List.ofFn fun s => List.replicate (a s) (v s)).flatten.length=∑ s : Fin n,a s := by
    simp only [List.length_flatten,List.map_ofFn,List.sum_ofFn,Function.comp_apply,List.length_replicate]
  exact generic 200 alpha rawSlot

theorem canonicalWord_original_order (r : ℕ) (alpha : Multiindex)
    (present : alpha∈originalMultiindices r) : (canonicalWord alpha).length=r := by
  rw [canonicalWord_length]
  exact (originalMultiindices_mem r alpha).mp present

theorem canonicalWord_zero : canonicalWord (0 : Multiindex)=[] := by
  simp [canonicalWord]

theorem canonicalJet_zero (f : Symbol) (zp : Phase) : canonicalJet 0 f zp=f zp := by
  unfold canonicalJet
  rw [canonicalWord_zero]
  exact iteratedFDeriv_zero_apply _

theorem opposite_zero : opposite (0 : Multiindex)=0 := rfl

theorem groupedWeight_zero : groupedWeight 0 (0 : Multiindex)=1 := by
  simp [groupedWeight]

theorem groupedCoefficient_zero (f g : Symbol) (zp : Phase) :
    groupedCoefficient 0 f g zp=(f zp : ℂ)*(g zp : ℂ) := by
  simp only [groupedCoefficient,originalMultiindices,Finset.Nat.antidiagonalTuple_zero_right,
    Finset.sum_singleton,opposite_zero,groupedWeight_zero,canonicalJet_zero,one_mul]

theorem originalGroupedN0Coefficient_zero (d e : Fin 3) (j k : Fin 14) (zp : Phase) :
    originalGroupedN0Coefficient 0 d e j k zp=originalN0Coefficient 0 d e j k zp := by
  rw [originalN0Coefficient_zero]
  exact groupedCoefficient_zero _ _ _

theorem canonicalJet_zero_symbol (alpha : Multiindex) (zp : Phase) :
    canonicalJet alpha (fun _ => 0) zp=0 := by
  simp [canonicalJet,iteratedFDeriv_fun_zero]

theorem originalGroupedN0Coefficient_Y_left (r : ℕ) (d e : Fin 3) (k : Fin 14) (zp : Phase) :
    originalGroupedN0Coefficient r d e (Fin.last 13) k zp=0 := by
  simp only [originalGroupedN0Coefficient,originalLeaf_Y_zero,groupedCoefficient,
    canonicalJet_zero_symbol,Complex.ofReal_zero,mul_zero,zero_mul,Finset.sum_const_zero]

theorem originalGroupedN0Coefficient_Y_right (r : ℕ) (d e : Fin 3) (j : Fin 14) (zp : Phase) :
    originalGroupedN0Coefficient r d e j (Fin.last 13) zp=0 := by
  simp only [originalGroupedN0Coefficient,originalLeaf_Y_zero,groupedCoefficient,
    canonicalJet_zero_symbol,Complex.ofReal_zero,mul_zero,Finset.sum_const_zero]

theorem originalFinitePrefix_succ (depth : ℕ) (d e : Fin 3) (j k : Fin 14) (zp : Phase) :
    originalFinitePrefix (depth+1) d e j k zp=originalFinitePrefix depth d e j k zp+
      originalGroupedN0Coefficient (depth+1) d e j k zp := by
  exact Finset.sum_range_succ _ _

end LowEnergy.PreparationVacuumCanonicalMoyal
