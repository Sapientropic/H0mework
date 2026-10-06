import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationMoyalSourceSmooth
import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationMoyalWordSigns

set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumMoyalSymmetry
open PreparationVacuumCanonicalMoyal PreparationVacuumMoyalCounts
open scoped BigOperators

theorem rawSlot_eq (s : Fin 200) (v : Slot) : rawSlot s=v ↔ s=slotIndex v := by
  constructor
  · intro equality
    simpa only [slotIndex_rawSlot] using congrArg slotIndex equality
  · intro equality
    rw [equality,rawSlot_slotIndex]

theorem list_count_ofFn (r : ℕ) (w : Word r) (v : Slot) :
    (List.ofFn w).count v=∑ i : Fin r,if w i=v then 1 else 0 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [List.ofFn_succ,List.count_cons,Fin.sum_univ_succ,ih]
    simp only [beq_iff_eq]
    split_ifs <;> omega

theorem word_list_count {r : ℕ} (w : Word r) (v : Slot) :
    (List.ofFn w).count v=wordAlpha w (slotIndex v) := by
  classical
  rw [list_count_ofFn]
  simp only [wordAlpha,wordCounts,Finsupp.finsetSum_apply,Finsupp.single_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact propext (slotIndexEquiv.injective.eq_iff).symm

theorem canonicalWord_count (alpha : Multiindex) (v : Slot) :
    (canonicalWord alpha).count v=alpha (slotIndex v) := by
  classical
  have generic (n : ℕ) (a : Fin n → ℕ) (s : Fin n → Slot) (v : Slot) :
      (List.ofFn fun i => List.replicate (a i) (s i)).flatten.count v=
        ∑ i : Fin n,if s i=v then a i else 0 := by
    simp only [List.count_flatten,List.map_ofFn,List.sum_ofFn,Function.comp_apply,
      List.count_replicate,beq_iff_eq]
  rw [canonicalWord,generic]
  simp only [rawSlot_eq,Finset.sum_ite_eq',Finset.mem_univ,if_true]

theorem word_canonical_permutation {r : ℕ} (w : Word r) :
    (List.ofFn w).Perm (canonicalWord (wordAlpha w)) := by
  apply List.perm_iff_count.mpr
  intro v
  rw [word_list_count,canonicalWord_count]

theorem canonicalJet_list (d : Fin 3) (j : Fin 14) (alpha : Multiindex)
    (zp : Phase) (physical : zp∈originalPhysicalPhase) :
    canonicalJet alpha (originalLeaf d j) zp=
      listJet ((canonicalWord alpha).map slotDirection) (originalLeaf d j) zp := by
  unfold canonicalJet
  dsimp only
  rw [←listJet_ofFn originalPhysicalPhase_open (originalLeaf_smoothOn d j)
    (canonicalWord alpha).length (fun i => slotDirection ((canonicalWord alpha).get i)) zp physical]
  congr 1
  change List.ofFn (slotDirection∘(canonicalWord alpha).get)=_
  rw [←List.map_ofFn]
  exact congrArg (List.map slotDirection) List.ofFn_getElem

theorem originalLeaf_word_jet (d : Fin 3) (j : Fin 14) (r : ℕ) (w : Word r)
    (zp : Phase) (physical : zp∈originalPhysicalPhase) :
    jet r (originalLeaf d j) w zp=canonicalJet (wordAlpha w) (originalLeaf d j) zp := by
  rw [canonicalJet_list d j _ zp physical]
  unfold jet
  rw [←listJet_ofFn originalPhysicalPhase_open (originalLeaf_smoothOn d j) r
    (fun a => slotDirection (w a)) zp physical]
  change listJet (List.ofFn (slotDirection∘w)) (originalLeaf d j) zp=_
  rw [←List.map_ofFn]
  exact listJet_perm originalPhysicalPhase_open (originalLeaf_smoothOn d j)
    ((word_canonical_permutation w).map slotDirection) physical

theorem originalN0Coefficient_grouped (r : ℕ) (d e : Fin 3) (j k : Fin 14)
    (zp : Phase) (physical : zp∈originalPhysicalPhase) :
    originalN0Coefficient r d e j k zp=originalGroupedN0Coefficient r d e j k zp := by
  unfold originalN0Coefficient coefficient
  rw [contraction_word_partition]
  rw [Complex.ofReal_sum,Finset.mul_sum]
  unfold originalGroupedN0Coefficient groupedCoefficient
  apply Finset.sum_congr rfl
  intro alpha present
  have term (w : Word r) (inside : w∈wordFiber r alpha) :
      ((wordSign w*jet r (originalLeaf d j) w zp*
        jet r (originalLeaf e k) (wordSwap r w) zp : ℝ) : ℂ)=
      (-1 : ℂ)^(∑ s : Fin 100,alpha (Fin.natAdd 100 s))*
        (canonicalJet alpha (originalLeaf d j) zp : ℂ)*
        (canonicalJet (opposite alpha) (originalLeaf e k) zp : ℂ) := by
    have identity : wordAlpha w=alpha := (Finset.mem_filter.mp inside).2
    rw [wordSign_original_p,originalLeaf_word_jet d j r w zp physical,
      originalLeaf_word_jet e k r (wordSwap r w) zp physical,wordAlpha_swap,identity]
    push_cast
    rfl
  rw [Complex.ofReal_sum]
  rw [Finset.sum_congr rfl term]
  simp only [Finset.sum_const,nsmul_eq_mul]
  have weight := source_grouped_weight_from_words r alpha present
  calc
    _=(Complex.I/2)^r/(r.factorial : ℂ)*
        (-1 : ℂ)^(∑ s : Fin 100,alpha (Fin.natAdd 100 s))*(wordFiber r alpha).card*
          (canonicalJet alpha (originalLeaf d j) zp : ℂ)*
          (canonicalJet (opposite alpha) (originalLeaf e k) zp : ℂ) := by ring
    _=_ := by rw [weight]

end LowEnergy.PreparationVacuumMoyalSymmetry
