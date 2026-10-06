import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationMoyalMultiplicity
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumMoyalCounts
open PreparationVacuumCanonicalMoyal
open scoped BigOperators

theorem wordSign_counts {r : ℕ} (w : Word r) :
    wordSign w=∏ s : Fin 200,slotSign (rawSlot s)^(wordAlpha w s) := by
  have grouped := Finset.prod_fiberwise' (Finset.univ : Finset (Fin r))
    (fun i => slotIndex (w i)) (fun s : Fin 200 => slotSign (rawSlot s))
  simp only [Finset.prod_const,rawSlot_slotIndex,←wordAlpha_count] at grouped
  exact grouped.symm

theorem original_p_sign (alpha : Multiindex) :
    (∏ s : Fin 200,slotSign (rawSlot s)^(alpha s))=
      (-1 : ℝ)^(∑ i : Fin 100,alpha (Fin.natAdd 100 i)) := by
  rw [Fin.prod_univ_add (a:=100) (b:=100)]
  simp only [rawSlot_q,rawSlot_p,slotSign,Bool.false_eq_true,ite_false,one_pow,
    ite_true,Finset.prod_const_one,one_mul]
  exact Finset.prod_pow_eq_pow_sum _ _ _

theorem wordSign_original_p {r : ℕ} (w : Word r) :
    wordSign w=(-1 : ℝ)^(∑ i : Fin 100,wordAlpha w (Fin.natAdd 100 i)) := by
  rw [wordSign_counts,original_p_sign]

theorem source_grouped_weight_from_words (r : ℕ) (alpha : Multiindex)
    (present : alpha∈originalMultiindices r) :
    (Complex.I/2)^r/(r.factorial : ℂ)*
      (-1 : ℂ)^(∑ i : Fin 100,alpha (Fin.natAdd 100 i))*(wordFiber r alpha).card=
        groupedWeight r alpha := by
  have ratio := source_multiplicity_complex_weight r alpha present
  unfold groupedWeight
  push_cast
  calc
    _ = (Complex.I/2)^r*(-1 : ℂ)^(∑ i : Fin 100,alpha (Fin.natAdd 100 i))*
        ((wordFiber r alpha).card/(r.factorial : ℂ)) := by ring
    _ = _ := by rw [ratio]; ring

end LowEnergy.PreparationVacuumMoyalCounts
