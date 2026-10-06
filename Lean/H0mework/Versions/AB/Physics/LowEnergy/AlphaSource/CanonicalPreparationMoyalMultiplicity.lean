import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationMoyalWordCounts
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Multinomial

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumMoyalCounts
open PreparationVacuumCanonicalMoyal
open scoped BigOperators

def alphaFinsupp (alpha : Multiindex) : Fin 200 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm alpha

theorem alphaFinsupp_apply (alpha : Multiindex) (s : Fin 200) : alphaFinsupp alpha s=alpha s := rfl

theorem wordCounts_eq_alpha {r : ℕ} (w : Word r) (alpha : Multiindex) :
    wordCounts w=alphaFinsupp alpha ↔ wordAlpha w=alpha := by
  constructor
  · intro h
    funext s
    exact congrArg (fun d : Fin 200 →₀ ℕ => d s) h
  · intro h
    apply Finsupp.ext
    intro s
    exact congrFun h s

theorem original_word_monomial {r : ℕ} (w : Word r) :
    (∏ i : Fin r,(MvPolynomial.X (slotIndex (w i)) : MvPolynomial (Fin 200) ℕ))=
      MvPolynomial.monomial (wordCounts w) 1 := by
  have single (i : Fin r) :
      MvPolynomial.monomial (Finsupp.single (slotIndex (w i)) 1) (1 : ℕ)=
        MvPolynomial.X (slotIndex (w i)) := by
    rw [←MvPolynomial.X_pow_eq_monomial,pow_one]
  simpa only [wordCounts,Finset.prod_const_one,single] using
    (MvPolynomial.monomial_sum_prod Finset.univ
      (fun i : Fin r => Finsupp.single (slotIndex (w i)) 1) (fun _ => (1 : ℕ))).symm

theorem original_word_polynomial (r : ℕ) :
    (∑ s : Fin 200,(MvPolynomial.X s : MvPolynomial (Fin 200) ℕ))^r=
      ∑ w : Word r,MvPolynomial.monomial (wordCounts w) 1 := by
  rw [←slotIndexEquiv.sum_comp (fun s : Fin 200 =>
    (MvPolynomial.X s : MvPolynomial (Fin 200) ℕ)),Fintype.sum_pow]
  exact Finset.sum_congr rfl (fun w _ => original_word_monomial w)

theorem original_fiber_coefficient (r : ℕ) (alpha : Multiindex) :
    MvPolynomial.coeff (alphaFinsupp alpha)
      ((∑ s : Fin 200,(MvPolynomial.X s : MvPolynomial (Fin 200) ℕ))^r)=
      (wordFiber r alpha).card := by
  classical
  rw [original_word_polynomial,MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial,wordCounts_eq_alpha]
  rw [wordFiber,Finset.card_eq_sum_ones,Finset.sum_filter]

theorem source_multiplicity (r : ℕ) (alpha : Multiindex)
    (present : alpha∈originalMultiindices r) :
    (wordFiber r alpha).card=Nat.multinomial Finset.univ alpha := by
  classical
  have total : (alphaFinsupp alpha).sum (fun _ m => m)=r := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    simp only [alphaFinsupp_apply]
    exact (originalMultiindices_mem r alpha).mp present
  rw [←original_fiber_coefficient,MvPolynomial.coeff_sum_X_pow_of_fintype,if_pos total,
    Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _)]
  rfl

theorem source_multiplicity_factorials (r : ℕ) (alpha : Multiindex)
    (present : alpha∈originalMultiindices r) :
    (∏ s : Fin 200,(alpha s).factorial)*(wordFiber r alpha).card=r.factorial := by
  rw [source_multiplicity r alpha present]
  have original := Nat.multinomial_spec Finset.univ alpha
  rw [(originalMultiindices_mem r alpha).mp present] at original
  exact original

theorem source_multiplicity_complex_weight (r : ℕ) (alpha : Multiindex)
    (present : alpha∈originalMultiindices r) :
    ((wordFiber r alpha).card : ℂ)/(r.factorial : ℂ)=
      1/(∏ s : Fin 200,((alpha s).factorial : ℂ)) := by
  have positive : (r.factorial : ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r)
  have nonzero : (∏ s : Fin 200,((alpha s).factorial : ℂ))≠0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro s _
    exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have paid := congrArg (fun n : ℕ => (n : ℂ)) (source_multiplicity_factorials r alpha present)
  push_cast at paid
  apply (div_eq_div_iff positive nonzero).mpr
  linear_combination paid

end LowEnergy.PreparationVacuumMoyalCounts
