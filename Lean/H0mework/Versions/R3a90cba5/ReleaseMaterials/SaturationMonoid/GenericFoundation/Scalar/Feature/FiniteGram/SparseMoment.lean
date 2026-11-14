import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Polynomial.Roots

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedFiniteGram.SparseMoment

open scoped Matrix BigOperators
open Matrix

universe u v
variable {I : Type u} {K : Type v} [Field K]

/-- The source coefficients are read through powers of their actual clock coordinates. -/
def moments (clock : I → K) (source : I →₀ K) (degree : Nat) : K :=
  source.sum fun site weight => weight * clock site ^ degree

def measure (clock : I → K) (source : I →₀ K) (bound : Nat) : Fin (bound+bound) → K :=
  fun i => moments clock source i.val

def hankel (data : Nat → K) (rank : Nat) : Matrix (Fin rank) (Fin rank) K :=
  Matrix.of (fun i j => data (i.val+j.val))

private def padded {bound : Nat} (data : Fin (bound+bound) → K) (n : Nat) : K :=
  if within : n < bound+bound then data ⟨n,within⟩ else 0

private theorem padded_prefix (clock : I → K) (source : I →₀ K) {bound n : Nat}
    (within : n < bound+bound) :
    padded (measure clock source bound) n = moments clock source n := by
  simp only [padded,dif_pos within,measure]

/-- Scan leading Hankel determinants for the last nonsingular size. -/
def order {bound : Nat} (data : Fin (bound+bound) → K) : Nat :=
  open Classical in
  ((Finset.range (bound+1)).filter (fun rank => (hankel (padded data) rank).det ≠ 0)).sup id

private def slots (sites : Finset I) : Fin sites.card → sites := sites.equivFin.symm

private def powers {rank : Nat} (values : Fin rank → K) (width : Nat) :
    Matrix (Fin width) (Fin rank) K :=
  Matrix.of (fun i j => values j ^ i.val)

private theorem powers_square {rank : Nat} (values : Fin rank → K) :
    powers values rank = (vandermonde values)ᵀ := rfl

private theorem powers_det {rank : Nat} (values : Fin rank → K) (distinct : Function.Injective values) :
    (powers values rank).det ≠ 0 := by
  rw [powers_square,det_transpose]
  exact det_vandermonde_ne_zero_iff.mpr distinct

private theorem support_moment (clock : I → K) (source : I →₀ K) (degree : Nat) :
    moments clock source degree =
      ∑ j : Fin source.support.card, source (slots source.support j).val * clock (slots source.support j).val ^ degree := by
  rw [moments,Finsupp.sum, ← Finset.sum_coe_sort]
  exact Fintype.sum_equiv source.support.equivFin _ _ fun j => by
    simp only [slots,Equiv.symm_apply_apply]

/-- Every observed block factors through the same literal support, including blocks wider than it. -/
theorem hankel_factor (clock : I → K) (source : I →₀ K) (width : Nat) :
    let atSite := slots source.support
    let V := powers (fun j => clock (atSite j).val) width
    hankel (moments clock source) width =
      V * diagonal (fun j => source (atSite j).val) * Vᵀ := by
  apply Matrix.ext
  intro i k
  rw [Matrix.mul_apply]
  simp only [hankel, Matrix.of_apply, Matrix.mul_diagonal, Matrix.transpose_apply,powers]
  rw [support_moment]
  exact Finset.sum_congr rfl fun j _ => by rw [pow_add]; ring

private theorem support_hankel_nonzero (clock : I → K) (distinct : Function.Injective clock) (source : I →₀ K) :
    (hankel (moments clock source) source.support.card).det ≠ 0 := by
  have separated : Function.Injective (fun j => clock (slots source.support j).val) :=
    distinct.comp (Subtype.val_injective.comp source.support.equivFin.symm.injective)
  have live (j : Fin source.support.card) : source (slots source.support j).val ≠ 0 :=
    Finsupp.mem_support_iff.mp (slots source.support j).property
  have invertible := powers_det _ separated
  rw [hankel_factor, det_mul, det_mul, det_transpose, det_diagonal]
  exact mul_ne_zero (mul_ne_zero invertible (Finset.prod_ne_zero_iff.mpr fun j _ => live j)) invertible

private theorem hankel_too_wide (clock : I → K) (source : I →₀ K) {width : Nat}
    (tooWide : source.support.card < width) :
    (hankel (moments clock source) width).det = 0 := by
  let V := powers (fun j => clock (slots source.support j).val) width
  let D := diagonal (fun j => source (slots source.support j).val)
  have factor : hankel (moments clock source) width = V*D*Vᵀ := hankel_factor clock source width
  by_contra live
  have small := (rank_mul_le_left (V*D) Vᵀ).trans ((rank_mul_le_left V D).trans (rank_le_width V))
  rw [← factor,rank_of_det_ne_zero live,Fintype.card_fin] at small
  exact (not_lt_of_ge small) tooWide

private theorem hankel_prefix (clock : I → K) (source : I →₀ K) {bound rank : Nat}
    (within : rank ≤ bound) :
    hankel (padded (measure clock source bound)) rank = hankel (moments clock source) rank := by
  apply Matrix.ext
  intro i j
  have hi := i.isLt
  have hj := j.isLt
  exact padded_prefix clock source (show i.val+j.val < bound+bound by omega)

theorem order_from_source (clock : I → K) (distinct : Function.Injective clock)
    (source : I →₀ K) {bound : Nat} (within : source.support.card ≤ bound) :
    order (measure clock source bound) = source.support.card := by
  classical
  let tested := (Finset.range (bound+1)).filter
    (fun rank => (hankel (padded (measure clock source bound)) rank).det ≠ 0)
  change tested.sup id = source.support.card
  have accept : source.support.card ∈ tested := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le within),
      fun silent => support_hankel_nonzero clock distinct source
        ((congrArg Matrix.det (hankel_prefix clock source within)).symm.trans silent)⟩
  apply le_antisymm ?_ (Finset.le_sup (f := id) accept)
  apply Finset.sup_le
  intro rank member
  have details := Finset.mem_filter.mp member
  have bounded : rank ≤ bound := Nat.le_of_lt_succ (Finset.mem_range.mp details.1)
  by_contra tooLarge
  have zero := hankel_too_wide clock source (Nat.lt_of_not_ge tooLarge)
  exact details.2 ((congrArg Matrix.det (hankel_prefix clock source bounded)).trans zero)

private def coefficients (data : Nat → K) (rank : Nat) : Fin rank → K :=
  (hankel data rank)⁻¹ *ᵥ (fun i => -data (i.val+rank))

private def monic {rank : Nat} (coeff : Fin rank → K) : Polynomial K :=
  Polynomial.monomial rank 1 + ∑ i : Fin rank, Polynomial.monomial i.val (coeff i)

/-- Solve the actual leading system, then adjoin its unit leading coefficient. -/
def recurrence {bound : Nat} (data : Fin (bound+bound) → K) : Polynomial K :=
  monic (coefficients (padded data) (order data))

private theorem coefficients_prefix (clock : I → K) (source : I →₀ K) {bound rank : Nat}
    (within : rank ≤ bound) :
    coefficients (padded (measure clock source bound)) rank = coefficients (moments clock source) rank := by
  unfold coefficients
  rw [hankel_prefix clock source within]
  congr 1
  funext i
  have hi := i.isLt
  rw [padded_prefix clock source (show i.val+rank < bound+bound by omega)]

private theorem monic_nonzero {rank : Nat} (coeff : Fin rank → K) : monic coeff ≠ 0 := by
  have top : (monic coeff).coeff rank = 1 := by
    simp only [monic,Polynomial.coeff_add,Polynomial.coeff_monomial,
      Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_zero]
    · exact add_zero _
    · intro i _
      exact if_neg (by have hi := i.isLt; omega)
  intro quiet
  rw [quiet,Polynomial.coeff_zero] at top
  exact zero_ne_one top

private theorem monic_degree {rank : Nat} (coeff : Fin rank → K) : (monic coeff).natDegree ≤ rank := by
  apply (Polynomial.natDegree_le_iff_coeff_eq_zero).mpr
  intro n above
  simp only [monic,Polynomial.coeff_add,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial]
  rw [if_neg (by omega), Finset.sum_eq_zero]
  · exact zero_add _
  · intro i _
    exact if_neg (by have hi := i.isLt; omega)

private theorem recurrence_system (clock : I → K) (distinct : Function.Injective clock) (source : I →₀ K) :
    let r := source.support.card
    hankel (moments clock source) r *ᵥ coefficients (moments clock source) r =
      (fun i => -moments clock source (i.val+r)) := by
  dsimp only
  rw [coefficients,Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr
    (support_hankel_nonzero clock distinct source)),Matrix.one_mulVec]

private theorem weighted_values (clock : I → K) (source : I →₀ K)
    (coeff : Fin source.support.card → K) :
    let r := source.support.card
    let atSite := slots source.support
    let V := powers (fun j => clock (atSite j).val) r
    V *ᵥ (fun j => source (atSite j).val * (monic coeff).eval (clock (atSite j).val)) =
      (fun i => moments clock source (i.val+r)) + hankel (moments clock source) r *ᵥ coeff := by
  let r := source.support.card
  let nodes := fun j => clock (slots source.support j).val
  let weights := fun j => source (slots source.support j).val
  funext i
  change (powers nodes r *ᵥ (fun j => weights j * (monic coeff).eval (nodes j))) i =
    moments clock source (i.val+r) + (hankel (moments clock source) r *ᵥ coeff) i
  simp only [Matrix.mulVec_apply_eq_sum,powers,hankel,Matrix.of_apply,monic,Polynomial.eval_add,
    Polynomial.eval_monomial,Polynomial.eval_finsetSum,one_mul,mul_add,Finset.sum_add_distrib]
  congr 1
  · rw [support_moment]
    exact Finset.sum_congr rfl fun j _ => by change _ = weights j * nodes j ^ (i.val+r); rw [pow_add]; ring
  · simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [support_moment,Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by
      change _ = weights k * nodes k ^ (i.val+j.val) * coeff j
      rw [pow_add]
      ring

theorem recurrence_vanishes (clock : I → K) (distinct : Function.Injective clock)
    (source : I →₀ K) {bound : Nat} (within : source.support.card ≤ bound)
    {site : I} (active : site ∈ source.support) :
    (recurrence (measure clock source bound)).eval (clock site) = 0 := by
  let r := source.support.card
  let atSite := slots source.support
  let nodes := fun j => clock (atSite j).val
  let V := powers nodes r
  let coeff := coefficients (moments clock source) r
  let z := fun j => source (atSite j).val * (monic coeff).eval (nodes j)
  have current : V *ᵥ z = 0 := by
    have square : V *ᵥ z =
        (fun i : Fin r => moments clock source (i.val+r)) + hankel (moments clock source) r *ᵥ coeff :=
      weighted_values clock source coeff
    have paid : hankel (moments clock source) r *ᵥ coeff = (fun i : Fin r => -moments clock source (i.val+r)) :=
      recurrence_system clock distinct source
    rw [paid] at square
    exact square.trans (add_neg_cancel _)
  have separated : Function.Injective nodes :=
    distinct.comp (Subtype.val_injective.comp source.support.equivFin.symm.injective)
  have invertible : IsUnit V.det := isUnit_iff_ne_zero.mpr (powers_det nodes separated)
  have zero : z = 0 := by
    have readback := congrArg (fun v : Fin r → K => V⁻¹ *ᵥ v) current
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ invertible,Matrix.one_mulVec,Matrix.mulVec_zero] at readback
    exact readback
  let j := source.support.equivFin ⟨site,active⟩
  have found : z j = 0 := congrFun zero j
  have belongs : (atSite j).val = site := congrArg Subtype.val (source.support.equivFin.symm_apply_apply _)
  change source (atSite j).val * (monic coeff).eval (clock (atSite j).val) = 0 at found
  rw [belongs] at found
  rw [recurrence,order_from_source clock distinct source within,coefficients_prefix clock source within]
  exact (mul_eq_zero.mp found).resolve_left (Finsupp.mem_support_iff.mp active)

/-- Test the generated recurrence only at the original available clock sites. -/
def recoverSupport {bound : Nat} (clock : I → K) (available : Finset I) (data : Fin (bound+bound) → K) : Finset I :=
  open Classical in
  available.filter fun site => (recurrence data).eval (clock site) = 0

theorem recover_support (clock : I → K) (distinct : Function.Injective clock)
    (available : Finset I) (source : I →₀ K) (availableSource : source.support ⊆ available)
    {bound : Nat} (within : source.support.card ≤ bound) :
    recoverSupport clock available (measure clock source bound) = source.support := by
  classical
  let poly := recurrence (measure clock source bound)
  let recovered := recoverSupport clock available (measure clock source bound)
  have activeRecovered : source.support ⊆ recovered := fun site active =>
    Finset.mem_filter.mpr ⟨availableSource active, recurrence_vanishes clock distinct source within active⟩
  have nonzero : poly ≠ 0 := monic_nonzero _
  have limited : poly.natDegree ≤ source.support.card := by
    change (monic (coefficients _ (order (measure clock source bound)))).natDegree ≤ _
    exact (monic_degree _).trans_eq (order_from_source clock distinct source within)
  have roots : (recovered.image clock).val ⊆ poly.roots := by
    intro value member
    have tagged : value ∈ recovered.image clock := member
    obtain ⟨site, found, rfl⟩ := Finset.mem_image.mp tagged
    exact (Polynomial.mem_roots nonzero).mpr (Finset.mem_filter.mp found).2
  have count : recovered.card ≤ source.support.card := by
    rw [← Finset.card_image_of_injective _ distinct]
    exact (Polynomial.card_le_degree_of_subset_roots roots).trans limited
  exact (Finset.eq_of_subset_of_card_le activeRecovered count).symm

private theorem decoded_weights (clock : I → K) (distinct : Function.Injective clock)
    (source : I →₀ K) {bound : Nat} (within : source.support.card ≤ bound) :
    let r := source.support.card
    let atSite := slots source.support
    let V := powers (fun j => clock (atSite j).val) r
    V⁻¹ *ᵥ (fun i : Fin r => padded (measure clock source bound) i.val) =
      (fun j => source (atSite j).val) := by
  let r := source.support.card
  let atSite := slots source.support
  let nodes := fun j => clock (atSite j).val
  let V := powers nodes r
  let weights := fun j => source (atSite j).val
  have separated : Function.Injective nodes :=
    distinct.comp (Subtype.val_injective.comp source.support.equivFin.symm.injective)
  have live : IsUnit V.det := isUnit_iff_ne_zero.mpr (powers_det nodes separated)
  have rows : (fun i : Fin r => padded (measure clock source bound) i.val) = V *ᵥ weights := by
    funext i
    have hi := i.isLt
    rw [padded_prefix clock source (show i.val < bound+bound by omega),support_moment]
    simp only [V,powers,Matrix.mulVec_apply_eq_sum,Matrix.of_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  change V⁻¹ *ᵥ (fun i : Fin r => padded (measure clock source bound) i.val) = weights
  rw [rows, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ live, Matrix.one_mulVec]

private def fromSlots (sites : Finset I) (weights : Fin sites.card → K) : I →₀ K :=
  Finsupp.embDomain
    (sites.equivFin.symm.toEmbedding.trans ⟨Subtype.val,Subtype.val_injective⟩)
    (Finsupp.equivFunOnFinite.symm weights)

/-- Reconstruct the original weights from the measured rows after recovering the support. -/
def recover {bound : Nat} (clock : I → K) (available : Finset I) (data : Fin (bound+bound) → K) :
    I →₀ K :=
  let sites := recoverSupport clock available data
  let V := powers (fun j => clock (slots sites j).val) sites.card
  fromSlots sites (V⁻¹ *ᵥ (fun i : Fin sites.card => padded data i.val))

theorem recover_prefix (clock : I → K) (distinct : Function.Injective clock)
    (available : Finset I) (source : I →₀ K) (availableSource : source.support ⊆ available)
    {bound : Nat} (within : source.support.card ≤ bound) :
    recover clock available (measure clock source bound) = source := by
  classical
  unfold recover
  rw [recover_support clock distinct available source availableSource within]
  change fromSlots source.support
    ((powers (fun j => clock (slots source.support j).val) source.support.card)⁻¹ *ᵥ
      (fun i : Fin source.support.card => padded (measure clock source bound) i.val)) = source
  rw [decoded_weights clock distinct source within]
  let sites := source.support
  let embed := sites.equivFin.symm.toEmbedding.trans
    (⟨Subtype.val,Subtype.val_injective⟩ : sites ↪ I)
  change Finsupp.embDomain embed (Finsupp.equivFunOnFinite.symm
    (fun j => source (slots sites j).val)) = source
  ext site
  by_cases active : site ∈ sites
  · let j := sites.equivFin ⟨site,active⟩
    have literal : embed j = site := congrArg Subtype.val (sites.equivFin.symm_apply_apply _)
    rw [← literal,Finsupp.embDomain_apply_self]
    rfl
  · have outside : site ∉ Set.range embed := by
      rintro ⟨j,rfl⟩
      exact active (slots sites j).property
    exact (Finsupp.embDomain_of_notMem_range _ _ _ outside).trans
      (Finsupp.notMem_support_iff.mp active).symm

end SourceGeneratedFiniteGram.SparseMoment
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
