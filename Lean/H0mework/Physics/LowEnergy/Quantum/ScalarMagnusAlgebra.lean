import H0mework.Physics.LowEnergy.Quantum.WavepacketCurrent
import Mathlib.Tactic.NoncommRing

/-! The Lie closure used by the scalar Magnus integral. The finite channel
index labels source Fourier insertions, not a truncation of matter momentum. -/
set_option autoImplicit false
namespace SourceScalarMagnus
open scoped BigOperators
noncomputable section

section Algebra
variable {R A T : Type*} [Ring R] [Algebra ℂ R] [Fintype A]

omit [Algebra ℂ R] in
private theorem reorder (q r p s : R) (middle : Commute r p) :
    (q * r) * (p * s) = (q * p) * (r * s) := by
  calc
    _ = q * (r * p) * s := by noncomm_ring
    _ = q * (p * r) * s := by rw [middle.eq]
    _ = _ := by noncomm_ring

theorem pair_commutator (q p r s : R) (d : ℂ)
    (rp : Commute r p) (sq : Commute s q) (rs : Commute r s)
    (CCR : q * p - p * q = d • 1) :
    (q * r) * (p * s) - (p * s) * (q * r) = d • (r * s) := by
  rw [reorder q r p s rp, reorder p s q r sq, ← rs.eq, ← sub_mul, CCR,
    smul_mul_assoc, one_mul]

def coupling (Q J : A → R) : R := ∑ a : A, Q a * J a

theorem coupling_commutator (Q P J K : A → R) (delta : A → A → ℂ)
    (crossQ : ∀ a b, Commute (K b) (Q a))
    (crossP : ∀ a b, Commute (J a) (P b))
    (currents : ∀ a b, Commute (J a) (K b))
    (CCR : ∀ a b, Q a * P b - P b * Q a = delta a b • 1) :
    coupling Q J * coupling P K - coupling P K * coupling Q J =
      ∑ a : A, ∑ b : A, delta a b • (J a * K b) := by
  simp only [coupling, Fintype.sum_mul_sum]
  rw [Finset.sum_comm (f := fun b a : A => P b * K b * (Q a * J a)),
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  exact pair_commutator _ _ _ _ _ (crossP a b) (crossQ a b) (currents a b) (CCR a b)

theorem coupling_triple_zero (Q J : T → A → R) (delta : T → A → T → A → ℂ)
    (cross : ∀ t a s b, Commute (J t a) (Q s b))
    (currents : ∀ t a s b, Commute (J t a) (J s b))
    (CCR : ∀ t a s b, Q t a * Q s b - Q s b * Q t a = delta t a s b • 1)
    (t s u : T) :
    Commute (coupling (Q u) (J u))
      (coupling (Q t) (J t) * coupling (Q s) (J s) -
        coupling (Q s) (J s) * coupling (Q t) (J t)) := by
  rw [coupling_commutator (Q t) (Q s) (J t) (J s) (fun a b => delta t a s b)
    (fun a b => cross s b t a) (fun a b => cross t a s b)
    (fun a b => currents t a s b) (fun a b => CCR t a s b)]
  apply Commute.sum_right
  intro a _
  apply Commute.sum_right
  intro b _
  apply Commute.smul_right
  apply Commute.mul_right
  · apply Commute.sum_left
    intro c _
    exact (cross t a u c).symm.mul_left (currents u c t a)
  · apply Commute.sum_left
    intro c _
    exact (cross s b u c).symm.mul_left (currents u c s b)

end Algebra

section Source
open SourceWavepacketInteraction SourceWavepacketCurrent
variable {M I B A T : Type*} [Fintype I] [DecidableEq I] [Fintype A]
variable [AddCommGroup B] [Module ℂ B] {N : ℕ}

omit [DecidableEq I] in
theorem actual_scalar_coupling (Q : A → Module.End ℂ B)
    (shift : A → M → M) (W : A → M → Matrix I I ℂ) :
    coupling (fun a => onBoson (M := M) (I := I) (N := N) (Q a))
      (fun a => current (shift a) (W a)) =
        familyInteraction shift (fun a => scalarKernel (W a) (Q a)) := by
  simp only [coupling, familyInteraction, boson_current_factor]

theorem actual_scalar_triple_zero (target : Finset I)
    (Q : T → A → Module.End ℂ B) (delta : T → A → T → A → ℂ)
    (shift : T → A → M → M) (W : T → A → M → Matrix I I ℂ)
    (source_grade : ∀ t a p i j, ((if i ∈ target then 1 else 0 : ℂ) -
      (if j ∈ target then 1 else 0 : ℂ) - 1) * W t a p i j = 0)
    (source_CCR : ∀ t a s b, Q t a * Q s b - Q s b * Q t a = delta t a s b • 1)
    (t s u : T) :
    let V := fun v => familyInteraction (N := N) (shift v)
      (fun a => scalarKernel (W v a) (Q v a))
    Commute (V u) (V t * V s - V s * V t) := by
  dsimp only
  simp_rw [← actual_scalar_coupling]
  apply coupling_triple_zero (fun v a => onBoson (Q v a))
    (fun v a => current (shift v a) (W v a)) delta _ _ _ t s u
  · intro v a w b
    exact (boson_commutes_current (Q w b) (shift v a) (W v a)).symm
  · intro v a w b
    exact currents_commute target _ _ _ _ (source_grade v a) (source_grade w b)
  · intro v a w b
    exact onBoson_CCR _ _ _ (source_CCR v a w b)

end Source
end
end SourceScalarMagnus
