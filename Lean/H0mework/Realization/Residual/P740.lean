import H0mework.Realization.Residual.P739

/-!
# Proposition 740: the natural residual-process skeleton is the rate monoid

P739 proves that every scalar-line natural residual process is determined by
one scalar rate and that composition sends rates to `satOrField`.

This file turns that into the process-level algebraic skeleton.  We quotient
informally by extensional equality of the two operational fields `keepR` and
`keepE`, then prove:

* extensional equality is equivalent to equality of rates;
* every process is extensionally its canonical scalar-rate process;
* composition is well-defined under that extensional equality;
* identity, associativity, commutativity, and absorbing zero-keep all hold
  extensionally;
* the canonical scalar-rate embedding preserves composition, identity, and
  absorbing rate one.

Thus the process algebra forced by residual conservation plus scalar-line
naturality is exactly the noisy-OR rate monoid, not merely a convenient display.
-/

noncomputable section

set_option linter.checkUnivs false
set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

namespace ScalarLineNaturalResidualProcess

/-- Extensional equality of natural residual processes: same scalar keep and
same carrier keep.  Proof fields are deliberately ignored. -/
def ExtEq
    (p q : ScalarLineNaturalResidualProcess E) : Prop :=
  p.keepR = q.keepR ∧ p.keepE = q.keepE

/-- THEOREM 1: extensional equality is reflexive. -/
theorem extEq_refl
    (p : ScalarLineNaturalResidualProcess E) :
    ExtEq p p := by
  exact ⟨rfl, rfl⟩

/-- THEOREM 2: extensional equality is symmetric. -/
theorem extEq_symm
    {p q : ScalarLineNaturalResidualProcess E}
    (h : ExtEq p q) :
    ExtEq q p := by
  exact ⟨h.1.symm, h.2.symm⟩

/-- THEOREM 3: extensional equality is transitive. -/
theorem extEq_trans
    {p q r : ScalarLineNaturalResidualProcess E}
    (hpq : ExtEq p q) (hqr : ExtEq q r) :
    ExtEq p r := by
  exact ⟨hpq.1.trans hqr.1, hpq.2.trans hqr.2⟩

/-- THEOREM 4: extensionally equal processes have equal rates. -/
theorem rate_eq_of_extEq
    {p q : ScalarLineNaturalResidualProcess E}
    (h : ExtEq p q) :
    p.rate = q.rate := by
  unfold rate complementTrace
  rw [h.1]

/-- THEOREM 5: equal rates force extensional equality. -/
theorem extEq_of_rate_eq
    (p q : ScalarLineNaturalResidualProcess E)
    (h : p.rate = q.rate) :
    ExtEq p q := by
  exact extensional_eq_of_same_rate p q h

/-- THEOREM 6: extensional equality is exactly equality of rates. -/
theorem extEq_iff_rate_eq
    (p q : ScalarLineNaturalResidualProcess E) :
    ExtEq p q ↔ p.rate = q.rate := by
  constructor
  · exact rate_eq_of_extEq
  · exact extEq_of_rate_eq p q

/-- THEOREM 7: every natural process is extensionally its canonical process at
its rate. -/
theorem extEq_canonical_rate
    (p : ScalarLineNaturalResidualProcess E) :
    ExtEq p (canonical (E := E) p.rate) := by
  exact ⟨keepR_eq_canonical p, keepE_eq_canonical p⟩

/-- THEOREM 8: canonical processes are extensionally equal exactly when their
rates are equal. -/
theorem canonical_extEq_iff
    (sigma tau : ℝ) :
    ExtEq (canonical (E := E) sigma) (canonical (E := E) tau) ↔
      sigma = tau := by
  rw [extEq_iff_rate_eq, canonical_rate, canonical_rate]

/-- THEOREM 9: process composition respects extensional equality. -/
theorem compose_ext_congr
    {p₂ p₁ q₂ q₁ : ScalarLineNaturalResidualProcess E}
    (h₂ : ExtEq p₂ q₂) (h₁ : ExtEq p₁ q₁) :
    ExtEq (compose p₂ p₁) (compose q₂ q₁) := by
  apply extEq_of_rate_eq
  rw [compose_rate p₂ p₁, compose_rate q₂ q₁,
    rate_eq_of_extEq h₁, rate_eq_of_extEq h₂]

/-- THEOREM 10: identity is a left identity extensionally. -/
theorem compose_identity_left_ext
    (p : ScalarLineNaturalResidualProcess E) :
    ExtEq (compose (identity (E := E)) p) p := by
  apply extEq_of_rate_eq
  rw [compose_rate (identity (E := E)) p, identity_rate]
  unfold satOrField
  ring

/-- THEOREM 11: identity is a right identity extensionally. -/
theorem compose_identity_right_ext
    (p : ScalarLineNaturalResidualProcess E) :
    ExtEq (compose p (identity (E := E))) p := by
  apply extEq_of_rate_eq
  rw [compose_rate p (identity (E := E)), identity_rate]
  unfold satOrField
  ring

/-- THEOREM 12: process composition is associative extensionally. -/
theorem compose_assoc_ext
    (p₃ p₂ p₁ : ScalarLineNaturalResidualProcess E) :
    ExtEq (compose p₃ (compose p₂ p₁))
      (compose (compose p₃ p₂) p₁) := by
  apply extEq_of_rate_eq
  rw [compose_rate p₃ (compose p₂ p₁), compose_rate p₂ p₁,
    compose_rate (compose p₃ p₂) p₁, compose_rate p₃ p₂]
  unfold satOrField
  ring

/-- THEOREM 13: process composition is commutative extensionally. -/
theorem compose_comm_ext
    (p₂ p₁ : ScalarLineNaturalResidualProcess E) :
    ExtEq (compose p₂ p₁) (compose p₁ p₂) := by
  apply extEq_of_rate_eq
  rw [compose_rate p₂ p₁, compose_rate p₁ p₂]
  unfold satOrField
  ring

/-- THEOREM 14: zero keep absorbs on the left extensionally. -/
theorem compose_zeroKeep_left_ext
    (p : ScalarLineNaturalResidualProcess E) :
    ExtEq (compose (zeroKeep (E := E)) p) (zeroKeep (E := E)) := by
  apply extEq_of_rate_eq
  rw [compose_rate (zeroKeep (E := E)) p, zeroKeep_rate]
  unfold satOrField
  ring

/-- THEOREM 15: zero keep absorbs on the right extensionally. -/
theorem compose_zeroKeep_right_ext
    (p : ScalarLineNaturalResidualProcess E) :
    ExtEq (compose p (zeroKeep (E := E))) (zeroKeep (E := E)) := by
  apply extEq_of_rate_eq
  rw [compose_rate p (zeroKeep (E := E)), zeroKeep_rate]
  unfold satOrField
  ring

/-- THEOREM 16: the canonical scalar-rate embedding preserves composition. -/
theorem canonical_compose_ext
    (sigma₂ sigma₁ : ℝ) :
    ExtEq
      (compose (canonical (E := E) sigma₂) (canonical (E := E) sigma₁))
      (canonical (E := E) (satOrField sigma₁ sigma₂)) := by
  apply extEq_of_rate_eq
  rw [compose_rate, canonical_rate, canonical_rate, canonical_rate]

/-- THEOREM 17: canonical rate zero is the identity process extensionally. -/
theorem canonical_zero_ext_identity :
    ExtEq (canonical (E := E) 0) (identity (E := E)) := by
  apply extEq_of_rate_eq
  rw [canonical_rate, identity_rate]

/-- THEOREM 18: canonical rate one is zero keep extensionally. -/
theorem canonical_one_ext_zeroKeep :
    ExtEq (canonical (E := E) 1) (zeroKeep (E := E)) := by
  apply extEq_of_rate_eq
  rw [canonical_rate, zeroKeep_rate]

end ScalarLineNaturalResidualProcess

open ScalarLineNaturalResidualProcess

/-- P740 certificate: modulo extensional equality, scalar-line natural
residual processes form exactly the noisy-OR rate monoid. -/
structure ScalarLineNaturalProcessMonoidSkeletonCertificate
    (E : Type u) [AddCommGroup E] [Module ℝ E] : Prop where
  ext_eq_iff_rate_eq :
    ∀ p q : ScalarLineNaturalResidualProcess E,
      ExtEq p q ↔ p.rate = q.rate
  canonical_surjective_ext :
    ∀ p : ScalarLineNaturalResidualProcess E,
      ExtEq p (canonical (E := E) p.rate)
  canonical_injective_ext :
    ∀ sigma tau : ℝ,
      ExtEq (canonical (E := E) sigma) (canonical (E := E) tau) ↔
        sigma = tau
  compose_respects_ext :
    ∀ {p₂ p₁ q₂ q₁ : ScalarLineNaturalResidualProcess E},
      ExtEq p₂ q₂ -> ExtEq p₁ q₁ ->
        ExtEq (compose p₂ p₁) (compose q₂ q₁)
  left_identity_ext :
    ∀ p : ScalarLineNaturalResidualProcess E,
      ExtEq (compose (identity (E := E)) p) p
  right_identity_ext :
    ∀ p : ScalarLineNaturalResidualProcess E,
      ExtEq (compose p (identity (E := E))) p
  assoc_ext :
    ∀ p₃ p₂ p₁ : ScalarLineNaturalResidualProcess E,
      ExtEq (compose p₃ (compose p₂ p₁))
        (compose (compose p₃ p₂) p₁)
  comm_ext :
    ∀ p₂ p₁ : ScalarLineNaturalResidualProcess E,
      ExtEq (compose p₂ p₁) (compose p₁ p₂)
  zero_keep_absorbs_left_ext :
    ∀ p : ScalarLineNaturalResidualProcess E,
      ExtEq (compose (zeroKeep (E := E)) p) (zeroKeep (E := E))
  zero_keep_absorbs_right_ext :
    ∀ p : ScalarLineNaturalResidualProcess E,
      ExtEq (compose p (zeroKeep (E := E))) (zeroKeep (E := E))
  canonical_compose_ext :
    ∀ sigma₂ sigma₁ : ℝ,
      ExtEq
        (compose (canonical (E := E) sigma₂)
          (canonical (E := E) sigma₁))
        (canonical (E := E) (satOrField sigma₁ sigma₂))
  canonical_zero_ext_identity :
    ExtEq (canonical (E := E) 0) (identity (E := E))
  canonical_one_ext_zeroKeep :
    ExtEq (canonical (E := E) 1) (zeroKeep (E := E))
  process_classification :
    ScalarLineNaturalProcessClassificationCertificate E

/-- THEOREM 19: every real module carrier has the natural-process monoid
skeleton certificate. -/
theorem scalarLineNaturalProcessMonoidSkeletonCertificate :
    ScalarLineNaturalProcessMonoidSkeletonCertificate E where
  ext_eq_iff_rate_eq := extEq_iff_rate_eq
  canonical_surjective_ext := extEq_canonical_rate
  canonical_injective_ext := canonical_extEq_iff
  compose_respects_ext := by
    intro p₂ p₁ q₂ q₁ h₂ h₁
    exact compose_ext_congr h₂ h₁
  left_identity_ext := compose_identity_left_ext
  right_identity_ext := compose_identity_right_ext
  assoc_ext := compose_assoc_ext
  comm_ext := compose_comm_ext
  zero_keep_absorbs_left_ext := compose_zeroKeep_left_ext
  zero_keep_absorbs_right_ext := compose_zeroKeep_right_ext
  canonical_compose_ext := canonical_compose_ext
  canonical_zero_ext_identity := canonical_zero_ext_identity
  canonical_one_ext_zeroKeep := canonical_one_ext_zeroKeep
  process_classification := scalarLineNaturalProcessClassificationCertificate

end AffineRelaxation
end SaturationMonoid
