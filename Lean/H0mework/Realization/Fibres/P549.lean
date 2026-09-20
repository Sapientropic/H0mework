import H0mework.Realization.Fibres.P548

/-!
# Proposition 549: the zero fiber is the genuine annealing specialization

P547/P548 prove the positive statement:

`SigmaRelaxedObject K X H 0 ≃ X`.

This file proves the complementary boundary.  Away from `sigma = 0`, the
current relaxed quotient is equivalent to the raw decorated carrier `X × H`.
Consequently, whenever the headroom type has two distinct values, the
forgetful map to `X` is not injective.  Thus the standard-object equivalence is
not a generic property of every fiber; it is exactly the annealed zero-fiber
specialization.
-/

noncomputable section

set_option linter.checkUnivs false

namespace SaturationMonoid
namespace AffineRelaxation

universe u v w

/-! ## Active fibers retain headroom -/

/-- THEOREM 1: away from `sigma = 0`, the relaxed quotient is just the raw
decorated carrier `X × H`.  The zero-collapse constructor is impossible, and
the active constructor only identifies literally equal pairs. -/
def sigmaActiveRelaxedEquivRaw
    {K : Type u} [Zero K] {X : Type v} {H : Type w}
    {σ : K} (hσ : σ ≠ 0) :
    SigmaRelaxedObject K X H σ ≃ SigmaRelaxedRaw X H where
  toFun := Quot.lift id (by
    intro a b h
    cases h with
    | zero hzero _ =>
        exact False.elim (hσ hzero)
    | active _ heq =>
        exact heq)
  invFun := Quot.mk (SigmaRelaxationRel (K := K) (X := X) (H := H) σ)
  left_inv := by
    intro z
    refine Quot.inductionOn z ?_
    intro a
    rfl
  right_inv := by
    intro a
    rfl

@[simp] theorem sigmaActiveRelaxedEquivRaw_mk
    {K : Type u} [Zero K] {X : Type v} {H : Type w}
    {σ : K} (hσ : σ ≠ 0) (x : X) (h : H) :
    sigmaActiveRelaxedEquivRaw (K := K) (X := X) (H := H) hσ
        (sigmaRelaxedMk (K := K) (σ := σ) x h) = (x, h) :=
  rfl

/-- The active-fiber forgetful map, obtained by projecting the raw decorated
carrier `X × H` back to `X`. -/
def sigmaActiveForget
    {K : Type u} [Zero K] {X : Type v} {H : Type w}
    {σ : K} (hσ : σ ≠ 0) :
    SigmaRelaxedObject K X H σ -> X :=
  fun z => (sigmaActiveRelaxedEquivRaw (K := K) (X := X) (H := H) hσ z).1

@[simp] theorem sigmaActiveForget_mk
    {K : Type u} [Zero K] {X : Type v} {H : Type w}
    {σ : K} (hσ : σ ≠ 0) (x : X) (h : H) :
    sigmaActiveForget (K := K) (X := X) (H := H) hσ
        (sigmaRelaxedMk (K := K) (σ := σ) x h) = x :=
  rfl

/-- THEOREM 2: if the headroom type has two distinct values, the active-fiber
forgetful map cannot be injective. -/
theorem sigmaActiveForget_not_injective_of_distinct_headrooms
    {K : Type u} [Zero K] {X : Type v} {H : Type w}
    {σ : K} (hσ : σ ≠ 0)
    (x : X) {h₁ h₂ : H} (hh : h₁ ≠ h₂) :
    ¬ Function.Injective
        (sigmaActiveForget (K := K) (X := X) (H := H) hσ) := by
  intro hinj
  let z₁ : SigmaRelaxedObject K X H σ :=
    sigmaRelaxedMk (K := K) (σ := σ) x h₁
  let z₂ : SigmaRelaxedObject K X H σ :=
    sigmaRelaxedMk (K := K) (σ := σ) x h₂
  have hsame :
      sigmaActiveForget (K := K) (X := X) (H := H) hσ z₁ =
        sigmaActiveForget (K := K) (X := X) (H := H) hσ z₂ := by
    simp [z₁, z₂]
  have hz : z₁ = z₂ := hinj hsame
  have hp :
      (x, h₁) = (x, h₂) := by
    simpa [z₁, z₂] using
      congrArg
        (sigmaActiveRelaxedEquivRaw (K := K) (X := X) (H := H) hσ)
        hz
  exact hh (congrArg Prod.snd hp)

end AffineRelaxation

open AffineRelaxation

/-! ## The boundary specialized to the eighteen-object table -/

/-- THEOREM 3: for every core mathematical object, every nonzero sigma fiber
retains a real headroom coordinate, so the forgetful map is not injective. -/
theorem coreObjectSigmaActiveForget_not_injective
    (O : CoreMathematicalObject18) {σ : ℝ} (hσ : σ ≠ 0) :
    ¬ Function.Injective
        (sigmaActiveForget
          (K := ℝ) (X := CoreObjectCarrier O) (H := CoreObjectHeadroom)
          hσ) :=
  sigmaActiveForget_not_injective_of_distinct_headrooms
    (K := ℝ) (X := CoreObjectCarrier O) (H := CoreObjectHeadroom)
    (σ := σ) hσ (default : CoreObjectCarrier O)
    (h₁ := (0 : CoreObjectHeadroom)) (h₂ := (1 : CoreObjectHeadroom))
    zero_ne_one

/-- Compact certificate that the P548 zero-fiber equivalence is a genuine
specialization statement: active fibers retain their headroom coordinate. -/
structure SigmaZeroAnnealingBoundaryCertificate where
  zero_fiber_table :
    CoreObjectSigmaZeroFiberTableCertificate
  active_raw_equiv :
    ∀ {K : Type u} [Zero K] {X : Type v} {H : Type w}
      {σ : K}, σ ≠ 0 ->
        SigmaRelaxedObject K X H σ ≃ SigmaRelaxedRaw X H
  active_forget_not_injective :
    ∀ (O : CoreMathematicalObject18) {σ : ℝ}, (hσ : σ ≠ 0) ->
      ¬ Function.Injective
          (sigmaActiveForget
            (K := ℝ) (X := CoreObjectCarrier O) (H := CoreObjectHeadroom)
            (σ := σ) hσ)

/-- THEOREM 4: the zero-fiber table and its active-fiber boundary are both
available as one root-importable certificate. -/
def sigmaZeroAnnealingBoundaryCertificate :
    SigmaZeroAnnealingBoundaryCertificate where
  zero_fiber_table := coreObjectSigmaZeroFiberTableCertificate
  active_raw_equiv := by
    intro K _zero X H σ hσ
    exact sigmaActiveRelaxedEquivRaw
      (K := K) (X := X) (H := H) hσ
  active_forget_not_injective := by
    intro O σ hσ
    exact coreObjectSigmaActiveForget_not_injective O hσ

end SaturationMonoid
