import H0mework.Realization.Fibres.P576

/-!
# Proposition 577: sigma-zero transport for Lyapunov certificates

P576 closed the bounded-linear observable-bisimulation bridge.  The runtime
Jacobian / reducer story is often expressed one layer more generally: provide a
Lyapunov energy `V` and prove that a step contracts that energy.

This file proves that such Lyapunov certificates transport through the
sigma-zero forgetful projection for arbitrary state updates, not just bounded
linear maps:

* pull back an energy `V : X -> X -> ℝ` to the zero fiber;
* lift an arbitrary step `T : X -> X` by `sigmaZeroLiftUnary`;
* prove Lyapunov contraction is preserved and reflected;
* compose the transported contraction with Lemma 3's Lyapunov-margin theorem.

This is the generic certificate bridge for runtime reducer proofs.  A concrete
Jacobian/PSD/interval certificate only has to produce the standard-side
Lyapunov contraction; this file moves it into the sigma-zero carrier and then
gets eventual observational equality.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

universe u v w x

/-! ## Pullback Lyapunov energy -/

/-- Pull a standard Lyapunov energy on `X` back to the sigma-zero fiber. -/
def sigmaZeroPullbackEnergy
    {K : Type u} [Zero K] {X : Type v} {H : Type w} [Inhabited H]
    (V : X → X → ℝ) :
    SigmaRelaxedObject K X H (0 : K) →
      SigmaRelaxedObject K X H (0 : K) → ℝ :=
  fun z w =>
    V
      (sigmaZeroForget (K := K) (X := X) (H := H) z)
      (sigmaZeroForget (K := K) (X := X) (H := H) w)

@[simp] theorem sigmaZeroPullbackEnergy_apply
    {K : Type u} [Zero K] {X : Type v} {H : Type w} [Inhabited H]
    (V : X → X → ℝ)
    (z w : SigmaRelaxedObject K X H (0 : K)) :
    sigmaZeroPullbackEnergy (K := K) (H := H) V z w =
      V
        (sigmaZeroForget (K := K) (X := X) (H := H) z)
        (sigmaZeroForget (K := K) (X := X) (H := H) w) :=
  rfl

/-- THEOREM 1: a pulled-back energy after a lifted step is the standard energy
after the standard step. -/
@[simp] theorem sigmaZeroPullbackEnergy_liftUnary
    {K : Type u} [Zero K] {X : Type v} {H : Type w} [Inhabited H]
    (V : X → X → ℝ) (T : X → X)
    (z w : SigmaRelaxedObject K X H (0 : K)) :
    sigmaZeroPullbackEnergy (K := K) (H := H) V
        (sigmaZeroLiftUnary (K := K) (H := H) T z)
        (sigmaZeroLiftUnary (K := K) (H := H) T w) =
      V
        (T (sigmaZeroForget (K := K) (X := X) (H := H) z))
        (T (sigmaZeroForget (K := K) (X := X) (H := H) w)) :=
  rfl

/-- THEOREM 2: a standard fixed point lifts to a sigma-zero fixed point for an
arbitrary unary step. -/
@[simp] theorem sigmaZeroLiftUnary_fixed_embed
    {K : Type u} [Zero K] {X : Type v} {H : Type w} [Inhabited H]
    (T : X → X) {a : X} (ha : T a = a) :
    sigmaZeroLiftUnary (K := K) (H := H) T
        (sigmaZeroEmbed (K := K) (X := X) (H := H) a) =
      sigmaZeroEmbed (K := K) (X := X) (H := H) a := by
  apply (sigmaZeroRelaxedEquiv K X H).injective
  change sigmaZeroForget (K := K) (X := X) (H := H)
      (sigmaZeroLiftUnary (K := K) (H := H) T
        (sigmaZeroEmbed (K := K) (X := X) (H := H) a)) =
    sigmaZeroForget (K := K) (X := X) (H := H)
      (sigmaZeroEmbed (K := K) (X := X) (H := H) a)
  simp [sigmaZeroForget_liftUnary, ha]

/-! ## Lyapunov contraction transport -/

/-- THEOREM 3: Lyapunov contraction is preserved and reflected by pulling the
energy and step through the sigma-zero carrier. -/
@[simp] theorem sigmaZeroLyapunovContraction_iff
    {K : Type u} [Zero K] {X : Type v} {H : Type w} [Inhabited H]
    (V : X → X → ℝ) (T : X → X) (r : ℝ) :
    LyapunovContraction (sigmaZeroPullbackEnergy (K := K) (H := H) V)
        (sigmaZeroLiftUnary (K := K) (H := H) T) r ↔
      LyapunovContraction V T r := by
  constructor
  · intro h x y
    have hxy := h
      (sigmaZeroEmbed (K := K) (X := X) (H := H) x)
      (sigmaZeroEmbed (K := K) (X := X) (H := H) y)
    simpa [sigmaZeroPullbackEnergy, sigmaZeroForget_liftUnary] using hxy
  · intro h z w
    change
      V
          (T (sigmaZeroForget (K := K) (X := X) (H := H) z))
          (T (sigmaZeroForget (K := K) (X := X) (H := H) w)) ≤
        r * V
          (sigmaZeroForget (K := K) (X := X) (H := H) z)
          (sigmaZeroForget (K := K) (X := X) (H := H) w)
    exact h _ _

/-! ## Observable equality from transported Lyapunov certificates -/

/-- THEOREM 4: a standard Lyapunov contraction certificate for `T` gives
eventual observational equality for the lifted sigma-zero step once both lifted
paths have certified tails into the same pulled-back observation margin. -/
theorem sigmaZeroLiftUnary_eventual_obs_eq_of_lyapunov_margin
    {K : Type u} [Zero K] {X : Type v} {H : Type w} [Inhabited H]
    (V : X → X → ℝ) (T : X → X) {r ε : ℝ} {a : X}
    {O : Type x}
    {x y : SigmaRelaxedObject K X H (0 : K)}
    {obs : SigmaRelaxedObject K X H (0 : K) → O}
    (hr_nonneg : 0 ≤ r)
    (hcontract : LyapunovContraction V T r)
    (ha : T a = a)
    (hobs_margin :
      ∀ z : SigmaRelaxedObject K X H (0 : K),
        sigmaZeroPullbackEnergy (K := K) (H := H) V z
            (sigmaZeroEmbed (K := K) (X := X) (H := H) a) < ε →
          obs z = obs (sigmaZeroEmbed (K := K) (X := X) (H := H) a))
    (hxtail : ∃ Nx, ∀ n, Nx ≤ n →
      r ^ n * sigmaZeroPullbackEnergy (K := K) (H := H) V x
        (sigmaZeroEmbed (K := K) (X := X) (H := H) a) < ε)
    (hytail : ∃ Ny, ∀ n, Ny ≤ n →
      r ^ n * sigmaZeroPullbackEnergy (K := K) (H := H) V y
        (sigmaZeroEmbed (K := K) (X := X) (H := H) a) < ε) :
    ∃ N, ∀ n, N ≤ n →
      obs (((sigmaZeroLiftUnary (K := K) (H := H) T)^[n]) x) =
        obs (((sigmaZeroLiftUnary (K := K) (H := H) T)^[n]) y) := by
  exact eventual_obs_eq_of_lyapunov_margin
    (V := sigmaZeroPullbackEnergy (K := K) (H := H) V)
    (T := sigmaZeroLiftUnary (K := K) (H := H) T)
    (r := r) (ε := ε)
    (z := sigmaZeroEmbed (K := K) (X := X) (H := H) a)
    (x := x) (y := y) (obs := obs)
    hr_nonneg
    ((sigmaZeroLyapunovContraction_iff (K := K) (H := H) V T r).2 hcontract)
    (sigmaZeroLiftUnary_fixed_embed (K := K) (H := H) T ha)
    hobs_margin
    hxtail
    hytail

/-- A compact generic bridge certificate for sigma-zero Lyapunov transport and
observable bisimulation. -/
structure SigmaZeroLyapunovObservableBridgeCertificate
    (K : Type u) [Zero K] where
  contraction_iff :
    ∀ {X : Type v} {H : Type w} [Inhabited H]
      (V : X → X → ℝ) (T : X → X) (r : ℝ),
      LyapunovContraction (sigmaZeroPullbackEnergy (K := K) (H := H) V)
          (sigmaZeroLiftUnary (K := K) (H := H) T) r ↔
        LyapunovContraction V T r
  eventual_obs :
    ∀ {X : Type v} {H : Type w} [Inhabited H]
      (V : X → X → ℝ) (T : X → X) {r ε : ℝ} {a : X}
      {O : Type x}
      {x y : SigmaRelaxedObject K X H (0 : K)}
      {obs : SigmaRelaxedObject K X H (0 : K) → O},
      0 ≤ r → LyapunovContraction V T r → T a = a →
      (∀ z : SigmaRelaxedObject K X H (0 : K),
        sigmaZeroPullbackEnergy (K := K) (H := H) V z
            (sigmaZeroEmbed (K := K) (X := X) (H := H) a) < ε →
          obs z = obs (sigmaZeroEmbed (K := K) (X := X) (H := H) a)) →
      (∃ Nx, ∀ n, Nx ≤ n →
        r ^ n * sigmaZeroPullbackEnergy (K := K) (H := H) V x
          (sigmaZeroEmbed (K := K) (X := X) (H := H) a) < ε) →
      (∃ Ny, ∀ n, Ny ≤ n →
        r ^ n * sigmaZeroPullbackEnergy (K := K) (H := H) V y
          (sigmaZeroEmbed (K := K) (X := X) (H := H) a) < ε) →
      ∃ N, ∀ n, N ≤ n →
        obs (((sigmaZeroLiftUnary (K := K) (H := H) T)^[n]) x) =
          obs (((sigmaZeroLiftUnary (K := K) (H := H) T)^[n]) y)

/-- THEOREM 5: the canonical sigma-zero Lyapunov observable bridge
certificate. -/
theorem sigmaZeroLyapunovObservableBridgeCertificate
    (K : Type u) [Zero K] :
    SigmaZeroLyapunovObservableBridgeCertificate K where
  contraction_iff := by
    intro X H _ V T r
    exact sigmaZeroLyapunovContraction_iff (K := K) (H := H) V T r
  eventual_obs := by
    intro X H _ V T r ε a O x y obs hr_nonneg hcontract ha
      hobs_margin hxtail hytail
    exact sigmaZeroLiftUnary_eventual_obs_eq_of_lyapunov_margin
      (K := K) (H := H) V T hr_nonneg hcontract ha
      hobs_margin hxtail hytail


end AffineRelaxation
end SaturationMonoid
