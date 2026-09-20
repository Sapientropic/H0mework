import H0mework.Realization.RelaxationFlow.P304

/-!
# Proposition 305: iteration counts act on the relaxation carrier

Proposition 304 made the effective-rate map

`Multiplicative ℕ →* NonAbsorbingRate`

explicit.  This file adds the corresponding carrier action.  For a fixed target
and base rate, `Multiplicative ℕ` acts on the carrier by repeated relaxation.
The action at `n` is exactly the single relaxation step whose rate is the
homomorphic effective rate of P304.

So the corrected spine now has both sides:

* arithmetic side: iteration counts form a monoid hom into noisy-OR rates;
* dynamics side: iteration counts act on states by repeated relaxation.
-/

namespace SaturationMonoid
namespace AffineRelaxation

open SatOrFieldAlgebra

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

/-- The parameterized action of iteration counts on the carrier: `n • x` means
apply the fixed relaxation step `n` times.  This is a value, not a global
instance, because it depends on `target` and `σ`. -/
@[reducible]
def relaxationIterationMulAction
    (target : E) (σ : K) :
    MulAction (Multiplicative ℕ) E where
  smul n x := (fun y : E => relaxModule target σ y)^[n.toAdd] x
  one_smul := by
    intro x
    rfl
  mul_smul := by
    intro n m x
    have hmul : (n * m).toAdd = n.toAdd + m.toAdd := rfl
    change
      (fun y : E => relaxModule target σ y)^[(n * m).toAdd] x =
        (fun y : E => relaxModule target σ y)^[n.toAdd]
          ((fun y : E => relaxModule target σ y)^[m.toAdd] x)
    rw [hmul]
    rw [Function.iterate_add_apply]

/-- THEOREM 1: the action's pointwise meaning is ordinary finite iteration. -/
theorem relaxationIterationMulAction_smul
    (target : E) (σ : K) (n : Multiplicative ℕ) (x : E) :
    (relaxationIterationMulAction target σ).smul n x =
      (fun y : E => relaxModule target σ y)^[n.toAdd] x := rfl

/-- THEOREM 2: the action at `n` equals a single relaxation using the
homomorphic effective rate from P304. -/
theorem relaxationIterationMulAction_eq_effectiveRate
    (target : E) {σ : K} (hσ : σ ≠ 1)
    (n : Multiplicative ℕ) (x : E) :
    (relaxationIterationMulAction target σ).smul n x =
      relaxModule target (iteratedRateMonoidHom σ hσ n).1 x := by
  rw [relaxationIterationMulAction_smul]
  exact relaxModule_iterate_eq_single_iteratedRate target σ x n.toAdd

/-- THEOREM 3: the generator action is one ordinary relaxation step. -/
theorem relaxationIterationMulAction_generator
    (target : E) (σ : K) (x : E) :
    (relaxationIterationMulAction target σ).smul
        (Multiplicative.ofAdd 1) x =
      relaxModule target σ x := by
  rfl

/-- THEOREM 4: serializing iteration actions is exactly the `MulAction`
composition law. -/
theorem relaxationIterationMulAction_serial
    (target : E) (σ : K) (n m : Multiplicative ℕ) (x : E) :
    (relaxationIterationMulAction target σ).smul (n * m) x =
      (relaxationIterationMulAction target σ).smul n
        ((relaxationIterationMulAction target σ).smul m x) := by
  exact (relaxationIterationMulAction target σ).mul_smul n m x

/-- A compact certificate for the carrier action induced by iteration counts.
-/
structure RelaxationIterationActionCertificate
    (target : E) (σ : K) (hσ : σ ≠ 1) where
  action : MulAction (Multiplicative ℕ) E :=
    relaxationIterationMulAction target σ
  pointwise :
    ∀ (n : Multiplicative ℕ) (x : E),
      action.smul n x =
        (fun y : E => relaxModule target σ y)^[n.toAdd] x
  effectiveRate :
    ∀ (n : Multiplicative ℕ) (x : E),
      action.smul n x =
        relaxModule target (iteratedRateMonoidHom σ hσ n).1 x
  generator :
    ∀ x : E, action.smul (Multiplicative.ofAdd 1) x =
      relaxModule target σ x
  serial :
    ∀ (n m : Multiplicative ℕ) (x : E),
      action.smul (n * m) x = action.smul n (action.smul m x)

/-- THEOREM 5: the canonical action certificate. -/
def relaxationIterationActionCertificate
    (target : E) (σ : K) (hσ : σ ≠ 1) :
    RelaxationIterationActionCertificate target σ hσ where
  action := relaxationIterationMulAction target σ
  pointwise := relaxationIterationMulAction_smul target σ
  effectiveRate := relaxationIterationMulAction_eq_effectiveRate target hσ
  generator := relaxationIterationMulAction_generator target σ
  serial := relaxationIterationMulAction_serial target σ

end AffineRelaxation
end SaturationMonoid
