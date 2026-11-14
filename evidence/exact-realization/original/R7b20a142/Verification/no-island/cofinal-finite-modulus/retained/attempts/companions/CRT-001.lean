import SaturationMonoid.GenericFoundation.Cofinal.Topology.Successor
import Mathlib.RingTheory.Ideal.Quotient.ChineseRemainder
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CofinalAllPrimeTopology

open SourceGeneratedPrimePowerCompletion
open scoped BigOperators Pointwise TensorProduct

variable {L : Type u} [AddCommGroup L]
variable (primes : Finset Nat.Primes) (depth : primes → Nat)

private def primeModulus (p : primes) : ℤ := (p.val.val : ℤ) ^ (depth p + 1)

/-- The composite modulus is computed from the actual finite prime-power observations. -/
def compositeModulus : ℤ := ∏ p : primes, primeModulus primes depth p

theorem composite_modulus_pos : 0 < compositeModulus primes depth :=
  Finset.prod_pos (fun p _ => pow_pos (Int.ofNat_pos.mpr p.val.property.pos) _)

private def primeIdeal (p : primes) : Ideal ℤ := Ideal.span {primeModulus primes depth p}

private theorem prime_moduli_coprime : Pairwise (fun p q : primes =>
    IsCoprime (primeModulus primes depth p) (primeModulus primes depth q)) := by
  intro p q distinct
  have different : p.val.val ≠ q.val.val := fun same => distinct (Subtype.ext (Subtype.ext same))
  have powers := Nat.coprime_pow_primes (depth p + 1) (depth q + 1) p.val.property q.val.property different
  simpa only [Nat.cast_pow] using powers.isCoprime

private theorem prime_ideals_coprime : Pairwise (fun p q : primes =>
    IsCoprime (primeIdeal primes depth p) (primeIdeal primes depth q)) := by
  intro p q distinct
  exact (Ideal.isCoprime_span_singleton_iff _ _).2 (prime_moduli_coprime primes depth distinct)

private theorem principal_smul_top (m : ℤ) :
    (Ideal.span {m}) • (⊤ : Submodule ℤ L) = LinearMap.range (DistribSMul.toLinearMap ℤ L m) := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.pointwise_smul_def, Submodule.map_top]

/-- Every component is the original integral stage projection. -/
def finitePrimeProjection : L →ₗ[ℤ] ((p : primes) → StageResidual (L := L) p.val (depth p)) :=
  LinearMap.pi fun p => stageProjection p.val (depth p)

private def tensorStage (p : primes) :
    ((ℤ ⧸ primeIdeal primes depth p) ⊗[ℤ] L) ≃ₗ[ℤ] StageResidual (L := L) p.val (depth p) :=
  (TensorProduct.quotTensorEquivQuotSMul L (primeIdeal primes depth p)).trans
    (Submodule.quotEquivOfEq _ _ (by
      rw [primeIdeal, principal_smul_top]
      exact congrArg LinearMap.range (LinearMap.ext fun _ => rfl)))

private def tensorProjection : L →ₗ[ℤ] ((p : primes) → ((ℤ ⧸ primeIdeal primes depth p) ⊗[ℤ] L)) :=
  LinearMap.pi fun p => TensorProduct.mk ℤ (ℤ ⧸ primeIdeal primes depth p) L 1

private theorem finite_prime_projection_tensor : finitePrimeProjection (L := L) primes depth =
    (LinearEquiv.piCongrRight (tensorStage (L := L) primes depth)).toLinearMap.comp
      (tensorProjection primes depth) := by
  apply LinearMap.ext
  intro value
  funext p
  change stageProjection p.val (depth p) value = tensorStage primes depth p (1 ⊗ₜ[ℤ] value)
  simp only [tensorStage, LinearEquiv.trans_apply, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul,
    Submodule.quotEquivOfEq_mk, stageProjection, Submodule.mkQ_apply]

/-- An arbitrary simultaneous finite residue family is realized by one original source value. -/
theorem finite_prime_projection_surjective : Function.Surjective (finitePrimeProjection (L := L) primes depth) := by
  rw [finite_prime_projection_tensor]
  exact (LinearEquiv.piCongrRight (tensorStage (L := L) primes depth)).surjective.comp
    (Ideal.pi_tensorProductMk_quotient_surjective L _ (prime_ideals_coprime primes depth))

/-- The entire ambiguity is the single composite-modulus ideal acting on the source. -/
theorem finite_prime_projection_kernel : (finitePrimeProjection (L := L) primes depth).ker =
    Ideal.span {compositeModulus primes depth} • (⊤ : Submodule ℤ L) := by
  have tensorKernel : (tensorProjection (L := L) primes depth).ker =
      (⨅ p : primes, primeIdeal primes depth p) • (⊤ : Submodule ℤ L) :=
    Ideal.ker_tensorProductMk_quotient L _ (prime_ideals_coprime primes depth)
  have sameKernel : (finitePrimeProjection (L := L) primes depth).ker =
      (tensorProjection (L := L) primes depth).ker := by
    rw [finite_prime_projection_tensor]
    let read := LinearEquiv.piCongrRight (tensorStage (L := L) primes depth)
    ext value
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, LinearEquiv.coe_coe]
    exact ⟨fun zero => read.injective (zero.trans (map_zero read).symm), fun zero => by rw [zero, map_zero]⟩
  have composite : (⨅ p : primes, primeIdeal primes depth p) = Ideal.span {compositeModulus primes depth} :=
    Ideal.iInf_span_singleton (fun p q distinct => prime_moduli_coprime primes depth distinct)
  exact sameKernel.trans (tensorKernel.trans (congrArg (fun ideal : Ideal ℤ => ideal • (⊤ : Submodule ℤ L)) composite))

def finitePrimeEquiv : (L ⧸ Ideal.span {compositeModulus primes depth} • (⊤ : Submodule ℤ L)) ≃ₗ[ℤ]
    ((p : primes) → StageResidual (L := L) p.val (depth p)) :=
  (Submodule.quotEquivOfEq _ _ (finite_prime_projection_kernel (L := L) primes depth).symm).trans
    ((finitePrimeProjection primes depth).quotKerEquivOfSurjective (finite_prime_projection_surjective primes depth))

theorem finite_prime_equiv_projection (value : L) :
    finitePrimeEquiv primes depth (Submodule.Quotient.mk value) = finitePrimeProjection primes depth value :=
  LinearMap.quotKerEquivOfSurjective_apply_mk _ _ value

theorem finite_prime_fibre (left right : L) :
    finitePrimeProjection primes depth left = finitePrimeProjection primes depth right ↔
      ∃ divided : L, compositeModulus primes depth • divided = left - right := by
  rw [← sub_eq_zero, ← map_sub, ← LinearMap.mem_ker, finite_prime_projection_kernel, principal_smul_top]
  rfl

end CofinalAllPrimeTopology
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
