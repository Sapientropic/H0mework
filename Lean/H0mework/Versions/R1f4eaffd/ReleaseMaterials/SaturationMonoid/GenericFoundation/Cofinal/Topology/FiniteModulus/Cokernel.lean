import H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.FiniteModulus.Completion
import H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.CokernelTorsion.CoherentEquivalence

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CofinalAllPrimeTopology

open SourceGeneratedPrimePowerCompletion

variable {L M L' M' : Type u} [AddCommGroup L] [AddCommGroup M] [AddCommGroup L'] [AddCommGroup M']
variable (evaluate : L →ₗ[ℤ] M) (injective : Function.Injective evaluate)
variable (divides : ∀ p j, Function.Bijective (powerMultiplication (L := M) p j))

abbrev AllPrimeCokernel (evaluate : L →ₗ[ℤ] M) :=
  (p : Nat.Primes) → PrimePowerTorsionCompletion (M ⧸ LinearMap.range evaluate) p

/-- The original coherent cokernel equivalences recover the entire all-prime family at once. -/
def allPrimeCokernelEquiv : AllPrimeCompletion L ≃ₗ[ℤ] AllPrimeCokernel evaluate :=
  (AddEquiv.piCongrRight fun p => (cokernelCompletionEquiv evaluate injective p (divides p)).toAddEquiv).toIntLinearEquiv

theorem all_prime_cokernel_roundtrip (family : AllPrimeCokernel evaluate) (p : Nat.Primes) :
    cokernelCompletionEquiv evaluate injective p (divides p)
      ((allPrimeCokernelEquiv evaluate injective divides).symm family p) = family p :=
  congrFun ((allPrimeCokernelEquiv evaluate injective divides).apply_symm_apply family) p

variable (primes : Finset Nat.Primes) (depth : primes → Nat)
variable (coordinate : L ≃ₗ[ℤ] ℤ) (family : AllPrimeCokernel evaluate)

/-- The inverse on the original cofinal cokernel feeds the original integral representative. -/
def finiteCokernelCharge : L :=
  finitePrimeIntegralLift primes depth coordinate ((allPrimeCokernelEquiv evaluate injective divides).symm family)

theorem finite_cokernel_charge_stage (p : primes) :
    (torsionCompletionRestriction (M ⧸ LinearMap.range evaluate) p.val (depth p)).hom (family p.val) =
      stageCokernelEquiv evaluate injective p.val (depth p) (divides p.val (depth p))
        (stageProjection p.val (depth p) (finiteCokernelCharge evaluate injective divides primes depth coordinate family)) := by
  let connected := (allPrimeCokernelEquiv evaluate injective divides).symm family
  let restrictionAt := (torsionCompletionRestriction (M ⧸ LinearMap.range evaluate) p.val (depth p)).hom
  let stageRead := stageCokernelEquiv evaluate injective p.val (depth p) (divides p.val (depth p))
  have integralRead := congrFun (finite_prime_integral_lift primes depth coordinate connected).1 p
  exact (congrArg restrictionAt (all_prime_cokernel_roundtrip evaluate injective divides family p.val).symm).trans
    ((cokernel_completion_restriction evaluate injective p.val (divides p.val) (depth p) (connected p.val)).trans
      (congrArg stageRead integralRead.symm))

/-- The same integral representative computes the next cokernel stage under the actual source action. -/
theorem finite_cokernel_charge_successor (nextEvaluation : L' →ₗ[ℤ] M')
    (nextInjective : Function.Injective nextEvaluation)
    (nextDivides : ∀ p j, Function.Bijective (powerMultiplication (L := M') p j))
    (action : L →ₗ[ℤ] L') (p : primes) :
    let connected := (allPrimeCokernelEquiv evaluate injective divides).symm family
    let moved := allPrimeSuccessor action connected
    (torsionCompletionRestriction (M' ⧸ LinearMap.range nextEvaluation) p.val (depth p)).hom
      (allPrimeCokernelEquiv nextEvaluation nextInjective nextDivides moved p.val) =
      stageCokernelEquiv nextEvaluation nextInjective p.val (depth p) (nextDivides p.val (depth p))
        (stageProjection p.val (depth p)
          (action (finiteCokernelCharge evaluate injective divides primes depth coordinate family))) := by
  let connected := (allPrimeCokernelEquiv evaluate injective divides).symm family
  let charge := finiteCokernelCharge evaluate injective divides primes depth coordinate family
  let moved := allPrimeSuccessor action connected
  let stageRead := stageCokernelEquiv nextEvaluation nextInjective p.val (depth p) (nextDivides p.val (depth p))
  have sourceRead := (finite_prime_integral_lift primes depth coordinate connected).1
  have write := congrFun (finite_prime_successor primes depth action connected charge sourceRead) p
  exact (cokernel_completion_restriction nextEvaluation nextInjective p.val (nextDivides p.val) (depth p)
    (moved p.val)).trans (congrArg stageRead write.symm)

end CofinalAllPrimeTopology
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
