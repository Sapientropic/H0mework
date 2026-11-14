import H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.CokernelTorsion.Tower

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedPrimePowerCompletion

variable {L M : Type u} [AddCommGroup L] [AddCommGroup M]

private theorem power_surjective_of_prime (p : Nat.Primes)
    (surjective : Function.Surjective (fun value : M => (p.1 : ℤ) • value)) (j : Nat) :
    Function.Surjective (powerMultiplication (L := M) p j) := by
  induction j with
  | zero =>
    intro value
    obtain ⟨divided, paid⟩ := surjective value
    refine ⟨divided, ?_⟩
    change (p.1 : ℤ)^1 • divided = value
    exact (congrArg (fun scalar : ℤ => scalar • divided) (pow_one _)).trans paid
  | succ j previous =>
    intro value
    obtain ⟨prior, written⟩ := previous value
    obtain ⟨divided, paid⟩ := surjective prior
    have division : (p.1 : ℤ) • divided = prior := paid
    refine ⟨divided, ?_⟩
    calc
      _ = powerMultiplication p j ((p.1 : ℤ) • divided) := by
        change (p.1 : ℤ)^(j+1+1) • divided = (p.1 : ℤ)^(j+1) • ((p.1 : ℤ) • divided)
        rw [pow_succ, mul_smul]
      _ = _ := (congrArg (powerMultiplication p j) division).trans written

theorem cokernel_connecting_stage_surjective (evaluate : L →ₗ[ℤ] M)
    (injective : Function.Injective evaluate) (p : Nat.Primes)
    (surjective : Function.Surjective (fun value : M => (p.1 : ℤ) • value)) (j : Nat) :
    Function.Surjective (stageCokernelConnecting evaluate injective p j) :=
  cokernel_connecting_surjective_of_source_division evaluate injective p j
    (fun word => power_surjective_of_prime p surjective j (evaluate word))

theorem prime_power_torsion_restriction_surjective (p : Nat.Primes) (j : Nat)
    (surjective : Function.Surjective (fun value : M => (p.1 : ℤ) • value)) :
    Function.Surjective (primePowerTorsionRestriction (M := M) p j) := by
  intro value
  obtain ⟨divided, paid⟩ := surjective value.val
  have exactDivision : (p.1 : ℤ) • divided = value.val := paid
  have torsion : (p.1 : ℤ)^(j+1+1) • divided = 0 := by
    rw [pow_succ, mul_smul, exactDivision]
    exact value.property
  exact ⟨⟨divided, torsion⟩, Subtype.ext exactDivision⟩

/-- A genuine ambient division lifts the kernel correction between two compatible stages. -/
theorem cokernel_connecting_lift_step (evaluate : L →ₗ[ℤ] M)
    (injective : Function.Injective evaluate) (p : Nat.Primes)
    (surjective : Function.Surjective (fun value : M => (p.1 : ℤ) • value)) (j : Nat)
    (lower : CokernelTorsion evaluate p j) (upper : StageResidual (L := L) p (j+1))
    (compatible : stageCokernelConnecting evaluate injective p j lower = transition p j upper) :
    ∃ lifted : CokernelTorsion evaluate p (j+1),
      primePowerTorsionRestriction p j lifted = lower ∧
      stageCokernelConnecting evaluate injective p (j+1) lifted = upper := by
  let read := stageCokernelConnecting evaluate injective p j
  let restrict := primePowerTorsionRestriction (M := M ⧸ LinearMap.range evaluate) p j
  obtain ⟨chosen, reads⟩ := cokernel_connecting_stage_surjective evaluate injective p surjective (j+1) upper
  let excess := restrict chosen - lower
  have same : read (restrict chosen) = read lower :=
    (cokernel_connecting_restriction evaluate injective p j chosen).trans
      ((congrArg (transition p j) reads).trans compatible.symm)
  have excessZero : read excess = 0 := by
    change read (restrict chosen - lower) = 0
    rw [map_sub, same, sub_self]
  have excessMem : excess ∈ LinearMap.range (ambientToCokernelTorsion evaluate p j) :=
    (cokernel_connecting_kernel evaluate injective p j).ge (LinearMap.mem_ker.mpr excessZero)
  obtain ⟨ambientLower, present⟩ := excessMem
  obtain ⟨ambientUpper, drops⟩ := prime_power_torsion_restriction_surjective p j surjective ambientLower
  let correction := ambientToCokernelTorsion evaluate p (j+1) ambientUpper
  have correctionDrop : restrict correction = excess :=
    (prime_power_torsion_map_restriction (LinearMap.range evaluate).mkQ p j ambientUpper).trans
      ((congrArg (ambientToCokernelTorsion evaluate p j) drops).trans present)
  have correctionZero : stageCokernelConnecting evaluate injective p (j+1) correction = 0 :=
    LinearMap.mem_ker.mp ((cokernel_connecting_kernel evaluate injective p (j+1)).le ⟨ambientUpper, rfl⟩)
  refine ⟨chosen - correction, ?_, ?_⟩
  · change restrict (chosen - correction) = lower
    rw [map_sub, correctionDrop]
    exact sub_sub_cancel _ _
  · rw [map_sub, reads, correctionZero, sub_zero]

end SourceGeneratedPrimePowerCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
