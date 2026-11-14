import H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.CokernelTorsion.CoherentKernel
import Mathlib.RingTheory.Noetherian.Basic

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedPrimePowerCompletion

variable {L M : Type u} [AddCommGroup L] [AddCommGroup M]

/-- Stabilize the original source torsion stages inside the source torsion submodule. -/
theorem source_prime_torsion_bounded [IsNoetherian ℤ (Submodule.torsion ℤ L)] (p : Nat.Primes) :
    ∃ d : Nat, ∀ j (value : PrimePowerTorsionSubmodule L p j), (p.1 : ℤ)^d • value.val = 0 := by
  let S := Submodule.torsion ℤ L
  let stages : ℕ →o Submodule ℤ S :=
    { toFun := fun j => (PrimePowerTorsionSubmodule L p j).comap S.subtype
      monotone' := fun j k increases => Submodule.comap_mono
        (Submodule.torsionBy_le_torsionBy_of_dvd _ _ (pow_dvd_pow _ (Nat.succ_le_succ increases))) }
  obtain ⟨k, stable⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance stages
  refine ⟨k+1, fun j value => ?_⟩
  have nonzero : (p.1 : ℤ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  let member : S := ⟨value.val, (Submodule.mem_torsion_iff (R := ℤ) value.val).mpr
    ⟨⟨_, mem_nonZeroDivisors_of_ne_zero (pow_ne_zero (j+1) nonzero)⟩, value.property⟩⟩
  have larger : member ∈ stages (max j k) := stages.monotone (le_max_left j k) value.property
  rw [← stable _ (le_max_right j k)] at larger
  exact larger

theorem cokernel_connecting_limit_kernel [IsNoetherian ℤ (Submodule.torsion ℤ L)]
    (evaluate : L →ₗ[ℤ] M) (injective : Function.Injective evaluate) (p : Nat.Primes) :
    LinearMap.range (ambientToCokernelAtLimit evaluate p) =
      LinearMap.ker (cokernelConnectingAtLimit evaluate injective p) := by
  obtain ⟨d, bounded⟩ := source_prime_torsion_bounded (L := L) p
  exact cokernel_connecting_limit_kernel_of_bounded evaluate injective p d bounded

theorem ambient_to_cokernel_limit_injective [IsNoetherian ℤ (Submodule.torsion ℤ L)]
    (evaluate : L →ₗ[ℤ] M) (injective : Function.Injective evaluate) (p : Nat.Primes) :
    Function.Injective (ambientToCokernelAtLimit evaluate p) := by
  obtain ⟨d, bounded⟩ := source_prime_torsion_bounded (L := L) p
  exact ambient_to_cokernel_limit_injective_of_bounded evaluate injective p d bounded

end SourceGeneratedPrimePowerCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
