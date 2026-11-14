import H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.SplitAction
import Mathlib.Algebra.Module.Torsion.Basic

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedPrimePowerCompletion

variable {L M : Type u} [AddCommGroup L] [AddCommGroup M]

abbrev CokernelTorsion (evaluate : L →ₗ[ℤ] M) (p : Nat.Primes) (j : Nat) :=
  Submodule.torsionBy ℤ (M ⧸ LinearMap.range evaluate) ((p.1 : ℤ)^(j+1))

private def ambientPowerEquiv (p : Nat.Primes) (j : Nat)
    (ambient : Function.Bijective (powerMultiplication (L := M) p j)) : M ≃ₗ[ℤ] M :=
  LinearEquiv.ofBijective (powerMultiplication p j) ambient

private def cokernelWrite (evaluate : L →ₗ[ℤ] M) (p : Nat.Primes) (j : Nat)
    (ambient : Function.Bijective (powerMultiplication (L := M) p j)) :
    L →ₗ[ℤ] CokernelTorsion evaluate p j :=
  let divide := (ambientPowerEquiv p j ambient).symm.toLinearMap
  let quotient := (LinearMap.range evaluate).mkQ
  LinearMap.codRestrict _ (quotient.comp (divide.comp evaluate)) (by
    intro word
    apply (Submodule.mem_torsionBy_iff _ _).mpr
    have divided : (p.1 : ℤ)^(j+1) • divide (evaluate word) = evaluate word :=
      (ambientPowerEquiv p j ambient).apply_symm_apply _
    change (p.1 : ℤ)^(j+1) • quotient (divide (evaluate word)) = 0
    rw [← map_smul, divided]
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨word, rfl⟩)

private theorem cokernel_write_kernel (evaluate : L →ₗ[ℤ] M)
    (injective : Function.Injective evaluate) (p : Nat.Primes) (j : Nat)
    (ambient : Function.Bijective (powerMultiplication (L := M) p j)) :
    LinearMap.ker (cokernelWrite evaluate p j ambient) = powerRange p j := by
  let power := ambientPowerEquiv p j ambient
  ext word
  rw [LinearMap.mem_ker, Subtype.ext_iff]
  change (LinearMap.range evaluate).mkQ (power.symm (evaluate word)) = 0 ↔
    word ∈ powerRange p j
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨preimage, same⟩
    refine ⟨preimage, injective ?_⟩
    calc
      evaluate (powerMultiplication p j preimage) = power (evaluate preimage) := by
        change evaluate ((p.1 : ℤ)^(j+1) • preimage) = (p.1 : ℤ)^(j+1) • evaluate preimage
        exact map_smul evaluate _ _
      _ = power (power.symm (evaluate word)) := congrArg power same
      _ = _ := power.apply_symm_apply _
  · rintro ⟨preimage, rfl⟩
    refine ⟨preimage, power.injective ?_⟩
    rw [power.apply_symm_apply]
    change (p.1 : ℤ)^(j+1) • evaluate preimage = evaluate ((p.1 : ℤ)^(j+1) • preimage)
    exact (map_smul evaluate _ _).symm

/-- An injective actual evaluation transfers its full prime-power observation to its cokernel. -/
def stageCokernelEquiv (evaluate : L →ₗ[ℤ] M) (injective : Function.Injective evaluate)
    (p : Nat.Primes) (j : Nat)
    (ambient : Function.Bijective (powerMultiplication (L := M) p j)) :
    StageResidual (L := L) p j ≃ₗ[ℤ] CokernelTorsion evaluate p j := by
  let power := ambientPowerEquiv p j ambient
  let write := cokernelWrite evaluate p j ambient
  let sourceRange := powerRange (L := L) p j
  let ambientRange := LinearMap.range evaluate
  have kernel : sourceRange = LinearMap.ker write := (cokernel_write_kernel evaluate injective p j ambient).symm
  let descend := sourceRange.liftQ write kernel.le
  refine LinearEquiv.ofBijective descend ⟨LinearMap.ker_eq_bot.mp ?_, ?_⟩
  · exact sourceRange.ker_liftQ_eq_bot write kernel.le kernel.ge
  · intro torsion
    obtain ⟨raw, represented⟩ := ambientRange.mkQ_surjective torsion.val
    have paid : (p.1 : ℤ)^(j+1) • raw ∈ ambientRange := by
      apply (Submodule.Quotient.mk_eq_zero _).mp
      change ambientRange.mkQ ((p.1 : ℤ)^(j+1) • raw) = 0
      rw [map_smul, represented]
      exact torsion.property
    obtain ⟨word, written⟩ := paid
    refine ⟨stageProjection p j word, Subtype.ext ?_⟩
    change ambientRange.mkQ (power.symm (evaluate word)) = torsion.val
    have inverse : power.symm (evaluate word) = raw :=
      power.injective ((power.apply_symm_apply _).trans written)
    exact (congrArg ambientRange.mkQ inverse).trans represented

theorem stage_cokernel_of_divided (evaluate : L →ₗ[ℤ] M) (injective : Function.Injective evaluate)
    (p : Nat.Primes) (j : Nat) (ambient : Function.Bijective (powerMultiplication (L := M) p j))
    (word : L) (divided : M) (actual : powerMultiplication p j divided = evaluate word) :
    (stageCokernelEquiv evaluate injective p j ambient (stageProjection p j word)).val =
      (LinearMap.range evaluate).mkQ divided := by
  let power := ambientPowerEquiv p j ambient
  change (LinearMap.range evaluate).mkQ (power.symm (evaluate word)) =
    (LinearMap.range evaluate).mkQ divided
  exact congrArg (LinearMap.range evaluate).mkQ
    (power.injective ((power.apply_symm_apply _).trans actual.symm))

/-- Restriction of the original tower becomes multiplication by the same prime in the cokernel. -/
theorem stage_cokernel_transition (evaluate : L →ₗ[ℤ] M) (injective : Function.Injective evaluate)
    (p : Nat.Primes) (j : Nat)
    (current : Function.Bijective (powerMultiplication (L := M) p j))
    (next : Function.Bijective (powerMultiplication (L := M) p (j+1)))
    (value : StageResidual (L := L) p (j+1)) :
    (stageCokernelEquiv evaluate injective p j current (transition p j value)).val =
      (p.1 : ℤ) • (stageCokernelEquiv evaluate injective p (j+1) next value).val := by
  obtain ⟨word, rfl⟩ := (powerRange (L := L) p (j+1)).mkQ_surjective value
  let power := ambientPowerEquiv p (j+1) next
  let divided := power.symm (evaluate word)
  have upper : powerMultiplication p (j+1) divided = evaluate word := power.apply_symm_apply _
  have lower : powerMultiplication p j ((p.1 : ℤ) • divided) = evaluate word := by
    change (p.1 : ℤ)^(j+1) • ((p.1 : ℤ) • divided) = evaluate word
    rw [smul_smul, ← pow_succ]
    exact upper
  have restrict := LinearMap.congr_fun (transition_projection (L := L) p j) word
  change transition p j (stageProjection p (j+1) word) = stageProjection p j word at restrict
  let quotient := (LinearMap.range evaluate).mkQ
  calc
    _ = (stageCokernelEquiv evaluate injective p j current (stageProjection p j word)).val :=
      congrArg (fun stage => (stageCokernelEquiv evaluate injective p j current stage).val) restrict
    _ = quotient ((p.1 : ℤ) • divided) :=
      stage_cokernel_of_divided evaluate injective p j current word _ lower
    _ = (p.1 : ℤ) • quotient divided := map_smul quotient _ _
    _ = _ := congrArg (fun residue => (p.1 : ℤ) • residue)
      (stage_cokernel_of_divided evaluate injective p (j+1) next word _ upper).symm

end SourceGeneratedPrimePowerCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
