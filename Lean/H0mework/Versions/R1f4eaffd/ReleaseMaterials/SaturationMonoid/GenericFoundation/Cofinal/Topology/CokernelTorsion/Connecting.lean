import H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.CokernelTorsion
import Mathlib.LinearAlgebra.Isomorphisms

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedPrimePowerCompletion

variable {L M : Type u} [AddCommGroup L] [AddCommGroup M]

private abbrev TorsionLifts (evaluate : L →ₗ[ℤ] M) (p : Nat.Primes) (j : Nat) :=
  (LinearMap.range evaluate).comap (powerMultiplication (L := M) p j)

private def liftProjection (evaluate : L →ₗ[ℤ] M) (p : Nat.Primes) (j : Nat) :
    TorsionLifts evaluate p j →ₗ[ℤ] CokernelTorsion evaluate p j :=
  let quotient := (LinearMap.range evaluate).mkQ
  LinearMap.codRestrict _ (quotient.comp (TorsionLifts evaluate p j).subtype) (by
    intro lift
    change (p.1 : ℤ)^(j+1) • quotient lift.val = 0
    rw [← map_smul]
    exact (Submodule.Quotient.mk_eq_zero _).mpr lift.property)

private theorem lift_projection_surjective (evaluate : L →ₗ[ℤ] M) (p : Nat.Primes) (j : Nat) :
    Function.Surjective (liftProjection evaluate p j) := by
  intro value
  let quotient := (LinearMap.range evaluate).mkQ
  obtain ⟨raw, represented⟩ := (LinearMap.range evaluate).mkQ_surjective value.val
  have paid : powerMultiplication p j raw ∈ LinearMap.range evaluate := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change quotient ((p.1 : ℤ)^(j+1) • raw) = 0
    rw [map_smul, represented]
    exact value.property
  exact ⟨⟨raw, paid⟩, Subtype.ext represented⟩

/-- An actual division receipt supplies a representative in the existing torsion submodule. -/
def cokernelTorsionClassOfDivision (evaluate : L →ₗ[ℤ] M) (p : Nat.Primes) (j : Nat)
    (word : L) (divided : M) (paid : powerMultiplication p j divided = evaluate word) :
    CokernelTorsion evaluate p j :=
  liftProjection evaluate p j ⟨divided, ⟨word, paid.symm⟩⟩

theorem cokernel_torsion_class_val (evaluate : L →ₗ[ℤ] M) (p : Nat.Primes) (j : Nat)
    (word : L) (divided : M) (paid : powerMultiplication p j divided = evaluate word) :
    (cokernelTorsionClassOfDivision evaluate p j word divided paid).val =
      (LinearMap.range evaluate).mkQ divided := rfl

theorem cokernel_torsion_has_division (evaluate : L →ₗ[ℤ] M) (p : Nat.Primes) (j : Nat)
    (value : CokernelTorsion evaluate p j) :
    ∃ word divided, ∃ paid : powerMultiplication p j divided = evaluate word,
      cokernelTorsionClassOfDivision evaluate p j word divided paid = value := by
  obtain ⟨lift, projected⟩ := lift_projection_surjective evaluate p j value
  obtain ⟨word, paid⟩ := lift.property
  exact ⟨word, lift.val, paid.symm, projected⟩

private def liftMultiplication (evaluate : L →ₗ[ℤ] M) (p : Nat.Primes) (j : Nat) :
    TorsionLifts evaluate p j →ₗ[ℤ] LinearMap.range evaluate :=
  LinearMap.codRestrict _ ((powerMultiplication p j).comp (TorsionLifts evaluate p j).subtype)
    (fun lift => lift.property)

private def liftRead (evaluate : L →ₗ[ℤ] M) (injective : Function.Injective evaluate)
    (p : Nat.Primes) (j : Nat) :
    TorsionLifts evaluate p j →ₗ[ℤ] StageResidual (L := L) p j :=
  (stageProjection p j).comp ((LinearEquiv.ofInjective evaluate injective).symm.toLinearMap.comp
    (liftMultiplication evaluate p j))

private theorem lift_read_of_paid (evaluate : L →ₗ[ℤ] M) (injective : Function.Injective evaluate)
    (p : Nat.Primes) (j : Nat) (lift : TorsionLifts evaluate p j) (word : L)
    (paid : powerMultiplication p j lift.val = evaluate word) :
    liftRead evaluate injective p j lift = stageProjection p j word := by
  let rangeEquiv := LinearEquiv.ofInjective evaluate injective
  have same : liftMultiplication evaluate p j lift = rangeEquiv word := Subtype.ext paid
  exact (congrArg (fun value => stageProjection p j (rangeEquiv.symm value)) same).trans
    (congrArg (stageProjection p j) (rangeEquiv.symm_apply_apply word))

private theorem lift_read_kills_projection_kernel (evaluate : L →ₗ[ℤ] M)
    (injective : Function.Injective evaluate) (p : Nat.Primes) (j : Nat) :
    LinearMap.ker (liftProjection evaluate p j) ≤ LinearMap.ker (liftRead evaluate injective p j) := by
  intro lift zero
  have gone : liftProjection evaluate p j lift = 0 := LinearMap.mem_ker.mp zero
  have quotient : (LinearMap.range evaluate).mkQ lift.val = 0 := congrArg Subtype.val gone
  obtain ⟨word, paid⟩ := (Submodule.Quotient.mk_eq_zero _).mp quotient
  have multiplied : powerMultiplication p j lift.val = evaluate (powerMultiplication p j word) :=
    (congrArg (powerMultiplication p j) paid.symm).trans (map_smul evaluate ((p.1 : ℤ)^(j+1)) word).symm
  apply LinearMap.mem_ker.mpr
  exact (lift_read_of_paid evaluate injective p j lift _ multiplied).trans
    ((stageProjection_eq_zero_iff p j _).mpr ⟨word, rfl⟩)

/-- The connecting map lifts a torsion class and reads its original multiplied source. -/
def stageCokernelConnecting (evaluate : L →ₗ[ℤ] M) (injective : Function.Injective evaluate)
    (p : Nat.Primes) (j : Nat) :
    CokernelTorsion evaluate p j →ₗ[ℤ] StageResidual (L := L) p j :=
  let project := liftProjection evaluate p j
  let quotient := project.quotKerEquivOfSurjective (lift_projection_surjective evaluate p j)
  let read := (LinearMap.ker project).liftQ (liftRead evaluate injective p j)
    (lift_read_kills_projection_kernel evaluate injective p j)
  read.comp quotient.symm.toLinearMap

theorem stage_cokernel_connecting_of_paid (evaluate : L →ₗ[ℤ] M) (injective : Function.Injective evaluate)
    (p : Nat.Primes) (j : Nat) (word : L) (divided : M)
    (paid : powerMultiplication p j divided = evaluate word) :
    stageCokernelConnecting evaluate injective p j
      (cokernelTorsionClassOfDivision evaluate p j word divided paid) = stageProjection p j word := by
  let lift : TorsionLifts evaluate p j := ⟨divided, ⟨word, paid.symm⟩⟩
  let project := liftProjection evaluate p j
  let onto := lift_projection_surjective evaluate p j
  let read := (LinearMap.ker project).liftQ (liftRead evaluate injective p j)
    (lift_read_kills_projection_kernel evaluate injective p j)
  change read ((project.quotKerEquivOfSurjective onto).symm (project lift)) = _
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  exact lift_read_of_paid evaluate injective p j lift word paid

end SourceGeneratedPrimePowerCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
