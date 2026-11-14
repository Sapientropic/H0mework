import H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.CokernelTorsion.Connecting

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedPrimePowerCompletion

open CofinalAllPrimeTopology

variable {L M : Type u} [AddCommGroup L] [AddCommGroup M]

abbrev PrimePowerTorsionSubmodule (A : Type u) [AddCommGroup A] (p : Nat.Primes) (j : Nat) :=
  Submodule.torsionBy ℤ A ((p.1 : ℤ)^(j+1))

local notation "Tor" "[" A "," p "," j "]" => PrimePowerTorsionSubmodule A p j

def primePowerTorsionMap (move : L →ₗ[ℤ] M) (p : Nat.Primes) (j : Nat) :
    Tor[L, p, j] →ₗ[ℤ] Tor[M, p, j] :=
  LinearMap.codRestrict _ (move.comp (Tor[L, p, j]).subtype) (by
    intro value
    change (p.1 : ℤ)^(j+1) • move value.val = 0
    have paid : (p.1 : ℤ)^(j+1) • value.val = 0 := value.property
    exact ((map_smul move _ _).symm.trans (congrArg move paid)).trans (map_zero move))

abbrev ambientToCokernelTorsion (evaluate : L →ₗ[ℤ] M) (p : Nat.Primes) (j : Nat) :
    Tor[M, p, j] →ₗ[ℤ] CokernelTorsion evaluate p j :=
  primePowerTorsionMap (LinearMap.range evaluate).mkQ p j

theorem source_ambient_torsion_exact (evaluate : L →ₗ[ℤ] M)
    (injective : Function.Injective evaluate) (p : Nat.Primes) (j : Nat) :
    LinearMap.range (primePowerTorsionMap evaluate p j) =
      LinearMap.ker (ambientToCokernelTorsion evaluate p j) := by
  ext value
  rw [LinearMap.mem_ker]
  constructor
  · rintro ⟨source, rfl⟩
    apply Subtype.ext
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨source.val, rfl⟩
  · intro zero
    have invisible : (LinearMap.range evaluate).mkQ value.val = 0 := congrArg Subtype.val zero
    obtain ⟨source, present⟩ := (Submodule.Quotient.mk_eq_zero _).mp invisible
    have torsion : (p.1 : ℤ)^(j+1) • source = 0 := injective <|
      (map_smul evaluate _ _).trans <|
        (congrArg (fun point => (p.1 : ℤ)^(j+1) • point) present).trans <|
          value.property.trans (map_zero evaluate).symm
    exact ⟨⟨source, torsion⟩, Subtype.ext present⟩

/-- The ambiguity of reading a torsion class consists of the ambient torsion itself. -/
theorem cokernel_connecting_kernel (evaluate : L →ₗ[ℤ] M)
    (injective : Function.Injective evaluate) (p : Nat.Primes) (j : Nat) :
    LinearMap.range (ambientToCokernelTorsion evaluate p j) =
      LinearMap.ker (stageCokernelConnecting evaluate injective p j) := by
  let quotient := (LinearMap.range evaluate).mkQ
  ext value
  rw [LinearMap.mem_ker]
  constructor
  · rintro ⟨raw, rfl⟩
    have paid : powerMultiplication p j raw.val = evaluate 0 :=
      raw.property.trans (map_zero evaluate).symm
    change stageCokernelConnecting evaluate injective p j
      (cokernelTorsionClassOfDivision evaluate p j 0 raw.val paid) = 0
    exact (stage_cokernel_connecting_of_paid evaluate injective p j 0 raw.val paid).trans (map_zero _)
  · intro zero
    obtain ⟨word, divided, paid, rfl⟩ := cokernel_torsion_has_division evaluate p j value
    have sourceZero : stageProjection p j word = 0 :=
      (stage_cokernel_connecting_of_paid evaluate injective p j word divided paid).symm.trans zero
    obtain ⟨previous, written⟩ := (stageProjection_eq_zero_iff p j word).mp sourceZero
    let raw := divided - evaluate previous
    have second : (p.1 : ℤ)^(j+1) • evaluate previous = evaluate word :=
      (map_smul evaluate _ _).symm.trans (congrArg evaluate written)
    have torsion : (p.1 : ℤ)^(j+1) • raw = 0 := by
      dsimp only [raw]
      rw [smul_sub, second]
      exact sub_eq_zero.mpr paid
    refine ⟨⟨raw, torsion⟩, Subtype.ext ?_⟩
    have paidZero : quotient (evaluate previous) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨previous, rfl⟩
    change quotient (divided - evaluate previous) = quotient divided
    rw [map_sub, paidZero, sub_zero]

/-- The source classes that disappear at the ambient stage are exactly those read by the connecting map. -/
theorem cokernel_connecting_image (evaluate : L →ₗ[ℤ] M)
    (injective : Function.Injective evaluate) (p : Nat.Primes) (j : Nat) :
    LinearMap.range (stageCokernelConnecting evaluate injective p j) =
      LinearMap.ker (stageMap p j evaluate) := by
  ext value
  rw [LinearMap.mem_ker]
  constructor
  · rintro ⟨torsion, rfl⟩
    obtain ⟨word, divided, paid, rfl⟩ := cokernel_torsion_has_division evaluate p j torsion
    have read := stage_cokernel_connecting_of_paid evaluate injective p j word divided paid
    exact (congrArg (stageMap p j evaluate) read).trans
      ((stage_successor_apply p j evaluate word).trans
        ((stageProjection_eq_zero_iff p j (evaluate word)).mpr ⟨divided, paid⟩))
  · intro invisible
    obtain ⟨word, rfl⟩ := (powerRange (L := L) p j).mkQ_surjective value
    have zero : stageProjection p j (evaluate word) = 0 :=
      (stage_successor_apply p j evaluate word).symm.trans invisible
    obtain ⟨divided, paid⟩ := (stageProjection_eq_zero_iff p j (evaluate word)).mp zero
    exact ⟨cokernelTorsionClassOfDivision evaluate p j word divided paid,
      stage_cokernel_connecting_of_paid evaluate injective p j word divided paid⟩

theorem cokernel_connecting_surjective_of_source_division (evaluate : L →ₗ[ℤ] M)
    (injective : Function.Injective evaluate) (p : Nat.Primes) (j : Nat)
    (divide : ∀ word, ∃ divided, powerMultiplication p j divided = evaluate word) :
    Function.Surjective (stageCokernelConnecting evaluate injective p j) := by
  intro value
  obtain ⟨word, rfl⟩ := (powerRange (L := L) p j).mkQ_surjective value
  obtain ⟨divided, paid⟩ := divide word
  exact ⟨cokernelTorsionClassOfDivision evaluate p j word divided paid,
    stage_cokernel_connecting_of_paid evaluate injective p j word divided paid⟩

theorem stage_cokernel_connecting_inverse (evaluate : L →ₗ[ℤ] M)
    (injective : Function.Injective evaluate) (p : Nat.Primes) (j : Nat)
    (ambient : Function.Bijective (powerMultiplication (L := M) p j)) :
    Function.LeftInverse (stageCokernelConnecting evaluate injective p j)
      (stageCokernelEquiv evaluate injective p j ambient) := by
  intro value
  obtain ⟨word, rfl⟩ := (powerRange (L := L) p j).mkQ_surjective value
  obtain ⟨divided, paid⟩ := ambient.2 (evaluate word)
  have same : stageCokernelEquiv evaluate injective p j ambient (stageProjection p j word) =
      cokernelTorsionClassOfDivision evaluate p j word divided paid :=
    Subtype.ext (stage_cokernel_of_divided evaluate injective p j ambient word divided paid)
  exact (congrArg (stageCokernelConnecting evaluate injective p j) same).trans
    (stage_cokernel_connecting_of_paid evaluate injective p j word divided paid)

end SourceGeneratedPrimePowerCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
