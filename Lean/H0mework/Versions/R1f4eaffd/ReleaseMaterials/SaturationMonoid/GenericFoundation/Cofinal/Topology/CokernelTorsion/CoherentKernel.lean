import H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.CokernelTorsion.Tower

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedPrimePowerCompletion

open CategoryTheory CategoryTheory.Limits

variable {L M : Type u} [AddCommGroup L] [AddCommGroup M]

local notation "Tor" "[" A "," p "," j "]" => PrimePowerTorsionSubmodule A p j

private theorem torsion_restriction_succ (p : Nat.Primes) (j : Nat)
    (value : PrimePowerTorsionCompletion M p) :
    primePowerTorsionRestriction p j ((torsionCompletionRestriction M p (j+1)).hom value) =
      (torsionCompletionRestriction M p j).hom value := by
  let arrow := (homOfLE (Nat.le_add_right j 1)).op
  have arrowEq : (primePowerTorsionTower M p).map arrow =
      ModuleCat.ofHom (primePowerTorsionRestriction p j) := Functor.ofOpSequence_map_homOfLE_succ _ j
  have square := limit.w (primePowerTorsionTower M p) arrow
  rw [arrowEq] at square
  exact ConcreteCategory.congr_hom square value

theorem torsion_restriction_power (p : Nat.Primes) (j d : Nat)
    (value : PrimePowerTorsionCompletion M p) :
    ((torsionCompletionRestriction M p j).hom value).val =
      (p.1 : ℤ)^d • ((torsionCompletionRestriction M p (j+d)).hom value).val := by
  induction d with
  | zero => rw [pow_zero, one_smul, Nat.add_zero]
  | succ d earlier =>
    have next := congrArg Subtype.val (torsion_restriction_succ p (j+d) value)
    change (p.1 : ℤ) • ((torsionCompletionRestriction M p (j+d+1)).hom value).val =
      ((torsionCompletionRestriction M p (j+d)).hom value).val at next
    rw [earlier, ← next, smul_smul, ← pow_succ, Nat.add_assoc]

private def torsionTowerMap (move : L →ₗ[ℤ] M) (p : Nat.Primes) :
    primePowerTorsionTower L p ⟶ primePowerTorsionTower M p :=
  NatTrans.ofOpSequence (fun j => ModuleCat.ofHom (primePowerTorsionMap move p j))
    (fun j => by
      simp only [primePowerTorsionTower, Functor.ofOpSequence_map_homOfLE_succ]
      apply ModuleCat.hom_ext
      exact LinearMap.ext fun value => (prime_power_torsion_map_restriction move p j value).symm)

def primePowerTorsionLimitMap (move : L →ₗ[ℤ] M) (p : Nat.Primes) :
    PrimePowerTorsionCompletion L p →ₗ[ℤ] PrimePowerTorsionCompletion M p :=
  (limMap (torsionTowerMap move p)).hom

theorem torsion_limit_map_restriction (move : L →ₗ[ℤ] M) (p : Nat.Primes) (j : Nat)
    (value : PrimePowerTorsionCompletion L p) :
    (torsionCompletionRestriction M p j).hom (primePowerTorsionLimitMap move p value) =
      primePowerTorsionMap move p j ((torsionCompletionRestriction L p j).hom value) :=
  ConcreteCategory.congr_hom (limMap_π (torsionTowerMap move p) (Opposite.op j)) value

abbrev ambientToCokernelAtLimit (evaluate : L →ₗ[ℤ] M) (p : Nat.Primes) :=
  primePowerTorsionLimitMap (LinearMap.range evaluate).mkQ p

private theorem ambient_difference_annihilated (evaluate : L →ₗ[ℤ] M)
    (injective : Function.Injective evaluate) (p : Nat.Primes) (d : Nat)
    (bounded : ∀ j (value : Tor[L, p, j]), (p.1 : ℤ)^d • value.val = 0)
    (j : Nat) (left right : Tor[M, p, j])
    (same : ambientToCokernelTorsion evaluate p j left = ambientToCokernelTorsion evaluate p j right) :
    (p.1 : ℤ)^d • left.val = (p.1 : ℤ)^d • right.val := by
  have invisible : left - right ∈ LinearMap.ker (ambientToCokernelTorsion evaluate p j) := by
    rw [LinearMap.mem_ker, map_sub, same, sub_self]
  rw [← source_ambient_torsion_exact evaluate injective p j] at invisible
  obtain ⟨source, produced⟩ := invisible
  have written : evaluate source.val = left.val - right.val := congrArg Subtype.val produced
  apply sub_eq_zero.mp
  rw [← smul_sub, ← written, ← map_smul, bounded j source, map_zero]

private theorem torsion_lift_coordinates (p : Nat.Primes)
    (rows : ∀ j, Tor[M, p, j])
    (consistent : ∀ j, primePowerTorsionRestriction p j (rows (j+1)) = rows j) :
    ∃ value : PrimePowerTorsionCompletion M p,
      ∀ j, (torsionCompletionRestriction M p j).hom value = rows j := by
  let diagram := primePowerTorsionTower M p
  let coordinates := Types.isLimitEquivSections
    (isLimitOfPreserves (forget (ModuleCat ℤ)) (limit.isLimit diagram))
  let actual : (diagram ⋙ forget (ModuleCat ℤ)).sections := Types.sectionOfCone
    { pt := PUnit
      π := NatTrans.ofOpSequence
        (fun j => ↾fun _ => rows j)
        (fun j => by
          ext point
          simp only [Functor.const_obj_map, Functor.comp_map, diagram, primePowerTorsionTower,
            Functor.ofOpSequence_map_homOfLE_succ]
          exact (consistent j).symm) } PUnit.unit
  exact ⟨coordinates.symm actual, fun j =>
    congrArg (fun sectionValue => sectionValue.val (Opposite.op j)) (coordinates.apply_symm_apply actual)⟩

/-- After a bounded source torsion shift, every coherent connecting-zero class has an ambient lift. -/
theorem cokernel_connecting_limit_kernel_of_bounded (evaluate : L →ₗ[ℤ] M)
    (injective : Function.Injective evaluate) (p : Nat.Primes) (d : Nat)
    (bounded : ∀ j (value : Tor[L, p, j]), (p.1 : ℤ)^d • value.val = 0) :
    LinearMap.range (ambientToCokernelAtLimit evaluate p) =
      LinearMap.ker (cokernelConnectingAtLimit evaluate injective p) := by
  ext value
  rw [LinearMap.mem_ker]
  constructor
  · rintro ⟨raw, rfl⟩
    apply Concrete.limit_ext (tower (L := L) p)
    rintro ⟨j⟩
    have projected : ambientToCokernelTorsion evaluate p j
        ((torsionCompletionRestriction M p j).hom raw) ∈
        LinearMap.ker (stageCokernelConnecting evaluate injective p j) := by
      rw [← cokernel_connecting_kernel evaluate injective p j]
      exact ⟨_, rfl⟩
    change (restriction (L := L) p j).hom
        (cokernelConnectingAtLimit evaluate injective p (ambientToCokernelAtLimit evaluate p raw)) = _
    rw [cokernel_connecting_limit_restriction, torsion_limit_map_restriction]
    exact (LinearMap.mem_ker.mp projected).trans (map_zero (restriction (L := L) p j).hom).symm
  · intro zero
    let C := M ⧸ LinearMap.range evaluate
    let observed (j : Nat) := (torsionCompletionRestriction C p j).hom value
    have choices (j : Nat) : ∃ raw : Tor[M, p, j],
        ambientToCokernelTorsion evaluate p j raw = observed j := by
      have silent : observed j ∈ LinearMap.ker (stageCokernelConnecting evaluate injective p j) := by
        rw [LinearMap.mem_ker, ← cokernel_connecting_limit_restriction evaluate injective p j value, zero, map_zero]
      rw [← cokernel_connecting_kernel evaluate injective p j] at silent
      exact silent
    choose raw selectedAt using choices
    let shifted (j : Nat) : Tor[M, p, j] := ⟨(p.1 : ℤ)^d • (raw (j+d)).val, by
      change (p.1 : ℤ)^(j+1) • ((p.1 : ℤ)^d • (raw (j+d)).val) = 0
      rw [smul_smul, ← pow_add, show j+1+d = j+d+1 by omega]
      exact (raw (j+d)).property⟩
    have consistent (j : Nat) : primePowerTorsionRestriction p j (shifted (j+1)) = shifted j := by
      let later := primePowerTorsionRestriction p (j+d) (raw (j+d+1))
      have same : ambientToCokernelTorsion evaluate p (j+d) later =
          ambientToCokernelTorsion evaluate p (j+d) (raw (j+d)) :=
        (prime_power_torsion_map_restriction (LinearMap.range evaluate).mkQ p (j+d) _).symm.trans
          ((congrArg (primePowerTorsionRestriction p (j+d)) (selectedAt (j+d+1))).trans
            ((torsion_restriction_succ p (j+d) value).trans (selectedAt (j+d)).symm))
      have paid := ambient_difference_annihilated evaluate injective p d bounded (j+d) later (raw (j+d)) same
      apply Subtype.ext
      change (p.1 : ℤ) • ((p.1 : ℤ)^d • (raw (j+1+d)).val) = (p.1 : ℤ)^d • (raw (j+d)).val
      rw [show j+1+d = j+d+1 by omega, smul_comm (p.1 : ℤ) ((p.1 : ℤ)^d)]
      exact paid
    obtain ⟨lifted, reads⟩ := torsion_lift_coordinates p shifted consistent
    refine ⟨lifted, ?_⟩
    apply Concrete.limit_ext (primePowerTorsionTower C p)
    rintro ⟨j⟩
    change (torsionCompletionRestriction C p j).hom (ambientToCokernelAtLimit evaluate p lifted) = observed j
    rw [torsion_limit_map_restriction, reads]
    apply Subtype.ext
    let quotient := (LinearMap.range evaluate).mkQ
    change quotient ((p.1 : ℤ)^d • (raw (j+d)).val) = (observed j).val
    rw [map_smul]
    exact (congrArg (fun x : C => (p.1 : ℤ)^d • x)
      (congrArg Subtype.val (selectedAt (j+d)))).trans (torsion_restriction_power p j d value).symm

/-- Coherent ambient lifts cannot differ by bounded source torsion. -/
theorem ambient_to_cokernel_limit_injective_of_bounded (evaluate : L →ₗ[ℤ] M)
    (injective : Function.Injective evaluate) (p : Nat.Primes) (d : Nat)
    (bounded : ∀ j (value : Tor[L, p, j]), (p.1 : ℤ)^d • value.val = 0) :
    Function.Injective (ambientToCokernelAtLimit evaluate p) := by
  intro left right same
  apply Concrete.limit_ext (primePowerTorsionTower M p)
  rintro ⟨j⟩
  have equal := congrArg (torsionCompletionRestriction (M ⧸ LinearMap.range evaluate) p (j+d)).hom same
  rw [torsion_limit_map_restriction, torsion_limit_map_restriction] at equal
  apply Subtype.ext
  exact (torsion_restriction_power p j d left).trans
    ((ambient_difference_annihilated evaluate injective p d bounded (j+d) _ _ equal).trans
      (torsion_restriction_power p j d right).symm)

end SourceGeneratedPrimePowerCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
