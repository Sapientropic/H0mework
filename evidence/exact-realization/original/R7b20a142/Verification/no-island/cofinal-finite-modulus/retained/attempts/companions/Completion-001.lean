import SaturationMonoid.GenericFoundation.Cofinal.Topology.FiniteModulus

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CofinalAllPrimeTopology

open CategoryTheory CategoryTheory.Limits SourceGeneratedPrimePowerCompletion
open scoped Pointwise

variable {L M : Type u} [AddCommGroup L] [AddCommGroup M]
variable (primes : Finset Nat.Primes) (depth : primes → Nat)

/-- The specified finite restriction of the original coherent all-prime family. -/
def finitePrimeRestriction (value : AllPrimeCompletion L) (p : primes) : StageResidual (L := L) p.val (depth p) :=
  (restriction (L := L) p.val (depth p)).hom (value p.val)

/-- One integral source representative realizes the complete finite restriction. -/
def finitePrimeLift (value : AllPrimeCompletion L) : L :=
  Classical.choose (finite_prime_projection_surjective primes depth (finitePrimeRestriction primes depth value))

theorem finite_prime_lift_projection (value : AllPrimeCompletion L) :
    finitePrimeProjection primes depth (finitePrimeLift primes depth value) = finitePrimeRestriction primes depth value :=
  Classical.choose_spec (finite_prime_projection_surjective primes depth (finitePrimeRestriction primes depth value))

/-- The canonical residue is independent of the representative used to realize it. -/
theorem finite_prime_lift_residue (value : AllPrimeCompletion L) (source : L) :
    (Submodule.Quotient.mk source : L ⧸ Ideal.span {compositeModulus primes depth} • (⊤ : Submodule ℤ L)) =
      (finitePrimeEquiv primes depth).symm (finitePrimeRestriction primes depth value) ↔
    finitePrimeProjection primes depth source = finitePrimeRestriction primes depth value := by
  let coordinates := finitePrimeEquiv (L := L) primes depth
  let observed := finitePrimeRestriction primes depth value
  constructor
  · intro residue
    exact (finite_prime_equiv_projection primes depth source).symm.trans
      ((congrArg coordinates residue).trans (coordinates.apply_symm_apply observed))
  · intro read
    apply coordinates.injective
    exact (finite_prime_equiv_projection primes depth source).trans
      (read.trans (coordinates.apply_symm_apply observed).symm)

/-- Every lower coordinate is read by its actual tower restriction. -/
theorem finite_prime_lift_lower (value : AllPrimeCompletion L) (p : primes) (j : Nat) (within : j ≤ depth p) :
    stageProjection p.val j (finitePrimeLift primes depth value) = (restriction p.val j).hom (value p.val) := by
  let source := finitePrimeLift primes depth value
  let edge := (homOfLE within).op
  let restrict := (tower (L := L) p.val).map edge
  have diagonal := (sourceState (L := L) p.val).naturality edge
  rw [Functor.const_obj_map, Category.id_comp] at diagonal
  have written : stageProjection p.val j source = restrict.hom (stageProjection p.val (depth p) source) :=
    ConcreteCategory.congr_hom diagonal source
  have matches : stageProjection p.val (depth p) source = (restriction p.val (depth p)).hom (value p.val) :=
    congrFun (finite_prime_lift_projection primes depth value) p
  have coherence := ConcreteCategory.congr_hom (limit.w (tower (L := L) p.val) edge) (value p.val)
  exact written.trans ((congrArg restrict.hom matches).trans coherence)

/-- The actual source action transports every representative of the computed residue. -/
theorem finite_prime_successor (action : L →ₗ[ℤ] M) (value : AllPrimeCompletion L) (source : L)
    (read : finitePrimeProjection primes depth source = finitePrimeRestriction primes depth value) :
    finitePrimeProjection primes depth (action source) =
      finitePrimeRestriction primes depth (allPrimeSuccessor action value) := by
  funext p
  let move := stageMap p.val (depth p) action
  have written := LinearMap.congr_fun (stageMap_projection p.val (depth p) action) source
  have prior : stageProjection p.val (depth p) source = (restriction p.val (depth p)).hom (value p.val) :=
    congrFun read p
  exact written.symm.trans ((congrArg move prior).trans
    (allPrime_successor_restriction action p.val (depth p) value).symm)

/-- A paid integral coordinate makes the finite representative unique in the standard remainder interval. -/
def finitePrimeIntegralLift (coordinate : L ≃ₗ[ℤ] ℤ) (value : AllPrimeCompletion L) : L :=
  coordinate.symm (coordinate (finitePrimeLift primes depth value) % compositeModulus primes depth)

theorem finite_prime_integral_lift (coordinate : L ≃ₗ[ℤ] ℤ) (value : AllPrimeCompletion L) :
    let source := finitePrimeIntegralLift primes depth coordinate value
    finitePrimeProjection primes depth source = finitePrimeRestriction primes depth value ∧
      0 ≤ coordinate source ∧ coordinate source < compositeModulus primes depth := by
  let source := finitePrimeIntegralLift primes depth coordinate value
  let representative := finitePrimeLift primes depth value
  let period := compositeModulus primes depth
  let integer := coordinate representative
  have coefficient : coordinate source = integer % period := coordinate.apply_symm_apply _
  have normal : finitePrimeProjection primes depth source = finitePrimeProjection primes depth representative := by
    apply (finite_prime_fibre primes depth source representative).2
    refine ⟨coordinate.symm (-(integer / period)), coordinate.injective ?_⟩
    rw [map_smul, map_sub, coefficient, coordinate.apply_symm_apply]
    change period * -(integer / period) = integer % period - integer
    have division := Int.emod_add_ediv_mul integer period
    rw [mul_comm (integer / period) period] at division
    rw [mul_neg]
    omega
  have positive : 0 < period := composite_modulus_pos primes depth
  exact ⟨normal.trans (finite_prime_lift_projection primes depth value),
    coefficient.symm ▸ Int.emod_nonneg _ (ne_of_gt positive),
    coefficient.symm ▸ Int.emod_lt_of_pos _ positive⟩

theorem finite_prime_integral_unique (coordinate : L ≃ₗ[ℤ] ℤ) {left right : L}
    (leftBounds : 0 ≤ coordinate left ∧ coordinate left < compositeModulus primes depth)
    (rightBounds : 0 ≤ coordinate right ∧ coordinate right < compositeModulus primes depth)
    (same : finitePrimeProjection primes depth left = finitePrimeProjection primes depth right) : left = right := by
  obtain ⟨difference, difference_eq⟩ := (finite_prime_fibre primes depth left right).1 same
  let period := compositeModulus primes depth
  have written := congrArg coordinate difference_eq
  rw [map_smul, map_sub] at written
  change period * coordinate difference = coordinate left - coordinate right at written
  have translated : coordinate left = coordinate right + period * coordinate difference := by omega
  apply coordinate.injective
  calc
    _ = coordinate left % period := (Int.emod_eq_of_lt leftBounds.1 leftBounds.2).symm
    _ = coordinate right % period := (congrArg (fun value : ℤ => value % period) translated).trans
      (Int.add_mul_emod_self_left (coordinate right) period (coordinate difference))
    _ = _ := Int.emod_eq_of_lt rightBounds.1 rightBounds.2

end CofinalAllPrimeTopology
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
