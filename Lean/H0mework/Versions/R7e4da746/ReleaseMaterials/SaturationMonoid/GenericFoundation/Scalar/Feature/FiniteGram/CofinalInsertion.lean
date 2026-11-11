import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.Projection

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedFiniteGram.CofinalRecord
open Finset Projection

variable (source : Nat → Nat → ℂ)
variable {n : Nat}

abbrev Values (n : Nat) := Coordinates (Fin n)

def sample (rows : Fin n → Nat) (field : Nat → ℂ) : Values n :=
  WithLp.toLp 2 (fun i => field (rows i))

def columns (rows : Fin n → Nat) (j : Fin n) : Values n :=
  sample rows (source j.val)

def replay (a : Values n) (time : Nat) : ℂ :=
  ∑ i : Fin n, a i * source i.val time

def withBirth (a : Values n) (b : ℂ) (time : Nat) : ℂ :=
  replay source a time + b * source n time

def priorFit (rows : Fin n → Nat) : Values n :=
  Projection.coefficients (columns source rows) (sample rows (source n))

def birthResidual (rows : Fin n → Nat) (time : Nat) : ℂ :=
  source n time - replay source (priorFit source rows) time

/-- No already recorded prefix can account for a new column over the entire remaining source tail. -/
theorem exists_birth_pivot (rows : Fin n → Nat) (cutoff : Nat)
    (separates : LinearIndependent ℂ (fun j : Nat => fun t : Nat => source j (cutoff+t))) :
    ∃ k : Nat, birthResidual source rows (cutoff+k) ≠ 0 := by
  classical
  by_contra! silent
  let fit := priorFit source rows
  let test : Fin (n+1) → ℂ := Fin.snoc (fun i => -fit i) 1
  have independent := separates.comp (Fin.val : Fin (n+1) → Nat) Fin.val_injective
  have erased : ∑ i : Fin (n+1), test i • (fun t : Nat => source i.val (cutoff+t)) = 0 := by
    funext t
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
    rw [Fin.sum_univ_castSucc]
    simp only [test, Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last,
      neg_mul, Finset.sum_neg_distrib, one_mul]
    change -replay source fit (cutoff+t) + source n (cutoff+t) = 0
    have equality := silent t
    change source n (cutoff+t) - replay source fit (cutoff+t) = 0 at equality
    linear_combination equality
  have gone := (Fintype.linearIndependent_iff.mp independent) test erased (Fin.last n)
  simp [test] at gone

/-- Subtract the continuation of the old fit at the selected source row before reading the birth. -/
def decodeInsert (rows : Fin n → Nat) (time : Nat) (previous : Values n) (current : ℂ) : Values n × ℂ :=
  let old := Projection.coefficients (columns source rows) previous
  let fresh := (current - replay source old time) / birthResidual source rows time
  (old - fresh • priorFit source rows, fresh)

private theorem sampled_birth (rows : Fin n → Nat) (a : Values n) (b : ℂ) :
    sample rows (withBirth source a b) =
      synthesis (columns source rows) a + b • sample rows (source n) := by
  ext i
  simp [sample, withBirth, replay, columns, synthesis, WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul]

private theorem old_solver_synthesis (rows : Fin n → Nat)
    (faithful : Function.Injective (synthesis (columns source rows))) (a : Values n) :
    Projection.coefficients (columns source rows) (synthesis (columns source rows) a) = a := by
  apply faithful
  have equation := predictable_readback (columns source rows) (synthesis (columns source rows) a)
  rw [predictable_source, Submodule.starProjection_eq_self_iff.mpr
    (show synthesis (columns source rows) a ∈ sourceSpan (columns source rows) from ⟨a,rfl⟩)] at equation
  exact equation

private theorem old_solver_linear (rows : Fin n → Nat)
    (faithful : Function.Injective (synthesis (columns source rows))) (u v : Values n) (b : ℂ) :
    Projection.coefficients (columns source rows) (u+b • v) =
      Projection.coefficients (columns source rows) u + b • Projection.coefficients (columns source rows) v := by
  apply faithful
  simp only [map_add, map_smul, ← predictable_source]
  let operator := predictableCLM (columns source rows)
  change operator (u+b • v) = operator u+b • operator v
  rw [map_add, map_smul]

private theorem replay_linear (a u : Values n) (b : ℂ) (time : Nat) :
    replay source (a+b • u) time = replay source a time+b * replay source u time := by
  simp only [replay, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]

/-- One actual source row extends the old exact decoder, using only its already chosen samples. -/
theorem decode_insert_exact (rows : Fin n → Nat)
    (faithful : Function.Injective (synthesis (columns source rows)))
    (time : Nat) (pivot : birthResidual source rows time ≠ 0) (a : Values n) (b : ℂ) :
    decodeInsert source rows time (sample rows (withBirth source a b)) (withBirth source a b time) = (a,b) := by
  have fit : Projection.coefficients (columns source rows) (sample rows (withBirth source a b)) =
      a+b • priorFit source rows := by
    rw [sampled_birth, old_solver_linear source rows faithful, old_solver_synthesis source rows faithful]
    rfl
  have difference : (replay source a time+b * source n time) -
      (replay source a time+b * replay source (priorFit source rows) time) =
        b * birthResidual source rows time := by
    unfold birthResidual
    ring
  unfold decodeInsert
  dsimp only
  rw [fit, replay_linear, withBirth, difference, mul_div_cancel_right₀ _ pivot, add_sub_cancel_right]

end SourceGeneratedFiniteGram.CofinalRecord
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
