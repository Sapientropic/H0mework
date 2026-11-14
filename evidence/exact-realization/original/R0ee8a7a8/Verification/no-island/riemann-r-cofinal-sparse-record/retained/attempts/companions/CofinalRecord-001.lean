import SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.CofinalInsertion

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedFiniteGram.CofinalRecord

open Finset Projection

variable (source : Nat → Nat → ℂ)
variable (separates : ∀ cutoff : Nat, LinearIndependent ℂ (fun j : Nat => fun t : Nat => source j (cutoff+t)))
variable {n : Nat}

/-- The recorded rows retain the old exact source inverse on their own sample space. -/
abbrev Schedule (count : Nat) :=
  {rows : Fin count → Nat // Function.Injective (synthesis (columns source rows))}

private def nextCutoff (rows : Fin n → Nat) : Nat :=
  Finset.univ.sup rows + 1

/-- The new query is the first nonzero actual residual strictly beyond the previous samples. -/
def pivotTime (rows : Fin n → Nat) : Nat := by
  classical
  let cutoff := nextCutoff rows
  exact cutoff + Nat.find (exists_birth_pivot source rows cutoff (separates cutoff))

theorem pivot_nonzero (rows : Fin n → Nat) :
    birthResidual source rows (pivotTime source separates rows) ≠ 0 := by
  classical
  exact Nat.find_spec (exists_birth_pivot source rows (nextCutoff rows) (separates (nextCutoff rows)))

theorem prior_lt_pivot (rows : Fin n → Nat) (i : Fin n) :
    rows i < pivotTime source separates rows := by
  have below : rows i ≤ Finset.univ.sup rows := Finset.le_sup (f:=rows) (Finset.mem_univ i)
  exact (Nat.lt_succ_of_le below).trans_le (Nat.le_add_right _ _)

private theorem replay_as_synthesis (rows : Fin n → Nat) (a : Values n) :
    synthesis (columns source rows) a = sample rows (replay source a) := by
  ext i
  simp [synthesis, sample, columns, replay, WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul]

private theorem replay_last (a : Values (n+1)) :
    replay source a =
      withBirth source (WithLp.toLp 2 (fun i : Fin n => a i.castSucc)) (a (Fin.last n)) := by
  funext time
  simp only [withBirth, replay, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last, PiLp.toLp_apply]

private theorem append_faithful (prior : Schedule source n) :
    Function.Injective (synthesis (columns source (Fin.snoc prior.val (pivotTime source separates prior.val)))) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro a vanished
  change synthesis (columns source (Fin.snoc prior.val (pivotTime source separates prior.val))) a = 0 at vanished
  let old : Values n := WithLp.toLp 2 (fun i : Fin n => a i.castSucc)
  let born := a (Fin.last n)
  let time := pivotTime source separates prior.val
  rw [replay_as_synthesis, replay_last] at vanished
  change sample (Fin.snoc prior.val time) (withBirth source old born) = 0 at vanished
  have oldZero : sample prior.val (withBirth source old born) = 0 := by
    ext i
    have atRow := congrArg (fun v : Values (n+1) => v i.castSucc) vanished
    simpa only [sample, PiLp.toLp_apply, PiLp.zero_apply, Fin.snoc_castSucc] using atRow
  have latestZero : withBirth source old born time = 0 := by
    have atRow := congrArg (fun v : Values (n+1) => v (Fin.last n)) vanished
    simpa only [sample, PiLp.toLp_apply, PiLp.zero_apply, Fin.snoc_last] using atRow
  have decoded := decode_insert_exact source prior.val prior.property time
    (pivot_nonzero source separates prior.val) old born
  have decodeZero := decode_insert_exact source prior.val prior.property time
    (pivot_nonzero source separates prior.val) (0:Values n) 0
  have zeroField : withBirth source (0:Values n) 0 = 0 := by
    funext t
    simp [withBirth, replay]
  have zeroSamples : sample prior.val (0:Nat → ℂ) = 0 := by rfl
  rw [zeroField, zeroSamples, Pi.zero_apply] at decodeZero
  rw [oldZero, latestZero, decodeZero] at decoded
  have oldEqual : old = 0 := (congrArg Prod.fst decoded).symm
  have bornEqual : born = 0 := (congrArg Prod.snd decoded).symm
  change a = 0
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact bornEqual
  · exact congrArg (fun v : Values n => v j) oldEqual

/-- The prior exact inverse is extended by a single future sample of the new source. -/
def appendSchedule (prior : Schedule source n) : Schedule source (n+1) :=
  ⟨Fin.snoc prior.val (pivotTime source separates prior.val), append_faithful source separates prior⟩

/-- Recursion preserves every already selected time and creates one new observation per birth. -/
def schedule : (count : Nat) → Schedule source count
  | 0 => ⟨Fin.elim0, fun a b _ => by ext i; exact Fin.elim0 i⟩
  | count+1 => appendSchedule source separates (schedule count)

theorem schedule_prior (count : Nat) (i : Fin count) :
    (schedule source separates (count+1)).val i.castSucc = (schedule source separates count).val i :=
  Fin.snoc_castSucc _ _ _

theorem schedule_last (count : Nat) :
    (schedule source separates (count+1)).val (Fin.last count) =
      pivotTime source separates (schedule source separates count).val :=
  Fin.snoc_last _ _

theorem schedule_fresh (count : Nat) (i : Fin count) :
    (schedule source separates count).val i < (schedule source separates (count+1)).val (Fin.last count) := by
  rw [schedule_last]
  exact prior_lt_pivot source separates _ i

theorem schedule_read_insert (a : Values n) (b : ℂ) :
    let prior := (schedule source separates n).val
    let latest := (schedule source separates (n+1)).val (Fin.last n)
    decodeInsert source prior latest (sample prior (withBirth source a b)) (withBirth source a b latest) = (a,b) := by
  dsimp only
  rw [schedule_last]
  exact decode_insert_exact source _ (schedule source separates n).property _
    (pivot_nonzero source separates _) a b

end SourceGeneratedFiniteGram.CofinalRecord
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
