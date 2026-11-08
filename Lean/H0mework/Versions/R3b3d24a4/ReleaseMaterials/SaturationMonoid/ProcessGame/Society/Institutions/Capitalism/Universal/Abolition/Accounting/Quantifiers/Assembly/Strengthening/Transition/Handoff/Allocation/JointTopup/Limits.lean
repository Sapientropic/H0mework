import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.JointTopup.Vector
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Diagnostics.Tags

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.JointTopup

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Allocation.Linear
open Diagnostics

variable {Party Good : Type*} [DecidableEq Party] [DecidableEq Good] {n : ℕ}

local notation "Address" => Party × Good

/-- Optional envelopes for promised additions. A shared limit uses one
physical good and is consumed by the sum across all its recipients. -/
structure Limits (Party Good : Type*) where
  atAddress : Party × Good → Option ℚ := fun _ => none
  shared : Good → Option ℚ := fun _ => none

def sameUnit (keys : List Address) (good : Good) : List Address :=
  keys.filter (fun key => decide (key.2 = good))

def unitTotal (keys : List Address) (good : Good) (extra : Address → ℚ) : ℚ :=
  ((sameUnit keys good).map extra).sum

def Limits.Fits (limits : Limits Party Good) (keys : List Address) (extra : Address → ℚ) : Prop :=
  (∀ key ∈ keys, 0 ≤ extra key ∧
    ∀ limit, limits.atAddress key = some limit → extra key ≤ limit) ∧
  (∀ good ∈ keys.map Prod.snd, ∀ limit, limits.shared good = some limit →
    unitTotal keys good extra ≤ limit)

inductive LimitSite (Party Good : Type*) where
  | nonnegative (key : Party × Good)
  | addressCap (key : Party × Good) (limit : ℚ)
  | sharedCap (good : Good) (limit : ℚ)

private def addressTags (limits : Limits Party Good) (keys : List Address) (distinct : keys.Nodup)
    (n : ℕ) (key : Address) : List (Tagged (LimitSite Party Good) (n + keys.length)) :=
  let added := extraForm keys distinct n key
  ⟨.nonnegative key, Affine.le (Affine.literal 0) added⟩ ::
    match limits.atAddress key with
    | none => []
    | some cap => [⟨.addressCap key cap, Affine.le added (Affine.literal cap)⟩]

private def sharedTags (limits : Limits Party Good) (keys : List Address) (distinct : keys.Nodup)
    (n : ℕ) (good : Good) : List (Tagged (LimitSite Party Good) (n + keys.length)) :=
  match limits.shared good with
  | none => []
  | some cap =>
      let used := Affine.sum ((sameUnit keys good).map (extraForm keys distinct n))
      [⟨.sharedCap good cap, Affine.le used (Affine.literal cap)⟩]

def limitTags (limits : Limits Party Good) (keys : List Address) (distinct : keys.Nodup)
    (n : ℕ) : List (Tagged (LimitSite Party Good) (n + keys.length)) :=
  keys.flatMap (addressTags limits keys distinct n) ++
    (keys.map Prod.snd).dedup.flatMap (sharedTags limits keys distinct n)

private theorem addressTags_exact (limits : Limits Party Good) (keys : List Address)
    (distinct : keys.Nodup) (key : Address) (values : Fin (n + keys.length) → ℚ) :
    Feasible (numeric (addressTags limits keys distinct n key)) values ↔
      0 ≤ extraAt keys distinct values key ∧
        ∀ cap, limits.atAddress key = some cap → extraAt keys distinct values key ≤ cap := by
  cases observed : limits.atAddress key with
  | none => simp [addressTags, observed, numeric, feasible_cons]
  | some cap => simp [addressTags, observed, numeric, feasible_cons]

private theorem sharedTags_exact (limits : Limits Party Good) (keys : List Address)
    (distinct : keys.Nodup) (good : Good) (values : Fin (n + keys.length) → ℚ) :
    Feasible (numeric (sharedTags limits keys distinct n good)) values ↔
      ∀ cap, limits.shared good = some cap → unitTotal keys good (extraAt keys distinct values) ≤ cap := by
  cases observed : limits.shared good with
  | none => simp [sharedTags, observed, numeric]
  | some cap => simp [sharedTags, observed, numeric, feasible_cons, unitTotal, Function.comp_def]

theorem limitTags_exact (limits : Limits Party Good) (keys : List Address) (distinct : keys.Nodup)
    (values : Fin (n + keys.length) → ℚ) :
    Feasible (numeric (limitTags limits keys distinct n)) values ↔
      limits.Fits keys (extraAt keys distinct values) := by
  simp only [limitTags, numeric_append, numeric_flatMap, feasible_append, feasible_flatMap,
    addressTags_exact, sharedTags_exact, List.mem_dedup, Limits.Fits]

theorem shared_cap_is_original (limits : Limits Party Good) (keys : List Address)
    (distinct : keys.Nodup) {tag : Tagged (LimitSite Party Good) (n + keys.length)}
    (listed : tag ∈ limitTags limits keys distinct n) {good : Good} {cap : ℚ}
    (named : tag.label = .sharedCap good cap) :
    good ∈ keys.map Prod.snd ∧ limits.shared good = some cap := by
  rcases List.mem_append.mp listed with byAddress | byUnit
  · obtain ⟨key, _, attached⟩ := List.mem_flatMap.mp byAddress
    cases observed : limits.atAddress key with
    | none =>
        simp only [addressTags, observed, List.mem_singleton] at attached
        rw [attached] at named
        cases named
    | some limit =>
        simp only [addressTags, observed, List.mem_cons, List.not_mem_nil, or_false] at attached
        rcases attached with found | found <;> rw [found] at named <;> cases named
  · obtain ⟨unit, source, attached⟩ := List.mem_flatMap.mp byUnit
    cases observed : limits.shared unit with
    | none => simp [sharedTags, observed] at attached
    | some limit =>
        simp only [sharedTags, observed, List.mem_singleton] at attached
        rw [attached] at named
        injection named with sameUnit sameCap
        exact ⟨sameUnit ▸ List.mem_dedup.mp source, sameUnit ▸ sameCap ▸ observed⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.JointTopup
