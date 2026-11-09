import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Choice.Frontier
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Choice.Policy

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Choice

variable {World Observation Action : Type*} (observe : World → Observation)
  (executable : World → Action → Prop) (score : World → Action → ℝ)

def fiberFloors (seen : Set.range observe) : Set ℝ :=
  { floor | ∃ action, ∀ world, observe world = seen.1 → executable world action ∧ floor ≤ score world action }

def policyFloors : Set ℝ :=
  { floor | ∃ policy, Satisfies observe (fun world action =>
      executable world action ∧ floor ≤ score world action) policy }

/-- A candidate in this menu supplies both a prior policy and a guarantee it actually meets. -/
def policyMenu : Menu (Policy observe Action × ℝ) where
  executable := { trial | Satisfies observe (fun world action =>
    executable world action ∧ trial.2 ≤ score world action) trial.1 }
  score := Prod.snd

@[simp]
theorem policyMenu_values :
    (policyMenu observe executable score).values = policyFloors observe executable score := by
  ext floor
  constructor
  · rintro ⟨⟨policy, _⟩, works, rfl⟩
    exact ⟨policy, works⟩
  · rintro ⟨policy, works⟩
    exact ⟨⟨policy, floor⟩, works, rfl⟩

theorem policy_floor_iff (floor : ℝ) :
    floor ∈ policyFloors observe executable score ↔
      ∀ seen, floor ∈ fiberFloors observe executable score seen :=
  policy_exists_iff_fiberwise observe _

theorem fiber_floors_downward {seen : Set.range observe} {floor lower : ℝ}
    (supported : floor ∈ fiberFloors observe executable score seen) (below : lower ≤ floor) :
    lower ∈ fiberFloors observe executable score seen := by
  obtain ⟨action, works⟩ := supported
  exact ⟨action, fun world same =>
    let ⟨actual, atLeast⟩ := works world same
    ⟨actual, below.trans atLeast⟩⟩

theorem policy_frontier_le_fiber_frontier
    (actual : (policyFloors observe executable score).Nonempty)
    (seen : Set.range observe) (bounded : BddAbove (fiberFloors observe executable score seen)) :
    sSup (policyFloors observe executable score) ≤ sSup (fiberFloors observe executable score seen) :=
  csSup_le_csSup bounded actual fun floor inPolicy =>
    (policy_floor_iff observe executable score floor).mp inPolicy seen

/-- The best uniform guarantee from a single prior policy is the infimum of the local
guarantees. Each local guarantee already uses one action for its whole observation fiber. -/
theorem robust_frontier_eq_worst_observation [Nonempty World]
    (actual : (policyFloors observe executable score).Nonempty)
    (bounded : ∀ seen, BddAbove (fiberFloors observe executable score seen)) :
    sSup (policyFloors observe executable score) =
      sInf (Set.range fun seen => sSup (fiberFloors observe executable score seen)) := by
  let values := policyFloors observe executable score
  let localValues := fiberFloors observe executable score
  have included (seen : Set.range observe) : values ⊆ localValues seen :=
    fun floor inPolicy => (policy_floor_iff observe executable score floor).mp inPolicy seen
  have localBound (seen : Set.range observe) : sSup values ≤ sSup (localValues seen) :=
    policy_frontier_le_fiber_frontier observe executable score actual seen (bounded seen)
  have rangeBound : BddBelow (Set.range fun seen => sSup (localValues seen)) :=
    ⟨sSup values, fun _ ⟨seen, exactValue⟩ => exactValue ▸ localBound seen⟩
  obtain ⟨world⟩ := ‹Nonempty World›
  let observed := Set.rangeFactorization observe world
  apply le_antisymm
  · apply le_csInf ⟨_, Set.mem_range_self observed⟩
    rintro _ ⟨seen, rfl⟩
    exact localBound seen
  · apply le_of_not_gt
    intro bigger
    obtain ⟨floor, above, below⟩ := exists_between bigger
    have reachable : floor ∈ values := (policy_floor_iff observe executable score floor).mpr fun seen => by
      have localBelow : floor < sSup (localValues seen) :=
        below.trans_le (csInf_le rangeBound (Set.mem_range_self seen))
      obtain ⟨supported, supportedMem, strict⟩ :=
        exists_lt_of_lt_csSup (actual.mono (included seen)) localBelow
      exact fiber_floors_downward observe executable score supportedMem strict.le
    exact (not_lt_of_ge (le_csSup ((bounded observed).mono (included observed)) reachable)) above

/-- Only a fiber whose supremum binds the global guarantee can prevent attainment. -/
theorem robust_frontier_attained_iff_binding_fibers_attain
    (actual : (policyFloors observe executable score).Nonempty)
    (bounded : ∀ seen, BddAbove (fiberFloors observe executable score seen)) :
    let best := sSup (policyFloors observe executable score)
    best ∈ policyFloors observe executable score ↔
      ∀ seen, sSup (fiberFloors observe executable score seen) = best →
        best ∈ fiberFloors observe executable score seen := by
  intro best
  rw [policy_floor_iff]
  constructor
  · exact fun all seen _ => all seen
  · intro binding seen
    have below := policy_frontier_le_fiber_frontier observe executable score actual seen (bounded seen)
    rcases lt_or_eq_of_le below with strict | equality
    · have localActual : (fiberFloors observe executable score seen).Nonempty :=
        actual.mono fun floor available =>
          (policy_floor_iff observe executable score floor).mp available seen
      obtain ⟨supported, supportedMem, above⟩ := exists_lt_of_lt_csSup localActual strict
      exact fiber_floors_downward observe executable score supportedMem above.le
    · exact binding seen equality.symm

theorem a_uniform_positive_policy_iff_positive_frontier
    (actual : (policyFloors observe executable score).Nonempty)
    (bounded : BddAbove (policyFloors observe executable score)) :
    (∃ floor > 0, ∃ policy, Satisfies observe (fun world action =>
        executable world action ∧ floor ≤ score world action) policy) ↔
      0 < sSup (policyFloors observe executable score) := by
  change (∃ floor > 0, floor ∈ policyFloors observe executable score) ↔
    0 < sSup (policyFloors observe executable score)
  rw [lt_csSup_iff bounded actual]
  exact ⟨fun ⟨floor, positive, supported⟩ => ⟨floor, supported, positive⟩,
    fun ⟨floor, supported, positive⟩ => ⟨floor, positive, supported⟩⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Choice
