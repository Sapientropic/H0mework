import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Material.Period
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Dispatch

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Material

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime (Ready ReviewAvailable)
open Conflict.Consumers.Evolving (C compact life)
open Quantities.Execution
open Reparation.Actual
open private keysAt original_key from
  H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary.Actual.Incidence

noncomputable section

abbrev livingInput : Input Bool Bool Bool Unit Unit := some (.execute livingWord)

section

variable (cut : C) (same : cut.native.input = compact) (raw : cut.raw = Original.snapshot 111 113)
  (ready : Ready cut) (review : ReviewAvailable cut)

include same raw ready review

theorem the_living_periods_original_inventory_at :
    Boundary.Actual.items cut livingInput =
      (Physical.Public.interpreter compact).rawItems (Original.snapshot 111 113) livingWord := by
  change inventory cut [livingInput] = _
  rw [a_checked_period_has_the_original_paid_inventory cut livingWord ready review
    (the_living_period_passes_the_original_guards_at cut same raw), same, raw]
  rfl

theorem the_living_period_has_original_authority_at :
    SourceAuthority cut [livingInput] := by
  intro item inside
  change item ∈ Boundary.Actual.items cut livingInput at inside
  rw [the_living_periods_original_inventory_at cut same raw ready review] at inside
  rw [same]
  exact (by decide +kernel : ∀ request ∈ (Physical.Public.interpreter compact).rawItems
    (Original.snapshot 111 113) livingWord, compact.law.Valid request.before request.request) item inside

theorem the_living_periods_material_body_is_damage_free_at :
    Boundary.Actual.damages cut livingInput Original.community = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro damage _
  have literal := damage.source_item
  rw [the_living_periods_original_inventory_at cut same raw ready review] at literal
  have keys := original_key damage
  unfold keysAt at keys
  obtain ⟨entry, entryIn, address⟩ := List.mem_map.mp keys
  change entry ∈ (Physical.Public.interpreter cut.native.input).actualDebit
    damage.item.before damage.item.request at entryIn
  rw [same] at entryIn
  have own := (by decide +kernel : ∀ item ∈ (Physical.Public.interpreter compact).rawItems
    (Original.snapshot 111 113) livingWord, ∀ part ∈
      (Physical.Public.interpreter compact).actualDebit item.before item.request,
      part.1.1 = item.request.signer) damage.item literal entry entryIn
  have notForeign := congrArg Original.community own
  have foreign := damage.actual_foreign_debit.1.1
  rw [← address] at foreign
  exact foreign notForeign

end

theorem the_living_period_has_original_authority :
    SourceAuthority Original.cut [livingInput] :=
  the_living_period_has_original_authority_at Original.cut Original.same_source Original.cut_raw Original.ready Original.review

theorem the_living_periods_material_body_is_damage_free :
    Boundary.Actual.damages Original.cut livingInput Original.community = [] :=
  the_living_periods_material_body_is_damage_free_at Original.cut Original.same_source Original.cut_raw
    Original.ready Original.review

theorem the_living_period_is_admitted_on_the_original_personal_lanes
    (answers : ExposureGuard.OwnerAnswers Original.seed)
    (affirmed : ∀ position bearer, answers Original.history livingInput position bearer = true) :
    ExposureGuard.Admitted [false, true] answers Original.history livingInput :=
  ⟨the_living_period_has_original_authority, fun position question _ _ => affirmed position question.1⟩

private theorem an_empty_inventory_has_no_damage_at_any_of_its_ticks
    (cut : C) (front later : Original.Word) (input : Input Bool Bool Bool Unit Unit)
    (empty : inventory cut (front ++ input :: later) = []) :
    Boundary.Actual.damages (endAt cut front) input Original.community = [] := by
  rw [inventory_append] at empty
  have atCut := (List.append_eq_nil_iff.mp empty).2
  simp only [inventory] at atCut
  apply Boundary.Actual.no_material_write_has_no_damage
  change Optimality.Programme.Epoch.materialItems (query (endAt cut front) input) ++ [] = []
  rw [(List.append_eq_nil_iff.mp atCut).1, List.nil_append]

private theorem a_safe_body_and_empty_drain_are_safe_at_each_tick
    (cut : C) (body : Input Bool Bool Bool Unit Unit) (tail : Original.Word)
    (safe : Boundary.Actual.damages cut body Original.community = [])
    (empty : inventory (next cut body) tail = [])
    (front later : Original.Word) (input : Input Bool Bool Bool Unit Unit)
    (listed : body :: tail = front ++ input :: later) :
    Boundary.Actual.damages (endAt cut front) input Original.community = [] := by
  cases front with
  | nil =>
    have same := (List.cons.inj listed).1
    change Boundary.Actual.damages cut input Original.community = []
    rwa [← same]
  | cons first front =>
    obtain ⟨same, continuation⟩ := List.cons.inj listed
    change Boundary.Actual.damages (endAt (next cut first) front) input Original.community = []
    rw [← same]
    exact an_empty_inventory_has_no_damage_at_any_of_its_ticks _ _ _ _ (continuation ▸ empty)

/-- The paid period's actual material input and every generated native
accounting input preserve the original loss inventory. -/
theorem each_input_of_the_paid_living_period_is_damage_free
    (front later : Original.Word) (input : Input Bool Bool Bool Unit Unit)
    (listed : livingPeriod = front ++ input :: later) :
    Boundary.Actual.damages (endAt Original.cut front) input Original.community = [] :=
  a_safe_body_and_empty_drain_are_safe_at_each_tick Original.cut livingInput _
    the_living_periods_material_body_is_damage_free
    (the_first_exhausted_native_cut_is_the_original_paid_drain (next Original.cut livingInput)).2.2.1
    front later input listed

#print axioms each_input_of_the_paid_living_period_is_damage_free

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Material
