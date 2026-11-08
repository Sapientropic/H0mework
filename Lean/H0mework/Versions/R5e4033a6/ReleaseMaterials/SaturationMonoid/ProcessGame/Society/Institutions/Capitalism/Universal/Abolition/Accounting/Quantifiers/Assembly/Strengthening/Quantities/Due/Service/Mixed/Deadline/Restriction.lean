import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction
open _root_.SaturationMonoid.ProcessGame.Society.UBI.Capacity
open _root_.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {TaskId : Type*} [DecidableEq TaskId]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Task" => PublicTaskSpec Party Good

private theorem original_left_is_full {source : C} {script : Script} {whole : Finset TaskId} {task : TaskId → Task}
    (choice : WholeChoice source script whole task) :
    choice.matching.image Prod.fst = (Clock.Window.Shared.geometry source whole task script).leftCarrier := by
  let geom := Clock.Window.Shared.geometry source whole task script
  apply Finset.eq_of_subset_of_card_le
  · intro slot present
    obtain ⟨edge, matched, rfl⟩ := Finset.mem_image.mp present
    exact ((geom.mem_edgeCarrier_iff edge).mp (geom.matching_subset_edgeCarrier choice.original matched)).1
  · rw [Finset.card_image_of_injOn (geom.matching_laws choice.original).1, choice.full]

/-- Earlier whole services keep exactly their own original matched ordinals. -/
def restrictWhole {source : C} {script : Script} {earlier later : Finset TaskId} {task : TaskId → Task}
    (included : earlier ⊆ later) (choice : WholeChoice source script later task) :
    WholeChoice source script earlier task := by
  let selected := choice.matching.filter fun edge => edge.1.1 ∈ earlier
  let old := Clock.Window.Shared.geometry source later task script
  let new := Clock.Window.Shared.geometry source earlier task script
  have subset : selected ⊆ choice.matching := Finset.filter_subset _ _
  have sourceLaws := old.matching_laws choice.original
  have listed : selected ∈ new.matchings := by
    classical
    unfold CanonicalBipartiteFeasibility.matchings
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr ?_, sourceLaws.1.mono subset, sourceLaws.2.mono subset⟩
    rintro ⟨slot, item⟩ member
    have oldEdge := old.matching_subset_edgeCarrier choice.original (subset member)
    have sameTask := ((Clock.Window.Shared.an_edge_is_an_original_task_and_its_own_timed_service
      source later task script slot item).mp oldEdge).2
    exact (Clock.Window.Shared.an_edge_is_an_original_task_and_its_own_timed_service
      source earlier task script slot item).mpr ⟨(Finset.mem_filter.mp member).2, sameTask⟩
  have exactLeft : selected.image Prod.fst = new.leftCarrier := by
    ext slot
    constructor
    · intro present
      obtain ⟨edge, used, rfl⟩ := Finset.mem_image.mp present
      exact ((new.mem_edgeCarrier_iff edge).mp (new.matching_subset_edgeCarrier listed used)).1
    · intro required
      have oldRequired : slot ∈ old.leftCarrier := by
        have belongs := Finset.mem_sigma.mp required
        exact Finset.mem_sigma.mpr ⟨included belongs.1, belongs.2⟩
      rw [← original_left_is_full choice] at oldRequired
      obtain ⟨edge, present, rfl⟩ := Finset.mem_image.mp oldRequired
      exact Finset.mem_image.mpr ⟨edge, Finset.mem_filter.mpr ⟨present, (Finset.mem_sigma.mp required).1⟩, rfl⟩
  exact ⟨selected, listed, (Finset.card_image_of_injOn (new.matching_laws listed).1).symm.trans
    (congrArg Finset.card exactLeft)⟩

theorem restriction_releases_only_unneeded_whole_reservations
    {source : C} {script : Script} {earlier later : Finset TaskId} {task : TaskId → Task}
    (included : earlier ⊆ later) (choice : WholeChoice source script later task) :
    (restrictWhole included choice).reserved ⊆ choice.reserved := by
  intro ordinal present
  obtain ⟨edge, kept, rfl⟩ := Finset.mem_image.mp present
  exact Finset.mem_image.mpr ⟨edge, (Finset.mem_filter.mp kept).1, rfl⟩

omit [DecidableEq TaskId] in
theorem released_reservations_preserve_original_allocation
    {source : C} {script : Script} {ids : Finset TaskId} {task : TaskId → Task}
    {small large : Finset (Ordinal source script)} (included : small ⊆ large)
    {allocation : Need ids task → Supply source script ids task → ℚ}
    (admitted : (network source script ids task large).Admissible allocation) :
    (network source script ids task small).Admissible allocation := by
  refine ⟨fun line item => ⟨(admitted.1 line item).1, fun absent => ?_⟩, admitted.2.1, fun item => ?_⟩
  · apply (admitted.1 line item).2
    cases found : (network source script ids task large).allows line item
    · rfl
    · have original := (network_allows_iff source script ids task large line item).mp found
      have kept : (network source script ids task small).allows line item = true :=
        (network_allows_iff source script ids task small line item).mpr
          ⟨fun present => original.1 (included present), original.2⟩
      rw [kept] at absent
      cases absent
  · apply (admitted.2.2 item).trans
    let amount := paidAmount source.native.handlerFace.rootRead (Execution.timedAt source script item.1).1 item.2.val
    change (if item.1 ∈ large then 0 else amount) ≤ (if item.1 ∈ small then 0 else amount)
    by_cases old : item.1 ∈ large
    · rw [if_pos old]
      split
      · rfl
      · exact paidAmount_nonnegative _ _ _
    · rw [if_neg old, if_neg (fun belongs => old (included belongs))]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed
