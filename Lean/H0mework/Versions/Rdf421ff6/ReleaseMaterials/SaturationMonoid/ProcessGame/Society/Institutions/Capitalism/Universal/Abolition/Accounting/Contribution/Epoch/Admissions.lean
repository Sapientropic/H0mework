import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.Epoch.Occurrences

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.EpochHistory

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

def origins (state : (Epoch.Finance.process input depth count).GeneratedState) :=
  state.current.slots.map fun slot => Epoch.Finance.Claim.origin input depth count
    (Epoch.Finance.slotClaim input depth count slot)

def emittedOrigin? (item : Item input depth count) : Option (Epoch.Finance.Origin input depth count) :=
  if ¬ (item.interpreter input depth count).Valid (item.instruction input depth count).before
      (item.instruction input depth count).request then none
  else (Epoch.Finance.readNewClaim input depth count item).map fun claim => .epoch claim.origin

theorem an_emitted_origin_is_its_original_item (item : Item input depth count)
    (origin : Epoch.Finance.Origin input depth count)
    (emitted : emittedOrigin? input depth count item = some origin) : origin = .epoch item := by
  unfold emittedOrigin? at emitted
  split at emitted
  · cases emitted
  · cases returned : Epoch.Finance.readNewClaim input depth count item with
    | none => simp only [returned,Option.map_none] at emitted; cases emitted
    | some claim =>
        simp only [returned,Option.map_some,Option.some.injEq] at emitted
        rw [← emitted,Epoch.Finance.readNewClaim_origin input depth count item claim returned]

theorem emitted_origins_never_duplicate_the_source_items (items : List (Item input depth count))
    (original : items.Nodup) : (items.filterMap (emittedOrigin? input depth count)).Nodup := by
  apply List.Nodup.filterMap _ original
  intro first second origin left right
  have one := an_emitted_origin_is_its_original_item input depth count first origin left
  have two := an_emitted_origin_is_its_original_item input depth count second origin right
  exact Epoch.Finance.Origin.epoch.inj (one.symm.trans two)

theorem each_actual_item_adds_only_its_own_original_origin (item : Item input depth count)
    (before : (Epoch.Finance.process input depth count).GeneratedState) :
    origins input depth count ((Epoch.Finance.consume input depth count item before).next input depth count) =
      origins input depth count before ++ (emittedOrigin? input depth count item).toList := by
  unfold Epoch.Finance.consume emittedOrigin?
  split
  · simp only [Epoch.Finance.InstructionResult.next,Option.toList_none,List.append_nil]
  · split
    · rename_i claim returned
      simp only [returned,Option.map_some,Option.toList_some]
      change (before.current.slots ++ [ObligationSlot.live (Epoch.Finance.admission input depth count (.inr claim)).toObligation]).map _ = _
      rw [List.map_append]
      rfl
    · rename_i absent
      simp only [absent,Option.map_none,Option.toList_none,List.append_nil]
      split
      · rename_i movement found
        have retained := congrArg (List.map (Epoch.Finance.Claim.origin input depth count))
          (Epoch.Finance.allocate input depth count item movement before).original_claims
        simpa only [origins,Epoch.Finance.InstructionResult.next,List.map_map,Function.comp_def] using retained
      · rfl

theorem every_visit_adds_exactly_its_source_emitted_origins (tag : Epoch.Interface.Tag input depth count)
    (visit : Epoch.Interface.Visit input depth count tag)
    (before : (Epoch.Finance.process input depth count).GeneratedState) :
    origins input depth count (Epoch.Finance.consumeVisit input depth count tag visit before) =
      origins input depth count before ++
        (Epoch.Finance.inventory input depth count tag visit).filterMap (emittedOrigin? input depth count) := by
  unfold Epoch.Finance.consumeVisit
  generalize Epoch.Finance.inventory input depth count tag visit = items
  induction items generalizing before with
  | nil => simp only [List.filterMap_nil,List.append_nil]; rfl
  | cons item rest ih =>
      calc
        _ = origins input depth count ((Epoch.Finance.consume input depth count item before).next input depth count) ++
            rest.filterMap (emittedOrigin? input depth count) := ih _
        _ = _ := by
          rw [each_actual_item_adds_only_its_own_original_origin]
          simp only [List.filterMap_cons]
          cases emittedOrigin? input depth count item <;>
            simp only [Option.toList_none,Option.toList_some,List.append_nil,List.append_assoc,
              List.cons_append,List.nil_append]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.EpochHistory
