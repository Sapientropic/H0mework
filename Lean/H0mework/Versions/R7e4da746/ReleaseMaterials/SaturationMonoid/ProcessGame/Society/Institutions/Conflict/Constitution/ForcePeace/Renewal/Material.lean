import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Origin
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Run.Disposition

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Renewal

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open PublicFunction.Mandate
open Quantities.Execution

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

local notation "M" => State Party Technology
local notation "C" => Root.Cut Party Good Port M Instrument
local notation "Raw" => RawCurrent Party Good M Instrument
local notation "Item" => ExecutionItem Party Good Port M Instrument
local notation "Word" => RawEvent Party Good Port M Instrument
local notation "Code" => Compile.RawInput Party Good Port M Instrument
local notation "Script" => List (Option Code)

variable (base : RawLaw Party Good Port Technology Instrument)
  (scope : Scope (Party := Party) (Good := Good) (Port := Port))

/-- A restriction of the original material inventory to mandate state.
The before state of every item is its original before state. -/
inductive MaterialTrace : M → List Item → M → Prop
  | nil (current : M) : MaterialTrace current [] current
  | cons {current final : M} {item : Item} {tail : List Item}
      (atCurrent : item.before.technology = current)
      (licensed : (law base scope).Valid item.before item.request)
      (rest : MaterialTrace ((law base scope).step item.before item.request).technology tail final) :
      MaterialTrace current (item :: tail) final

theorem MaterialTrace.append {start middle final : M} {front back : List Item}
    (first : MaterialTrace base scope start front middle) (later : MaterialTrace base scope middle back final) :
    MaterialTrace base scope start (front ++ back) final := by
  induction first with
  | nil => exact later
  | cons before licensed _ ih => exact .cons before licensed (ih later)

theorem MaterialTrace.cut {start final : M} (front back : List Item)
    (trace : MaterialTrace base scope start (front ++ back) final) :
    ∃ middle, MaterialTrace base scope start front middle ∧ MaterialTrace base scope middle back final := by
  induction front generalizing start with
  | nil => exact ⟨start, .nil start, trace⟩
  | cons _ tail prior =>
    cases trace with
    | cons before licensed rest =>
      obtain ⟨middle, kept, later⟩ := prior rest
      exact ⟨middle, .cons before licensed kept, later⟩

theorem MaterialTrace.at_item {start final : M} (front : List Item) (item : Item) (back : List Item)
    (trace : MaterialTrace base scope start (front ++ item :: back) final) :
    MaterialTrace base scope start front item.before.technology ∧ (law base scope).Valid item.before item.request := by
  obtain ⟨middle, first, rest⟩ := MaterialTrace.cut base scope front (item :: back) trace
  cases rest with
  | cons exactCurrent licensed _ => exact ⟨exactCurrent.symm ▸ first, licensed⟩

private theorem word_trace (start : Raw) (index : Nat) (word : Word)
    (authority : ∀ item ∈ ((law base scope).execute start index word).items,
      (law base scope).Valid item.before item.request) :
    MaterialTrace base scope start.technology ((law base scope).execute start index word).items
      ((law base scope).execute start index word).final.technology := by
  induction word generalizing start index with
  | nil => exact .nil _
  | cons req tail later =>
    exact .cons rfl (authority _ List.mem_cons_self)
      (later ((law base scope).step start req) (index + 1)
        (fun item listed => authority item (List.mem_cons_of_mem _ listed)))

private theorem programme_trace
    (input : Capitalism.Universal.Root.ProgrammeSource.Input Party Good Port M Instrument)
    (installed : input.law = law base scope)
    (start : Capitalism.Universal.Abolition.Root.Actual.Current
      (Party := Party) (Good := Good) (Port := Port) (Technology := M) (Instrument := Instrument))
    (code : List Code)
    (authority : ∀ item ∈ Optimality.Programme.items input start code, input.law.Valid item.before item.request) :
    MaterialTrace base scope start.raw.technology (Optimality.Programme.items input start code)
      (Optimality.Programme.run input start code).raw.technology := by
  induction code generalizing start with
  | nil => exact .nil _
  | cons proposal tail later =>
    let result := Physical.Public.compile input start proposal
    have first : ∀ item ∈ result.execution.items, input.law.Valid item.before item.request :=
      fun item listed => authority item (List.mem_append_left _ listed)
    have rest := later result.next (fun item listed => authority item (List.mem_append_right _ listed))
    change MaterialTrace base scope start.raw.technology
      (result.execution.items ++ Optimality.Programme.items input result.next tail)
      (Optimality.Programme.run input result.next tail).raw.technology
    apply MaterialTrace.append base scope _ rest
    cases actual : result with
    | refused => exact .nil _
    | metadata => exact .nil _
    | accepted word selected physical =>
      rw [actual] at first
      have same : (law base scope).execute start.raw 0 word =
          (Physical.Public.interpreter input).execute start.raw 0 word := by
        rw [← installed]
        exact PublicFunction.execute_physical_of_authorized input.law start.raw 0 word physical first
      have trace := word_trace base scope start.raw 0 word (fun item listed => by
        have listedPhysical : item ∈ ((Physical.Public.interpreter input).execute start.raw 0 word).items := by
          rwa [← same]
        have valid := first item listedPhysical
        rwa [installed] at valid)
      have physicalTrace : MaterialTrace base scope start.raw.technology
          ((Physical.Public.interpreter input).execute start.raw 0 word).items
          ((Physical.Public.interpreter input).execute start.raw 0 word).final.technology := same ▸ trace
      cases proposal <;> exact physicalTrace

theorem the_actual_inventory_carries_the_mandate_state (source : C) (history : Script)
    (installed : Emergency.Installed source base scope)
    (authority : Reparation.Actual.SourceAuthority source history) :
    MaterialTrace base scope source.raw.technology (inventory source history) (endAt source history).raw.technology := by
  have literal := physical_is_the_folded_actual_end source history
  have actual := material_is_the_folded_actual_inventory source history
  have traced := programme_trace base scope source.native.input installed
    (Evolving.Epoch.Source.originalState source.native) (programme source history) (by rwa [actual])
  rw [actual, literal] at traced
  exact traced

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Renewal
