import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Supply.Effect
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Public.Result

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Supply

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Capitalism.Universal.Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

private theorem authorized_inventory_is_the_physical_inventory
    (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) (index : Nat)
    (authorized : ∀ item ∈ (input.law.execute current index word).items,
      input.law.Valid item.before item.request) :
    (Physical.Public.interpreter input).execute current index word = input.law.execute current index word := by
  induction word generalizing current index with
  | nil => rfl
  | cons request tail earlier =>
    have legal : input.law.Valid current request := authorized ⟨index, current, request⟩ List.mem_cons_self
    have physicalLegal : (Physical.Public.interpreter input).Valid current request :=
      PublicFunction.valid_physical _ _ _ legal
    have actual : (Physical.Public.interpreter input).step current request = input.law.step current request := by
      simp only [RawLaw.step, if_pos physicalLegal, if_pos legal]
      rfl
    rw [RawLaw.execute, RawLaw.execute, actual, earlier]
    intro item listed
    exact authorized item (List.mem_cons_of_mem _ listed)

variable {input} {origin : RawCurrent Party Good Technology Instrument}
  {roster : List Party} {word : RawEvent Party Good Port Technology Instrument}
  (before : Capitalism.Universal.Abolition.Root.Actual.Current (Party := Party) (Good := Good)
    (Port := Port) (Technology := Technology) (Instrument := Instrument))

private theorem Period.resigns_to_the_literal_word (paid : Period input origin before.raw roster word) :
    (word.map fun request => request.resign request.signer) = word := by
  conv => rhs; rw [← List.map_id word]
  apply List.map_congr_left
  intro request listed
  have original : request ∈ (input.law.rawItems before.raw word).map ExecutionItem.request := by
    rwa [RawLaw.rawItems, RawLaw.inventory_requests_exact]
  obtain ⟨item, source, exactRequest⟩ := List.mem_map.mp original
  exact Request.resign_self _ (exactRequest ▸ (paid.own item source).noConsent)

/-- The public physical dispatcher consumes the actual checked programme.
Its inventory includes the same before-state at every original ordinal. -/
theorem Period.native_write (paid : Period input origin before.raw roster word) :
    let written := Physical.Public.compile input before (.execute word)
    written.isAccepted = true ∧ written.execution = input.law.execute before.raw 0 word ∧
      written.next = { before with raw := input.law.next before.raw word } := by
  have selected : Physical.Public.wordAt before (.execute word) = some word :=
    congrArg some (paid.resigns_to_the_literal_word before)
  have written := authorized_inventory_is_the_physical_inventory input before.raw word 0
    (fun item listed => (paid.own item listed).valid)
  dsimp only
  cases Physical.Public.compile input before (.execute word) with
  | accepted actual original _ =>
    rw [selected] at original
    cases Option.some.inj original
    refine ⟨rfl, written, ?_⟩
    change { before with raw := (Physical.Public.interpreter input).next before.raw word } = _
    unfold RawLaw.next
    rw [written]
    rfl
  | refused actual original item listed failed =>
    rw [selected] at original
    cases Option.some.inj original
    change item ∈ ((Physical.Public.interpreter input).execute before.raw 0 word).items at listed
    rw [written] at listed
    exact (failed (PublicFunction.valid_physical _ _ _ (paid.own item listed).valid)).elim
  | metadata empty =>
    rw [selected] at empty
    cases empty

theorem Period.each_native_item_has_exact_original_ownership (paid : Period input origin before.raw roster word) :
    ∀ item ∈ (Physical.Public.compile input before (.execute word)).execution.items,
      OwnItem input.law roster item := by
  rw [(paid.native_write before).2.1]
  exact paid.own

theorem Period.each_physical_item_is_own (paid : Period input origin before.raw roster word) :
    ∀ item ∈ (Physical.Public.compile input before (.execute word)).execution.items,
      OwnItem (Physical.Public.interpreter input) roster item := by
  intro item listed
  have original := paid.each_native_item_has_exact_original_ownership before item listed
  exact ⟨original.operation, original.member, original.noConsent,
    PublicFunction.valid_physical _ _ _ original.valid⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Supply
