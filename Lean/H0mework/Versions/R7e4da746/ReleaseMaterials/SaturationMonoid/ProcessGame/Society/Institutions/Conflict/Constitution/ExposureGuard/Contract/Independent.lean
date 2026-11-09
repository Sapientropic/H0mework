import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Exit.Check
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Contract.Grant

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.MandateExit

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open PublicFunction.Mandate
open Quantities.Execution (endAt inventory)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology]
  [DecidableEq Instrument] [DecidableEq Community]

local notation "M" => State Party Technology
local notation "C" => Root.Cut Party Good Port M Instrument
local notation "Raw" => RawCurrent Party Good M Instrument
local notation "Word" => Reparation.Actual.Script Party Good Port M Instrument
local notation "Item" => ExecutionItem Party Good Port M Instrument

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology]
    [DecidableEq Instrument] [DecidableEq Community] in
def withoutWarTitle (current : Raw) : Raw :=
  { current with technology := { current.technology with holder := none, offered := none } }

variable (base : RawLaw Party Good Port Technology Instrument)
  (scope : Scope (Party := Party) (Good := Good) (Port := Port))

omit [DecidableEq Community] in
/-- Read the very same paid exit item with its war titles cleared. The
original owner keeps the ordinary permissions of the underlying law. -/
def TitleFree (item : Item) : Prop :=
  (law base scope).Valid (withoutWarTitle item.before) item.request ∧
    ¬ Grants item.request

omit [DecidableEq Community] in
instance (item : Item) : Decidable (TitleFree base scope item) := by
  unfold TitleFree
  infer_instance

omit [DecidableEq Instrument] [DecidableEq Community] in
theorem a_title_free_item_cannot_depend_on_the_protected_mandate (item : Item)
    (free : TitleFree base scope item) :
    ¬ Civil.Mandate.NeedsAuthority base scope item.before item.request := by
  intro needs
  have same : Civil.Mandate.NeedsAuthority base scope (withoutWarTitle item.before) item.request := by
    unfold Civil.Mandate.NeedsAuthority at needs ⊢
    exact needs
  exact (Civil.Mandate.a_released_mandate_refuses_every_protected_operation base scope
    (withoutWarTitle item.before) item.request ⟨rfl, rfl⟩ same) free.1

variable (seed : Root.Cut Party Good Port (State Party Technology) Instrument)
  (community : Party → Community)
  (anchor history : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument)
  (control : RawCurrent Party Good (State Party Technology) Instrument → List Party)
  (word : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument)

def Certificate : Prop :=
  Exit.Certificate seed community anchor history control word ∧
    ∀ item ∈ inventory (endAt seed history) word, TitleFree base scope item

def Available : Prop := ∃ exit : Word, Certificate base scope seed community anchor history control exit

inductive Failure
  | material (issue : Exit.Failure seed community anchor history control word)
  | title (item : Item) (original : item ∈ inventory (endAt seed history) word)
      (blocked : ¬ TitleFree base scope item)

def inspect : Failure base scope seed community anchor history control word ⊕
    PLift (Certificate base scope seed community anchor history control word) :=
  match Exit.inspect seed community anchor history control word with
  | .inl failed => .inl (.material failed)
  | .inr checked =>
    match Capitalism.Universal.Abolition.Material.inspectList (TitleFree base scope) (inventory (endAt seed history) word) with
    | .failure item original denied => .inl (.title item original denied)
    | .clear whole => .inr ⟨⟨checked.down, whole⟩⟩

theorem Failure.refutes (issue : Failure base scope seed community anchor history control word) :
    ¬ Certificate base scope seed community anchor history control word := by
  intro claimed
  cases issue with
  | material failure => exact failure.refutes _ _ _ _ _ _ claimed.1
  | title item original blocked => exact blocked (claimed.2 item original)

theorem no_independent_exit_iff_every_original_candidate_returns_its_exact_issue :
    ¬ Available base scope seed community anchor history control ↔
      ∀ proposal : Word, Nonempty (Failure base scope seed community anchor history control proposal) := by
  constructor
  · intro denied proposal
    cases inspect base scope seed community anchor history control proposal with
    | inl failure => exact ⟨failure⟩
    | inr paid => exact (denied ⟨proposal, paid.down⟩).elim
  · rintro fails ⟨proposal, paid⟩
    obtain ⟨issue⟩ := fails proposal
    exact issue.refutes _ _ _ _ _ _ _ _ paid

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.MandateExit
