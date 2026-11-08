import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Root.Settlement
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.PrimitiveInventory
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Scan
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime.Complete

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root

open Capitalism.Universal
open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

abbrev Cut (Party Good Port Technology Instrument : Type)
    [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] :=
  Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)

local notation "C" => Cut Party Good Port Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument
local notation "Script" => Quantities.Execution.primitiveScript
local notation "finish" => Quantities.Execution.endAt

/-- Check the original signed authority at the very intermediate cuts the
native interpreter uses. Its public material projection can erase old gates. -/
def Authorized (source : C) (word : Word) : Prop :=
  ∀ item ∈ (Physical.Public.interpreter source.native.input).rawItems source.raw word,
    source.native.input.law.Valid item.before item.request

/-- All targets and the whole-ledger write are computed by the existing root. -/
structure Paid (source : C) (word : Word) : Prop where
  authorized : Authorized source word
  trace : Runtime.Trace source word (finish source (Script word))
  whole : Quantities.Settled source (Script word)

abbrev terminal (source : C) (word : Word) : C := finish source (Script word)

inductive Failure (source : C) (word : Word)
  | authority (item : ExecutionItem Party Good Port Technology Instrument)
      (original : item ∈ (Physical.Public.interpreter source.native.input).rawItems source.raw word)
      (refused : ¬ source.native.input.law.Valid item.before item.request)
  | body (front : Word) (stopped : C) (request : Request Party Good Port Technology Instrument)
      (remaining : Word) (split : word = front ++ request :: remaining)
      (actual : Runtime.Trace source front stopped) (issue : Runtime.Issue stopped request)
  | accounts (actual : Runtime.Trace source word (terminal source word))
      (recorded : Quantities.Recorded source (Script word))
      (issue : Quantities.Obstruction source (Script word))

inductive Decision (source : C) (word : Word)
  | paid (proof : Paid source word)
  | rejected (failure : Failure source word)

/-- All four checks are local to the submitted word and its generated cuts.
A comparison may inspect several words without merging their writes. -/
def inspect (source : C) (word : Word) : Decision source word :=
  match Abolition.Material.inspectList
      (fun item => source.native.input.law.Valid item.before item.request)
      ((Physical.Public.interpreter source.native.input).rawItems source.raw word) with
  | .failure item original refused => .rejected (.authority item original refused)
  | .clear authorized =>
      match Runtime.run source word with
      | .blocked front stopped request remaining split actual issue =>
          .rejected (.body front stopped request remaining split actual issue)
      | .completed target actual =>
          have trace : Runtime.Trace source word (terminal source word) := by
            rw [show terminal source word = target from Quantities.Execution.original_primitive_trace actual]
            exact actual
          match Quantities.decideAt source (Script word) with
          | .blocked issue => .rejected (.accounts trace (Quantities.record source _) issue)
          | .feasible paid =>
              .paid ⟨fun item original => authorized item original, trace, Quantities.settle source _ paid⟩

theorem Paid.raw_exact {source : C} {word : Word} (paid : Paid source word) :
    (terminal source word).raw =
      ((Physical.Public.interpreter source.native.input).execute source.raw 0 word).final :=
  paid.trace.raw_is_the_complete_original_execution 0

theorem Paid.original_raw_exact {source : C} {word : Word} (paid : Paid source word) :
    (terminal source word).raw = (source.native.input.law.execute source.raw 0 word).final := by
  rw [PublicFunction.execute_physical_of_authorized source.native.input.law source.raw 0 word
    (fun item member => PublicFunction.valid_physical _ _ _ (paid.authorized item member))
    (fun item member => paid.authorized item member)]
  exact paid.raw_exact

def Decision.accepted {source : C} {word : Word} : Decision source word → Bool
  | .paid _ => true
  | .rejected _ => false

private theorem run_selects_trace {source target : C} {word : Word}
    (trace : Runtime.Trace source word target) : Runtime.run source word = .completed target trace := by
  induction trace with
  | nil => rfl
  | cons source request tail target ready review consents valid later chosen =>
      simp only [Runtime.run, dif_pos ready, dif_pos review, dif_pos consents, dif_pos valid, chosen]

theorem inspect_accepts_iff (source : C) (word : Word) :
    (inspect source word).accepted = true ↔ Paid source word := by
  constructor
  · cases inspect source word <;> simp_all [Decision.accepted]
  · intro paid
    unfold inspect
    cases selected : Abolition.Material.inspectList
        (fun item => source.native.input.law.Valid item.before item.request)
        ((Physical.Public.interpreter source.native.input).rawItems source.raw word) with
    | failure item original denied => exact (denied (paid.authorized item original)).elim
    | clear authorized =>
        rw [run_selects_trace paid.trace]
        cases Quantities.decideAt source (Script word) with
        | blocked issue => exact (issue.refutes paid.whole.toFeasible).elim
        | feasible => rfl

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root
