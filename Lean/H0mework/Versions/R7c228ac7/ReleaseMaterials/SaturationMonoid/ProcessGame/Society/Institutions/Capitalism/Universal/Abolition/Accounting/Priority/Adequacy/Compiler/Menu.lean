import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Capacity.Guarantee
import Mathlib.Algebra.Order.Floor.Ring

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Compiler

open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  [DecidableEq Technology] [DecidableEq Port]
  {source : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : source.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (claim : Responsibility.Family.Claim source past nature response)
  (state : Responsibility.Family.State claim) (law : RawLaw Party Good Port Technology Instrument)
  (members : List Party)

/-- The command port is the original source programme's port. These requests
ask for no controller consent and never issue a financial claim. -/
def command (actor : Party) (operation : Operation Party Good Technology Instrument) : Request Party Good Port Technology Instrument :=
  ⟨actor,[],source.investmentPort,[],operation⟩

def technologies : List Technology :=
  (state.raw.technology :: (Control.responseExecution source past nature response).items.filterMap
    (fun item => match item.request.operation with | .revise _ technology => some technology | _ => none)).dedup

def needsWord : RawEvent Party Good Port Technology Instrument := members.dedup.flatMap fun actor =>
  (if law.necessities state.raw actor = [] then [] else [command (source := source) actor (.use actor (law.necessities state.raw actor) .necessity)]) ++
  (if law.mandatoryMaintenance state.raw actor = [] then [] else [command (source := source) actor (.use actor (law.mandatoryMaintenance state.raw actor) .maintenance)])

def required (good : Good) : ℚ :=
  ((Responsibility.Family.positiveScope source past nature response).map fun key =>
    if key.2 = good then state.remaining key else 0).sum +
  (members.dedup.map fun actor => amount Good (law.necessities state.raw actor) good +
    amount Good (law.mandatoryMaintenance state.raw actor) good).sum

def recipeNet (operator : Party) (technology : Technology) (good : Good) : ℚ :=
  amount Good (law.technique technology operator).outputs good -
    amount Good ((law.technique technology operator).inputs ++ (law.technique technology operator).maintenance) good

def relevantGoods (operator : Party) (technology : Technology) : List Good :=
  ((Responsibility.Family.positiveScope source past nature response).map Prod.snd ++
    members.flatMap (fun actor => (law.necessities state.raw actor ++ law.mandatoryMaintenance state.raw actor).map Prod.fst) ++
    (law.revisionCost state.raw.technology technology).map Prod.fst ++
    ((law.technique technology operator).inputs ++ (law.technique technology operator).maintenance ++
      (law.technique technology operator).outputs).map Prod.fst).dedup

/-- Doses are computed from source debts, maintenance bills, revision costs and
positive primitive recipe yields. No caller search cap or successful future is used. -/
def dose (operator : Party) (technology : Technology) : Nat :=
  max 1 (((relevantGoods claim state law members operator technology).map fun good =>
    if 0 < recipeNet law operator technology good then
      ⌈(required claim state law members good +
        amount Good (law.revisionCost state.raw.technology technology) good) / recipeNet law operator technology good⌉₊
    else 0).foldl max 0)

/-- Remove only requests for which this old repair row has no current authority.
In particular extra production cannot redeem an already paid row. -/
def normalizeFrom : RawEvent Party Good Port Technology Instrument →
    RawEvent Party Good Port Technology Instrument → RawEvent Party Good Port Technology Instrument
  | front, [] => front
  | front, request :: rest =>
      normalizeFrom (if Capacity.RawAmount claim state law members front request then front ++ [request] else front) rest

def payFrom (operator : Party) : RawEvent Party Good Port Technology Instrument → List (Party × Good) →
    RawEvent Party Good Port Technology Instrument
  | front, [] => front
  | front, key :: rest =>
      let due := Capacity.residual claim state law front key
      let next := if 0 < due ∧ operator ≠ key.1 then
        front ++ [command (source := source) operator (.transfer operator key.1 [(key.2,due)])] else front
      payFrom operator next rest

def plantPlan (operator : Party) (technology : Technology) : RawEvent Party Good Port Technology Instrument :=
  let revision := if technology = state.raw.technology then [] else [command (source := source) operator (.revise operator technology)]
  let produced := normalizeFrom claim state law members []
    (revision ++ needsWord claim state law members ++ List.replicate (dose claim state law members operator technology)
      (command (source := source) operator (.produce operator)))
  payFrom claim state law operator produced (Responsibility.Family.positiveScope source past nature response)

/-- Each current plant and each revision parameter from the original actual
requested inventory is tried. A rejected historical revision is a raw parameter,
never a borrowed success proof. -/
def plans : List (RawEvent Party Good Port Technology Instrument) :=
  (Responsibility.controllerCohort source past nature response).flatMap fun operator =>
    (technologies claim state).map fun technology => plantPlan claim state law members operator technology

omit [DecidableEq Port] in
theorem current_technology_is_always_in_the_source_menu : state.raw.technology ∈ technologies claim state := by
  apply List.mem_dedup.mpr
  exact List.mem_cons_self

theorem each_plan_has_an_original_controller_and_source_technology
    (word : RawEvent Party Good Port Technology Instrument) (member : word ∈ plans claim state law members) :
    ∃ operator ∈ Responsibility.controllerCohort source past nature response,
      ∃ technology ∈ technologies claim state, word = plantPlan claim state law members operator technology := by
  obtain ⟨operator,cohort,inside⟩ := List.mem_flatMap.mp member
  obtain ⟨technology,original,same⟩ := List.mem_map.mp inside
  exact ⟨operator,cohort,technology,original,same.symm⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Compiler
