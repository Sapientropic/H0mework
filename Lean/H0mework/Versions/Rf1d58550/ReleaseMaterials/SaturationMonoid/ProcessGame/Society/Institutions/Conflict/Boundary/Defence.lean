import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary.Containment

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument
local notation "Item" => ExecutionItem Party Good Port Technology Instrument

variable {source : Root.Cut Party Good Port Technology Instrument}
  {attackWord : RawEvent Party Good Port Technology Instrument}
  {community : Party → Community}

abbrev AggressionAt.after (_attack : AggressionAt source attackWord community) : C :=
  Root.terminal source attackWord

def AggressionAt.residents (attack : AggressionAt source attackWord community) : List Party :=
  source.members.filter (fun member => decide (community member = community attack.victim))

def GuardAt (attack : AggressionAt source attackWord community) (item : Item) : Prop :=
  ClosesPermission attack.after.native.input.law attack.item.request item →
    item.request.signer ∈ attack.residents

instance (attack : AggressionAt source attackWord community) (item : Item) :
    Decidable (GuardAt attack item) := by
  unfold GuardAt
  infer_instance

abbrev responseItems (attack : AggressionAt source attackWord community) (response : Word) :=
  attack.after.native.input.law.rawItems attack.after.raw response

/-- A defensive response acts on a still-live foreign capture permission,
charges no new unassented crossing, and pays the original local exit floor
from its literal generated successor. -/
structure DefenceAt (attack : AggressionAt source attackWord community) (response continuation : Word) : Prop where
  victimStanding : attack.victim ∈ source.members
  active : Permission attack.after.native.input.law attack.after.raw attack.item.request
  responsePaid : Root.Paid attack.after response
  closed : ¬ Permission attack.after.native.input.law (Root.terminal attack.after response).raw attack.item.request
  localOwners : ∀ item ∈ responseItems attack response, GuardAt attack item
  noOverreach : ¬ Nonempty (AggressionAt attack.after response community)
  independentExit : ExitFloorAt source (Root.terminal attack.after response) attack.residents continuation

inductive DefenceFailure (attack : AggressionAt source attackWord community) (response continuation : Word)
  | noStanding (absent : attack.victim ∉ source.members)
  | noLivePermission (alreadyClosed : ¬ Permission attack.after.native.input.law attack.after.raw attack.item.request)
  | payment (failed : Root.Failure attack.after response)
  | stillOpen (openAfter : Permission attack.after.native.input.law
      (Root.terminal attack.after response).raw attack.item.request)
  | outsider (item : Item) (original : item ∈ responseItems attack response) (failed : ¬ GuardAt attack item)
  | overreach (newCapture : AggressionAt attack.after response community)
  | exit (failed : ExitFailure source (Root.terminal attack.after response) attack.residents continuation)

inductive DefenceDecision (attack : AggressionAt source attackWord community) (response continuation : Word)
  | permitted (defended : DefenceAt attack response continuation)
  | refused (failure : DefenceFailure attack response continuation)

def inspectDefence (attack : AggressionAt source attackWord community) (response continuation : Word) :
    DefenceDecision attack response continuation :=
  if standing : attack.victim ∈ source.members then
    if active : Permission attack.after.native.input.law attack.after.raw attack.item.request then
      match Root.inspect attack.after response with
      | .rejected failed => .refused (.payment failed)
      | .paid paid =>
          if openAfter : Permission attack.after.native.input.law
              (Root.terminal attack.after response).raw attack.item.request then
            .refused (.stillOpen openAfter)
          else
            match Material.inspectList (GuardAt attack) (responseItems attack response) with
            | .failure item original failed => .refused (.outsider item original failed)
            | .clear localOwners =>
                match generated : aggressions attack.after response community paid with
                | newCapture :: _ => .refused (.overreach newCapture)
                | [] =>
                    have noOverreach : ¬ Nonempty (AggressionAt attack.after response community) := by
                      rintro ⟨capture⟩
                      have listed := capture.listed_in_generated_aggressions
                      rw [generated] at listed
                      exact List.not_mem_nil listed
                    match inspectExit source (Root.terminal attack.after response) attack.residents continuation with
                    | .refused failed => .refused (.exit failed)
                    | .preserved exit =>
                        .permitted ⟨standing, active, paid, openAfter,
                          fun item original => localOwners item original, noOverreach, exit⟩
    else .refused (.noLivePermission active)
  else .refused (.noStanding standing)

def inspectOriginalDefence (attack : AggressionAt source attackWord community) (response : Word) :=
  inspectDefence attack response (originalExitWord source (Root.terminal attack.after response))

/-- The permission was closed by an actual signed local instruction, and
the same successor offers the original local floor through a paid exit. -/
theorem DefenceAt.local_closure_and_independent_exit
    {attack : AggressionAt source attackWord community} {response continuation : Word}
    (defended : DefenceAt attack response continuation) :
    (∃ item ∈ responseItems attack response,
      item.request.signer ∈ attack.residents ∧
      attack.after.native.input.law.Valid item.before item.request ∧
      ClosesPermission attack.after.native.input.law attack.item.request item) ∧
    ¬ attack.after.native.input.law.Valid (Root.terminal attack.after response).raw attack.item.request ∧
    Quantities.Settled (Root.terminal attack.after response) (Quantities.Execution.primitiveScript continuation) := by
  let law := attack.after.native.input.law
  have closes := defended.closed
  rw [defended.responsePaid.original_raw_exact] at closes
  obtain ⟨item, original, action⟩ := an_actual_instruction_closes_permission law attack.item.request
    response attack.after.raw 0 defended.active closes
  have valid : law.Valid item.before item.request := by
    by_contra refused
    have unchanged := law.rejected_preserves_current item.before item.request refused
    apply action.2
    rw [unchanged]
    exact action.1
  exact ⟨⟨item, original, defended.localOwners item original action, valid, action⟩,
    fun valid => defended.closed (permission_of_valid _ _ _ valid), defended.independentExit.paid.whole⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary
