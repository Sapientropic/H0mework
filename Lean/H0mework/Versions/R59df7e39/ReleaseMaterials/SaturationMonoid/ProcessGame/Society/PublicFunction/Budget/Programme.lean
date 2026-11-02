import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Normalization.Acceptance
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Whole.Complete

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency Distributed.Recall.Information.Agency.Protocol
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (code : Code Party Good Port (Mandate.State Party Technology) Instrument)

/-- Raw work has no catalogue-membership or word-length field. -/
structure Rule where
  work : Option code.Policy
  events : EventTable code

abbrev Program := List (Rule code)

namespace Rule
variable {code}
def ofOriginal (rule : Distributed.Recall.Information.Agency.Protocol.Rule code) : Rule code :=
  ⟨some rule.work.val,rule.events⟩
def normalize (cap : Nat) (rule : Rule code) : Rule code :=
  ⟨rule.work.map (Normalization.policy code cap),rule.events⟩
def supported (rule : Rule code) : Prop :=
  ∀ policy, rule.work = some policy → Normalization.Supported code policy
end Rule

def stage (reference : Rule code) (program : Program code) (ordinal : Nat) : Rule code :=
  (program[ordinal]?).getD (program.getLast?.getD reference)

def localEvent (rule : Rule code) (site : Fin code.sites) (signal : Fin code.signals) : Move code :=
  (rule.events (site,signal) (code.key_mem _)).val

def driver (start : Nat) (rule : Rule code) (rival : Opponent code) : Opponent code :=
  fun history past frame => match ownerAt code start history.length with
    | some site => localEvent code rule site (frame.inbox site)
    | none => externalChoice code (rival history past frame)

variable {code}
  (point : Continuation.Cursor code) (reference : Rule code) (program : Program code)

def controller (rival : Opponent code) : Opponent code := fun history past frame =>
  driver code point.ownerStart
    (stage code reference program (history.length-(point.history.length+1+point.cut))) rival history past frame

omit [DecidableEq Port] [DecidableEq Technology] in
theorem actual_owned_decision_uses_only_the_workers_record
    (first second : Opponent code) (history : History) (past : Events code)
    (left right : code.Frame) (site : Fin code.sites)
    (owned : ownerAt code point.ownerStart history.length = some site)
    (same : left.inbox site = right.inbox site) :
    controller point reference program first history past left = controller point reference program second history past right := by
  simp only [controller,driver,owned,same]

def schedule : List (Option code.Policy) :=
  (List.range (Cut.horizon point.source point.entry point.cut)).map fun ordinal =>
    (stage code reference program ordinal).work

abbrev source (rival : Opponent code) := Future.target point.source point.entry point.cut
  (controller point reference program rival) (schedule point reference program)
abbrev entry (rival : Opponent code) := Future.takeover point.source point.entry point.cut
  (controller point reference program rival)

def normalized (cap horizon : Nat) (reference : Rule code) (program : Program code) : Program code :=
  (List.range horizon).map fun ordinal => (stage code reference program ordinal).normalize cap

omit [DecidableEq Port] [DecidableEq Technology] in
theorem normalized_at (cap horizon ordinal : Nat) (inside : ordinal < horizon) :
    stage code reference (normalized cap horizon reference program) ordinal =
      (stage code reference program ordinal).normalize cap := by
  simp only [stage,normalized,List.getElem?_map,List.getElem?_range inside,Option.map_some,Option.getD_some]

omit [DecidableEq Port] [DecidableEq Technology] in
theorem normalization_retains_each_owned_event (cap horizon ordinal : Nat) (inside : ordinal < horizon)
    (site : Fin code.sites) (signal : Fin code.signals) :
    localEvent code (stage code reference (normalized cap horizon reference program) ordinal) site signal =
      localEvent code (stage code reference program ordinal) site signal := by
  rw [normalized_at reference program cap horizon ordinal inside]
  rfl

variable (code)
def ruleMenu (cap : Nat) : List (Rule code) :=
  (none :: (List.pi code.keys (fun _ => words code.actions cap)).map some).flatMap fun work =>
    (eventTables code).map fun events => ⟨work,events⟩

def programs (cap horizon : Nat) : List (Program code) :=
  sequences (ruleMenu code cap) horizon

omit [DecidableEq Port] [DecidableEq Technology] in
theorem every_supported_normalization_is_generated (cap horizon : Nat)
    (supported : ∀ ordinal < horizon, (stage code reference program ordinal).supported) :
    normalized cap horizon reference program ∈ programs code cap horizon := by
  apply (mem_sequences_iff _ _ _).mpr
  refine ⟨by simp only [normalized,List.length_map,List.length_range];omega,?_⟩
  intro rule member
  obtain ⟨ordinal,inside,rfl⟩ := List.mem_map.mp member
  have original := supported ordinal (List.mem_range.mp inside)
  apply List.mem_flatMap.mpr
  refine ⟨(stage code reference program ordinal).work.map (Normalization.policy code cap),?_,?_⟩
  · cases chosen : (stage code reference program ordinal).work with
    | none => exact List.mem_cons_self
    | some policy =>
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨_,
        Normalization.every_normalized_raw_table_is_finitely_enumerated code cap policy (original policy chosen),rfl⟩)
  · apply List.mem_map.mpr
    refine ⟨(stage code reference program ordinal).events,?_,rfl⟩
    apply (List.mem_pi _ _).mpr
    intro key inside
    exact List.mem_attach _ _

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme
