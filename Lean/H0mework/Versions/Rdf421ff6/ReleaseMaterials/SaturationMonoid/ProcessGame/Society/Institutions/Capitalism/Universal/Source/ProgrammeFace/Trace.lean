import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.RawProgram
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.SourceNativeUniversalRootGrammar
import Mathlib.Data.List.Dedup

/-! The original raw instruction trace generates the finite party, action
and relation incidences.  These are source keys; actors are constructed by
the existing M0 image in the next module. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeFace

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Program UniversalRootGrammar

universe u

variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

abbrev Origin (Party Good Port Technology Instrument : Type u) :=
  RawCurrent Party Good Technology Instrument × RawEvent Party Good Port Technology Instrument

inductive ActionKind
  | request | consent | execution
  deriving DecidableEq

structure ActionSeed (Party : Type u) where
  index : Nat
  kind : ActionKind
  party : Party
  deriving DecidableEq

inductive Point (Party Good Port Technology Instrument : Type u)
  | source (origin : Origin Party Good Port Technology Instrument)
  | party (seed : Party)
  | relation (seed : Port)
  | action (seed : ActionSeed Party)
  | target (current : RawCurrent Party Good Technology Instrument)

def operationParties : Operation Party Good Technology Instrument → List Party
  | .produce operator | .use operator _ _ | .revise operator _ => [operator]
  | .transfer sender recipient _ | .issue _ sender recipient _ |
      .settle _ sender recipient _ => [sender, recipient]
  | .assign _ issuer sender recipient _ => [issuer, sender, recipient]
  | .present => []

variable (law : RawLaw Party Good Port Technology Instrument)

def itemPorts (item : ExecutionItem Party Good Port Technology Instrument) : List Port :=
  item.request.purpose :: law.requiredPorts item.before item.request

def itemParties (item : ExecutionItem Party Good Port Technology Instrument) : List Party :=
  item.request.signer :: (item.request.consents ++ operationParties item.request.operation ++
    ((law.requiredPorts item.before item.request).map (law.controller item.before.technology) ++
      (law.requiredPorts item.before item.request).map
        (law.controller (law.step item.before item.request).technology)))

omit [DecidableEq Port] in
theorem operation_party_mem_itemParties (item : ExecutionItem Party Good Port Technology Instrument)
    (party : Party) (present : party ∈ operationParties item.request.operation) :
    party ∈ itemParties law item := by
  simp only [itemParties, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inl (Or.inr present))

omit [DecidableEq Port] in
theorem actual_target_controller_mem_itemParties
    (item : ExecutionItem Party Good Port Technology Instrument) (port : Port)
    (required : port ∈ law.requiredPorts item.before item.request) :
    law.controller (law.step item.before item.request).technology port ∈ itemParties law item := by
  simp only [itemParties, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inr (Or.inr (List.mem_map.mpr ⟨port, required, rfl⟩)))

omit [DecidableEq Port] in
theorem rejected_target_controller_is_original
    (item : ExecutionItem Party Good Port Technology Instrument) (port : Port)
    (rejected : ¬ law.Valid item.before item.request) :
    law.controller (law.step item.before item.request).technology port =
      law.controller item.before.technology port := by
  rw [law.rejected_preserves_current item.before item.request rejected]

def parties (origin : Origin Party Good Port Technology Instrument) : List Party :=
  ((law.rawItems origin.1 origin.2).flatMap (itemParties law)).dedup

def ports (origin : Origin Party Good Port Technology Instrument) : List Port :=
  ((law.rawItems origin.1 origin.2).flatMap (itemPorts law)).dedup

def itemActions (item : ExecutionItem Party Good Port Technology Instrument) : List (ActionSeed Party) :=
  ⟨item.index, .request, item.request.signer⟩ ::
    ((item.request.consents.map fun party => ⟨item.index, .consent, party⟩) ++
      if law.Valid item.before item.request then
        [⟨item.index, .execution, item.request.signer⟩] else [])

def actions (origin : Origin Party Good Port Technology Instrument) : List (ActionSeed Party) :=
  (law.rawItems origin.1 origin.2).flatMap (itemActions law)

def relationIncidences (origin : Origin Party Good Port Technology Instrument) : List (Port × Party) :=
  (law.rawItems origin.1 origin.2).flatMap fun item =>
    (itemPorts law item).flatMap fun port =>
      (itemParties law item).map fun party => (port, party)

private def branches : List (Point Party Good Port Technology Instrument) →
    AccountedBranches (Point Party Good Port Technology Instrument)
  | [] => .nil
  | point :: tail => .cons (.zero point) (branches tail)

def points (origin : Origin Party Good Port Technology Instrument) :
    List (Point Party Good Port Technology Instrument) :=
  (((parties law origin).map Point.party ++ (ports law origin).map Point.relation) ++
    (actions law origin).map Point.action) ++
    [.target (law.next origin.1 origin.2)]

def trace (origin : Origin Party Good Port Technology Instrument) :
    RootedAccountedUnfolding (Point Party Good Port Technology Instrument) :=
  .occur (.source origin) (branches (points law origin))

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
private theorem branches_trace (nodes : List (Point Party Good Port Technology Instrument)) :
    RootedAccountedUnfolding.traceBranches (branches nodes) = nodes := by
  induction nodes with
  | nil => rfl
  | cons point tail ih =>
      change point :: RootedAccountedUnfolding.traceBranches (branches tail) = point :: tail
      rw [ih]

theorem trace_exact (origin : Origin Party Good Port Technology Instrument) :
    (trace law origin).trace = .source origin :: points law origin := by
  change _ :: RootedAccountedUnfolding.traceBranches (branches _) = _
  rw [branches_trace]

theorem source_mem_trace (origin : Origin Party Good Port Technology Instrument) :
    Point.source origin ∈ (trace law origin).trace := RootedAccountedUnfolding.root_mem_trace _

theorem party_mem_trace (origin : Origin Party Good Port Technology Instrument)
    (party : Party) (present : party ∈ parties law origin) :
    Point.party party ∈ (trace law origin).trace := by
  rw [trace_exact]
  apply List.mem_cons_of_mem
  unfold points
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨party, present, rfl⟩

theorem port_mem_trace (origin : Origin Party Good Port Technology Instrument)
    (port : Port) (present : port ∈ ports law origin) :
    Point.relation port ∈ (trace law origin).trace := by
  rw [trace_exact]
  apply List.mem_cons_of_mem
  unfold points
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨port, present, rfl⟩

theorem target_mem_trace (origin : Origin Party Good Port Technology Instrument) :
    Point.target (law.next origin.1 origin.2) ∈ (trace law origin).trace := by
  rw [trace_exact]
  apply List.mem_cons_of_mem
  exact List.mem_append_right _ List.mem_cons_self

omit [DecidableEq Port] [DecidableEq Instrument] in
theorem item_action_is_actual_submission (item : ExecutionItem Party Good Port Technology Instrument)
    (action : ActionSeed Party) (admitted : action ∈ itemActions law item) :
    action.party = item.request.signer ∨ action.party ∈ item.request.consents := by
  rcases List.mem_cons.mp admitted with first | later
  · cases first
    exact Or.inl rfl
  · rcases List.mem_append.mp later with consent | execution
    · obtain ⟨party, member, same⟩ := List.mem_map.mp consent
      cases same
      exact Or.inr member
    · by_cases valid : law.Valid item.before item.request
      · simp only [if_pos valid, List.mem_singleton] at execution
        cases execution
        exact Or.inl rfl
      · simp only [if_neg valid, List.not_mem_nil] at execution

omit [DecidableEq Port] in
theorem action_party_present (origin : Origin Party Good Port Technology Instrument)
    (action : ActionSeed Party) (admitted : action ∈ actions law origin) :
    action.party ∈ parties law origin := by
  obtain ⟨item, itemMem, actionMem⟩ := List.mem_flatMap.mp admitted
  apply List.mem_dedup.mpr
  apply List.mem_flatMap.mpr
  refine ⟨item, itemMem, ?_⟩
  rcases item_action_is_actual_submission law item action actionMem with signer | consent
  · rw [signer]
    exact List.mem_cons_self
  · simp [itemParties, consent]

omit [DecidableEq Port] in
theorem rejected_no_consent_keeps_only_request
    (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument)
    (rejected : ¬ law.Valid current request) (noConsent : request.consents = []) :
    actions law (current, [request]) = [⟨0, .request, request.signer⟩] := by
  simp [actions, RawLaw.rawItems, RawLaw.execute, itemActions, rejected, noConsent]

omit [DecidableEq Port] in
theorem mentioned_non_signer_has_no_action_on_refusal
    (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument)
    (rejected : ¬ law.Valid current request) (noConsent : request.consents = [])
    (person : Party) (notSigner : person ≠ request.signer) (kind : ActionKind) :
    (⟨0, kind, person⟩ : ActionSeed Party) ∉ actions law (current, [request]) := by
  rw [rejected_no_consent_keeps_only_request law current request rejected noConsent]
  intro member
  have same := List.mem_singleton.mp member
  exact notSigner (congrArg ActionSeed.party same)

omit [DecidableEq Port] in
theorem relation_party_present (origin : Origin Party Good Port Technology Instrument)
    (incidence : Port × Party) (admitted : incidence ∈ relationIncidences law origin) :
    incidence.2 ∈ parties law origin := by
  obtain ⟨item, itemMem, portMem⟩ := List.mem_flatMap.mp admitted
  obtain ⟨port, _inPorts, pairMem⟩ := List.mem_flatMap.mp portMem
  obtain ⟨party, partyMem, same⟩ := List.mem_map.mp pairMem
  cases same
  apply List.mem_dedup.mpr
  exact List.mem_flatMap.mpr ⟨item, itemMem, partyMem⟩

theorem relation_port_present (origin : Origin Party Good Port Technology Instrument)
    (incidence : Port × Party) (admitted : incidence ∈ relationIncidences law origin) :
    incidence.1 ∈ ports law origin := by
  obtain ⟨item, itemMem, portMem⟩ := List.mem_flatMap.mp admitted
  obtain ⟨port, inPorts, pairMem⟩ := List.mem_flatMap.mp portMem
  obtain ⟨party, _partyMem, same⟩ := List.mem_map.mp pairMem
  cases same
  apply List.mem_dedup.mpr
  exact List.mem_flatMap.mpr ⟨item, itemMem, inPorts⟩

omit [DecidableEq Port] in
theorem item_relation_present (origin : Origin Party Good Port Technology Instrument)
    (item : ExecutionItem Party Good Port Technology Instrument)
    (itemMem : item ∈ law.rawItems origin.1 origin.2) (port : Port) (party : Party)
    (portMem : port ∈ itemPorts law item) (partyMem : party ∈ itemParties law item) :
    (port, party) ∈ relationIncidences law origin :=
  List.mem_flatMap.mpr ⟨item, itemMem,
    List.mem_flatMap.mpr ⟨port, portMem, List.mem_map.mpr ⟨party, partyMem, rfl⟩⟩⟩

omit [DecidableEq Port] in
theorem controller_mem_itemParties (item : ExecutionItem Party Good Port Technology Instrument)
    (port : Port) (required : port ∈ law.requiredPorts item.before item.request) :
    law.controller item.before.technology port ∈ itemParties law item := by
  have present : law.controller item.before.technology port ∈
      (law.requiredPorts item.before item.request).map (law.controller item.before.technology) :=
    List.mem_map.mpr ⟨port, required, rfl⟩
  simp only [itemParties, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inr (Or.inl present))

def partyAt : Point Party Good Port Technology Instrument → Option Party
  | .party party => some party
  | _ => none

def portAt : Point Party Good Port Technology Instrument → Option Port
  | .relation port => some port
  | _ => none

def actorLineage (origin : Origin Party Good Port Technology Instrument) (party : Party) : List Party :=
  ((sourceGeneratedDependentFaceAudit (trace law origin)).filterMap partyAt).filter
    (fun candidate => decide (candidate = party))

def relationLineage (origin : Origin Party Good Port Technology Instrument) (port : Port) : List Port :=
  ((sourceGeneratedDependentFaceAudit (trace law origin)).filterMap portAt).filter
    (fun candidate => decide (candidate = port))

theorem actorLineage_contains_seed (origin : Origin Party Good Port Technology Instrument)
    (party : Party) (present : party ∈ parties law origin) :
    party ∈ actorLineage law origin party := by
  apply List.mem_filter.mpr
  refine ⟨?_, by simp⟩
  rw [sourceGeneratedDependentFaceAudit_eq_trace]
  exact List.mem_filterMap.mpr ⟨Point.party party, party_mem_trace law origin party present, rfl⟩

theorem actorLineage_distinguishes (origin : Origin Party Good Port Technology Instrument)
    (first second : Party) (present : first ∈ parties law origin)
    (same : actorLineage law origin first = actorLineage law origin second) : first = second := by
  have member := actorLineage_contains_seed law origin first present
  rw [same] at member
  exact of_decide_eq_true (List.mem_filter.mp member).2

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeFace
