import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Search

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Review

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code))

/-- All native anchor coordinates are exactly the original due multiset order. -/
def packedNoWorse (first second : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code) : Prop :=
  ∀ world ∈ Replanning.points model domain,
    ∀ table ∈ Cut.tables world.val.source world.val.entry world.val.cut,
      let current := Replanning.tableEvaluation model world.val first table
      let prior := Replanning.tableEvaluation model world.val second table
      (Authority.Trace.Lawful.inventory current.native).due.Subperm
        (Authority.Trace.Lawful.inventory prior.native).due ∧
      ∀ axis ∈ economicAxes world.val.source world.val.cut,current.value axis ≤ prior.value axis

instance (first second : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code) : Decidable (packedNoWorse model domain first second) := by
  unfold packedNoWorse
  infer_instance

theorem packedNoWorse_iff (first second : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)  :
    packedNoWorse model domain first second ↔
      Distributed.NoWorse (Search.axes model domain)
        (Search.benefit model domain) first second := by
  constructor
  · intro all coordinate _
    cases coordinate with
    | economic world table axis =>
      exact (all world (Replanning.every_point_is_source_generated model domain world) table.val table.property).2 axis.val axis.property
    | native world table anchor =>
      have due := (all world (Replanning.every_point_is_source_generated model domain world) table.val table.property).1
      change (Authority.Trace.Lawful.inventory (Replanning.readTable model domain world first table).native).due.Subperm
        (Authority.Trace.Lawful.inventory (Replanning.readTable model domain world second table).native).due at due
      change (if _ then (0 : ℚ) else 1) ≤ (if _ then 0 else 1)
      by_cases old : (Authority.Trace.Lawful.inventory (Replanning.readTable model domain world second table).native).due.Subperm
          (Authority.Trace.Lawful.inventory (Replanning.readTable model domain world anchor table).native).due
      · have current := due.trans old
        simp only [if_pos old,if_pos current,le_refl]
      · split <;> simp_all
  · intro all world _ table inside
    let sourceTable : Replanning.TableAt model domain world := ⟨table,inside⟩
    have nativeInside : Replanning.Axis.native world sourceTable second ∈ Search.axes model domain :=
      List.mem_flatMap.mpr ⟨world,List.mem_attach _ _,List.mem_flatMap.mpr
        ⟨sourceTable,List.mem_attach _ _,List.mem_append_right _ (List.mem_map.mpr ⟨second,every_rule_is_source_generated _ _,rfl⟩)⟩⟩
    have native := all _ nativeInside
    have reflexive : (Authority.Trace.Lawful.inventory (Replanning.readTable model domain world second sourceTable).native).due.Subperm
        (Authority.Trace.Lawful.inventory (Replanning.readTable model domain world second sourceTable).native).due := List.Subperm.refl _
    change (if _ then (0 : ℚ) else 1) ≤ (if _ then 0 else 1) at native
    rw [if_pos reflexive] at native
    have due : (Authority.Trace.Lawful.inventory (Replanning.readTable model domain world first sourceTable).native).due.Subperm
        (Authority.Trace.Lawful.inventory (Replanning.readTable model domain world second sourceTable).native).due := by
      split at native
      · assumption
      · norm_num at native
    refine ⟨due,?_⟩
    intro axis generated
    exact all (.economic world sourceTable ⟨axis,generated⟩)
      (List.mem_flatMap.mpr ⟨world,List.mem_attach _ _,List.mem_flatMap.mpr
        ⟨sourceTable,List.mem_attach _ _,List.mem_append_left _ (List.mem_map.mpr ⟨⟨axis,generated⟩,List.mem_attach _ _,rfl⟩)⟩⟩)

def packedImproves (first second : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code) : Prop :=
  packedNoWorse model domain second first ∧ ¬ packedNoWorse model domain first second

instance (first second : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code) : Decidable (packedImproves model domain first second) := by
  unfold packedImproves
  infer_instance

theorem packedImproves_iff (first second : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)  :
    packedImproves model domain first second ↔
      Distributed.Improves (Search.axes model domain) (Search.benefit model domain) first second := by
  simp only [packedImproves,Distributed.Improves,packedNoWorse_iff model domain second first,
    packedNoWorse_iff model domain first second]

private theorem quiet_table (point : Cursor model.source.code)
    (protocol : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)
    (table : Cut.Table point.source point.entry point.cut)
    (quiet : PublicDomain.quiet (code := model.source.code) = true) :
    Replanning.tableEvaluation model point protocol table =
      Replanning.actualEvaluation model point protocol PublicDomain.silent := by
  rw [Replanning.table_evaluation_is_its_own_actual_protocol]
  have same := PublicDomain.quiet_controllers_are_identical quiet point protocol
    (Cut.opponent point.source point.entry point.cut table)
  unfold Replanning.actualEvaluation
  rw [same]

def noWorse (first second : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code) : Prop :=
  if PublicDomain.quiet (code := model.source.code) then
    ∀ world ∈ Replanning.points model domain,
      let current := Replanning.actualEvaluation model world.val first PublicDomain.silent
      let prior := Replanning.actualEvaluation model world.val second PublicDomain.silent
      (Authority.Trace.Lawful.inventory current.native).due.Subperm
        (Authority.Trace.Lawful.inventory prior.native).due ∧
      ∀ axis ∈ economicAxes world.val.source world.val.cut,current.value axis ≤ prior.value axis
  else packedNoWorse model domain first second

instance (first second : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code) :
    Decidable (noWorse model domain first second) := by
  unfold noWorse
  split <;> infer_instance

theorem noWorse_iff (first second : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code) :
    noWorse model domain first second ↔
      Distributed.NoWorse (Search.axes model domain) (Search.benefit model domain) first second := by
  rw [←packedNoWorse_iff]
  unfold noWorse
  split
  · rename_i quiet
    constructor
    · intro all world inside table _
      dsimp only
      rw [quiet_table model world.val first table quiet,quiet_table model world.val second table quiet]
      exact all world inside
    · intro all world inside
      have original := all world inside (externalTable world.val PublicDomain.silent)
        (Residual.restriction_is_generated _ _ _ PublicDomain.silent)
      dsimp only at original
      rw [quiet_table model world.val first _ quiet,quiet_table model world.val second _ quiet] at original
      exact original
  · exact Iff.rfl

def improves (first second : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code) : Prop :=
  noWorse model domain second first ∧ ¬ noWorse model domain first second

instance (first second : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code) :
    Decidable (improves model domain first second) := by
  unfold improves
  infer_instance

theorem improves_iff (first second : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code) :
    improves model domain first second ↔
      Distributed.Improves (Search.axes model domain) (Search.benefit model domain) first second := by
  simp only [improves,Distributed.Improves,noWorse_iff]

/-- The independent checker recomputes the original evaluator; it does not consume
    a planner's maximality proof or a caller's preferred ranking. -/
def verify (reference proposed : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code) : Bool :=
  decide (Search.acceptable model domain reference proposed ∧
    ∀ other ∈ rules model.source.code,Search.acceptable model domain reference other →
      ¬ improves model domain proposed other)

theorem verify_exact (reference proposed : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code) :
    verify model domain reference proposed = Search.verify model domain reference proposed := by
  apply Bool.eq_iff_iff.mpr
  simp only [verify,Search.verify,decide_eq_true_eq,improves_iff]

variable (reference : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)

private structure Scanned (seed : Search.Candidate model domain reference) (remaining : List (Search.Candidate model domain reference)) where
  policy : Search.Candidate model domain reference
  original : policy = seed ∨ policy ∈ remaining
  advances : policy = seed ∨ Distributed.Improves (Search.axes model domain) (fun candidate : Search.Candidate model domain reference => Search.benefit model domain candidate.protocol) seed policy
  maximal : ∀ other ∈ remaining, ¬ Distributed.Improves (Search.axes model domain) (fun candidate : Search.Candidate model domain reference => Search.benefit model domain candidate.protocol) policy other

private theorem cannot_improve_seed {seed : Search.Candidate model domain reference} {remaining : List (Search.Candidate model domain reference)}
    (result : Scanned model domain reference seed remaining) : ¬ Distributed.Improves (Search.axes model domain) (fun candidate : Search.Candidate model domain reference => Search.benefit model domain candidate.protocol) result.policy seed := by
  intro backward
  rcases result.advances with same | forward
  · apply improves_irrefl (Search.axes model domain) (fun candidate : Search.Candidate model domain reference => Search.benefit model domain candidate.protocol) seed
    simpa only [same] using backward
  · exact improves_irrefl (Search.axes model domain) (fun candidate : Search.Candidate model domain reference => Search.benefit model domain candidate.protocol) seed (improves_trans forward backward)

private def scan (seed : Search.Candidate model domain reference) : (remaining : List (Search.Candidate model domain reference)) → Scanned model domain reference seed remaining
  | [] => ⟨seed, .inl rfl, .inl rfl, by simp⟩
  | head :: tail =>
    if compact : improves model domain seed.protocol head.protocol then
      have improves : Distributed.Improves (Search.axes model domain)
          (fun candidate : Search.Candidate model domain reference => Search.benefit model domain candidate.protocol) seed head :=
        (improves_iff model domain seed.protocol head.protocol).mp compact
      let result := scan head tail
      { policy := result.policy
        original := .inr (by
          rcases result.original with same | inside
          · simpa only [same] using (List.mem_cons_self : head ∈ head :: tail)
          · exact List.mem_cons_of_mem _ inside)
        advances := .inr (by
          rcases result.advances with same | further
          · exact same.symm ▸ improves
          · exact improves_trans improves further)
        maximal := by
          intro other inside
          rcases List.mem_cons.mp inside with same | later
          · subst other; exact cannot_improve_seed model domain reference result
          · exact result.maximal other later }
    else
      have improves : ¬ Distributed.Improves (Search.axes model domain)
          (fun candidate : Search.Candidate model domain reference => Search.benefit model domain candidate.protocol) seed head :=
        fun better => compact ((improves_iff model domain seed.protocol head.protocol).mpr better)
      let result := scan seed tail
      { policy := result.policy
        original := result.original.imp_right (List.mem_cons_of_mem _)
        advances := result.advances
        maximal := by
          intro other inside
          rcases List.mem_cons.mp inside with same | later
          · subst other
            intro backward
            rcases result.advances with same | forward
            · exact improves (same ▸ backward)
            · exact improves (improves_trans forward backward)
          · exact result.maximal other later }

def choose (pool : List (Search.Candidate model domain reference)) :
    Option (Selected (Search.axes model domain)
      (fun candidate : Search.Candidate model domain reference => Search.benefit model domain candidate.protocol) pool) :=
  match same : pool with
  | [] => none
  | head :: tail =>
      let result := scan model domain reference head tail
      some ⟨result.policy,by
        rcases result.original with same | inside
        · simpa only [same] using (List.mem_cons_self : head ∈ head::tail)
        · exact List.mem_cons_of_mem _ inside,by
        intro other inside
        rcases List.mem_cons.mp inside with same | inside
        · subst other;exact cannot_improve_seed model domain reference result
        · exact result.maximal other inside⟩

theorem choose_none_iff_empty (pool : List (Search.Candidate model domain reference)) :
    choose model domain reference pool = none ↔ pool = [] := by
  unfold choose
  split <;> simp_all

/-- Same original Rule family and full relation, evaluated through its proved
    multiset order and same-occurrence quiet equalities. -/
def compile : Search.Outcome model domain reference :=
  match result : choose model domain reference (Search.candidates model domain reference) with
  | some choice => .selected choice
  | none => .blocked (fun protocol =>
      match Distributed.inspect (Search.holds model domain reference protocol) (Search.rows model domain) with
      | .rejected row original broken => ⟨row,original,broken⟩
      | .accepted all => False.elim (by
          obtain ⟨candidate,inside,_⟩ := Search.every_accepted_protocol_is_generated model domain reference protocol all
          rw [choose_none_iff_empty] at result
          simp only [result,List.not_mem_nil] at inside))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Review
