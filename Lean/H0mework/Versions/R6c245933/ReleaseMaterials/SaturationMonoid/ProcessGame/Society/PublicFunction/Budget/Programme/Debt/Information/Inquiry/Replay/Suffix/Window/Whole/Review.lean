import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Review

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
  (original : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)
  {fuel : Nat}

/-- All native anchor coordinates are exactly the original due multiset order. -/
def packedNoWorse (first second : Program model.source.code fuel) : Prop :=
  ∀ world ∈ Replanning.points model domain,
    ∀ table ∈ Cut.tables world.val.source world.val.entry world.val.cut,
      let current := tableEvaluation model world.val original first table
      let prior := tableEvaluation model world.val original second table
      (Authority.Trace.Lawful.inventory current.native).due.Subperm
        (Authority.Trace.Lawful.inventory prior.native).due ∧
      ∀ axis ∈ economicAxes world.val.source world.val.cut,current.value axis ≤ prior.value axis

instance (first second : Program model.source.code fuel) : Decidable (packedNoWorse model domain original first second) := by
  unfold packedNoWorse
  infer_instance

theorem packedNoWorse_iff (first second : Program model.source.code fuel)  :
    packedNoWorse model domain original first second ↔
      Distributed.NoWorse (Selection.axes (fuel := fuel) model domain)
        (Selection.benefit model domain original) first second := by
  constructor
  · intro all coordinate _
    cases coordinate with
    | economic world table axis =>
      exact (all world (Replanning.every_point_is_source_generated model domain world) table.val table.property).2 axis.val axis.property
    | native world table anchor =>
      have due := (all world (Replanning.every_point_is_source_generated model domain world) table.val table.property).1
      change (Authority.Trace.Lawful.inventory (Selection.readTable model domain original world first table).native).due.Subperm
        (Authority.Trace.Lawful.inventory (Selection.readTable model domain original world second table).native).due at due
      change (if _ then (0 : ℚ) else 1) ≤ (if _ then 0 else 1)
      by_cases old : (Authority.Trace.Lawful.inventory (Selection.readTable model domain original world second table).native).due.Subperm
          (Authority.Trace.Lawful.inventory (Selection.readTable model domain original world anchor table).native).due
      · have current := due.trans old
        simp only [if_pos old,if_pos current,le_refl]
      · split <;> simp_all
  · intro all world _ table inside
    let sourceTable : Replanning.TableAt model domain world := ⟨table,inside⟩
    have nativeInside : Selection.Axis.native world sourceTable second ∈ Selection.axes (fuel := fuel) model domain :=
      List.mem_flatMap.mpr ⟨world,List.mem_attach _ _,List.mem_flatMap.mpr
        ⟨sourceTable,List.mem_attach _ _,List.mem_append_right _ (List.mem_map.mpr ⟨second,every_bounded_program_is_source_generated _ _ _,rfl⟩)⟩⟩
    have native := all _ nativeInside
    have reflexive : (Authority.Trace.Lawful.inventory (Selection.readTable model domain original world second sourceTable).native).due.Subperm
        (Authority.Trace.Lawful.inventory (Selection.readTable model domain original world second sourceTable).native).due := List.Subperm.refl _
    change (if _ then (0 : ℚ) else 1) ≤ (if _ then 0 else 1) at native
    rw [if_pos reflexive] at native
    have due : (Authority.Trace.Lawful.inventory (Selection.readTable model domain original world first sourceTable).native).due.Subperm
        (Authority.Trace.Lawful.inventory (Selection.readTable model domain original world second sourceTable).native).due := by
      split at native
      · assumption
      · norm_num at native
    refine ⟨due,?_⟩
    intro axis generated
    exact all (.economic world sourceTable ⟨axis,generated⟩)
      (List.mem_flatMap.mpr ⟨world,List.mem_attach _ _,List.mem_flatMap.mpr
        ⟨sourceTable,List.mem_attach _ _,List.mem_append_left _ (List.mem_map.mpr ⟨⟨axis,generated⟩,List.mem_attach _ _,rfl⟩)⟩⟩)

def packedImproves (first second : Program model.source.code fuel) : Prop :=
  packedNoWorse model domain original second first ∧ ¬ packedNoWorse model domain original first second

instance (first second : Program model.source.code fuel) : Decidable (packedImproves model domain original first second) := by
  unfold packedImproves
  infer_instance

theorem packedImproves_iff (first second : Program model.source.code fuel)  :
    packedImproves model domain original first second ↔
      Distributed.Improves (Selection.axes (fuel := fuel) model domain) (Selection.benefit model domain original) first second := by
  simp only [packedImproves,Distributed.Improves,packedNoWorse_iff model domain original second first,
    packedNoWorse_iff model domain original first second]

private theorem quiet_table (point : Cursor model.source.code)
    (protocol : Program model.source.code fuel)
    (table : Cut.Table point.source point.entry point.cut)
    (quiet : PublicDomain.quiet (code := model.source.code) = true) :
    tableEvaluation model point original protocol table =
      actualEvaluation model point original protocol PublicDomain.silent := by
  exact quiet_evaluation model point original protocol quiet _

def noWorse (first second : Program model.source.code fuel) : Prop :=
  if PublicDomain.quiet (code := model.source.code) then
    ∀ world ∈ Replanning.points model domain,
      let current := actualEvaluation model world.val original first PublicDomain.silent
      let prior := actualEvaluation model world.val original second PublicDomain.silent
      (Authority.Trace.Lawful.inventory current.native).due.Subperm
        (Authority.Trace.Lawful.inventory prior.native).due ∧
      ∀ axis ∈ economicAxes world.val.source world.val.cut,current.value axis ≤ prior.value axis
  else packedNoWorse model domain original first second

instance (first second : Program model.source.code fuel) :
    Decidable (noWorse model domain original first second) := by
  unfold noWorse
  split <;> infer_instance

theorem noWorse_iff (first second : Program model.source.code fuel) :
    noWorse model domain original first second ↔
      Distributed.NoWorse (Selection.axes (fuel := fuel) model domain) (Selection.benefit model domain original) first second := by
  rw [←packedNoWorse_iff]
  unfold noWorse
  split
  · rename_i quiet
    constructor
    · intro all world inside table _
      dsimp only
      rw [quiet_table model original world.val first table quiet,quiet_table model original world.val second table quiet]
      exact all world inside
    · intro all world inside
      have checked := all world inside (externalTable world.val PublicDomain.silent)
        (Residual.restriction_is_generated _ _ _ PublicDomain.silent)
      dsimp only at checked
      rw [quiet_table model original world.val first _ quiet,quiet_table model original world.val second _ quiet] at checked
      exact checked
  · exact Iff.rfl

def improves (first second : Program model.source.code fuel) : Prop :=
  noWorse model domain original second first ∧ ¬ noWorse model domain original first second

instance (first second : Program model.source.code fuel) :
    Decidable (improves model domain original first second) := by
  unfold improves
  infer_instance

theorem improves_iff (first second : Program model.source.code fuel) :
    improves model domain original first second ↔
      Distributed.Improves (Selection.axes (fuel := fuel) model domain) (Selection.benefit model domain original) first second := by
  simp only [improves,Distributed.Improves,noWorse_iff]

/-- The independent checker recomputes the original evaluator; it does not consume
    a planner's maximality proof or a caller's preferred ranking. -/
def verify (reference proposed : Program model.source.code fuel) : Bool :=
  decide (Selection.acceptable model domain original reference proposed ∧
    ∀ other ∈ programs model.source.code fuel,Selection.acceptable model domain original reference other →
      ¬ improves model domain original proposed other)

theorem verify_exact (reference proposed : Program model.source.code fuel) :
    verify model domain original reference proposed = Selection.verify model domain original reference proposed := by
  apply Bool.eq_iff_iff.mpr
  simp only [verify,Selection.verify,decide_eq_true_eq,improves_iff]

variable (reference : Program model.source.code fuel)

private structure Scanned (seed : Selection.Candidate model domain original reference) (remaining : List (Selection.Candidate model domain original reference)) where
  policy : Selection.Candidate model domain original reference
  lineage : policy = seed ∨ policy ∈ remaining
  advances : policy = seed ∨ Distributed.Improves (Selection.axes (fuel := fuel) model domain) (fun candidate : Selection.Candidate model domain original reference => Selection.benefit model domain original candidate.protocol) seed policy
  maximal : ∀ other ∈ remaining, ¬ Distributed.Improves (Selection.axes (fuel := fuel) model domain) (fun candidate : Selection.Candidate model domain original reference => Selection.benefit model domain original candidate.protocol) policy other

private theorem cannot_improve_seed {seed : Selection.Candidate model domain original reference} {remaining : List (Selection.Candidate model domain original reference)}
    (result : Scanned model domain original reference seed remaining) : ¬ Distributed.Improves (Selection.axes (fuel := fuel) model domain) (fun candidate : Selection.Candidate model domain original reference => Selection.benefit model domain original candidate.protocol) result.policy seed := by
  intro backward
  rcases result.advances with same | forward
  · apply improves_irrefl (Selection.axes (fuel := fuel) model domain) (fun candidate : Selection.Candidate model domain original reference => Selection.benefit model domain original candidate.protocol) seed
    simpa only [same] using backward
  · exact improves_irrefl (Selection.axes (fuel := fuel) model domain) (fun candidate : Selection.Candidate model domain original reference => Selection.benefit model domain original candidate.protocol) seed (improves_trans forward backward)

private def scan (seed : Selection.Candidate model domain original reference) : (remaining : List (Selection.Candidate model domain original reference)) → Scanned model domain original reference seed remaining
  | [] => ⟨seed, .inl rfl, .inl rfl, by simp⟩
  | head :: tail =>
    if compact : improves model domain original seed.protocol head.protocol then
      have improves : Distributed.Improves (Selection.axes (fuel := fuel) model domain)
          (fun candidate : Selection.Candidate model domain original reference => Selection.benefit model domain original candidate.protocol) seed head :=
        (improves_iff model domain original seed.protocol head.protocol).mp compact
      let result := scan head tail
      { policy := result.policy
        lineage := .inr (by
          rcases result.lineage with same | inside
          · simpa only [same] using (List.mem_cons_self : head ∈ head :: tail)
          · exact List.mem_cons_of_mem _ inside)
        advances := .inr (by
          rcases result.advances with same | further
          · exact same.symm ▸ improves
          · exact improves_trans improves further)
        maximal := by
          intro other inside
          rcases List.mem_cons.mp inside with same | later
          · subst other; exact cannot_improve_seed model domain original reference result
          · exact result.maximal other later }
    else
      have improves : ¬ Distributed.Improves (Selection.axes (fuel := fuel) model domain)
          (fun candidate : Selection.Candidate model domain original reference => Selection.benefit model domain original candidate.protocol) seed head :=
        fun better => compact ((improves_iff model domain original seed.protocol head.protocol).mpr better)
      let result := scan seed tail
      { policy := result.policy
        lineage := result.lineage.imp_right (List.mem_cons_of_mem _)
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

def choose (pool : List (Selection.Candidate model domain original reference)) :
    Option (Selected (Selection.axes (fuel := fuel) model domain)
      (fun candidate : Selection.Candidate model domain original reference => Selection.benefit model domain original candidate.protocol) pool) :=
  match same : pool with
  | [] => none
  | head :: tail =>
      let result := scan model domain original reference head tail
      some ⟨result.policy,by
        rcases result.lineage with same | inside
        · simpa only [same] using (List.mem_cons_self : head ∈ head::tail)
        · exact List.mem_cons_of_mem _ inside,by
        intro other inside
        rcases List.mem_cons.mp inside with same | inside
        · subst other;exact cannot_improve_seed model domain original reference result
        · exact result.maximal other inside⟩

theorem choose_none_iff_empty (pool : List (Selection.Candidate model domain original reference)) :
    choose model domain original reference pool = none ↔ pool = [] := by
  unfold choose
  split <;> simp_all

/-- Same original Rule family and full relation, evaluated through its proved
    multiset order and same-occurrence quiet equalities. -/
def compile : Selection.Outcome model domain original reference :=
  match result : choose model domain original reference (Selection.candidates model domain original reference) with
  | some choice => .selected choice
  | none => .blocked (fun protocol =>
      match Distributed.inspect (Selection.holds model domain original reference protocol) (Replanning.rows model domain) with
      | .rejected row original broken => ⟨row,original,broken⟩
      | .accepted all => False.elim (by
          obtain ⟨candidate,inside,_⟩ := Selection.every_accepted_protocol_is_generated model domain original reference protocol all
          rw [choose_none_iff_empty] at result
          simp only [result,List.not_mem_nil] at inside))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Review
