import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Counted.Runtime

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32768

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

namespace Selection.Review
variable (domain : List (Cursor model.source.code)) (fallback : Rule model.source.code)
  (pool : List (Program model.source.code))

/-- The native anchor basis is exactly the original due multiset order on pool members. -/
def noWorse (first second : Program model.source.code) : Prop :=
  ∀ world ∈ Replanning.points model domain,
    ∀ table ∈ Finite.tables world.val fallback pool,
      let current := Finite.tableEvaluation model world.val fallback pool first table
      let prior := Finite.tableEvaluation model world.val fallback pool second table
      (Authority.Trace.Lawful.inventory current.native).due.Subperm
        (Authority.Trace.Lawful.inventory prior.native).due ∧
      ∀ axis ∈ economicAxes world.val.source world.val.cut,current.value axis ≤ prior.value axis

instance (first second : Program model.source.code) : Decidable (noWorse model domain fallback pool first second) := by
  unfold noWorse
  infer_instance

theorem noWorse_iff (first second : Program model.source.code) (member : second ∈ pool) :
    noWorse model domain fallback pool first second ↔
      Distributed.NoWorse (Selection.axes model domain fallback pool)
        (Selection.benefit model domain fallback pool) first second := by
  constructor
  · intro all coordinate _
    cases coordinate with
    | economic world table axis =>
      exact (all world (Replanning.every_point_is_source_generated model domain world) table.val table.property).2 axis.val axis.property
    | native world table anchor =>
      have due := (all world (Replanning.every_point_is_source_generated model domain world) table.val table.property).1
      change (Authority.Trace.Lawful.inventory (Selection.readTable model domain fallback pool world first table).native).due.Subperm
        (Authority.Trace.Lawful.inventory (Selection.readTable model domain fallback pool world second table).native).due at due
      change (if _ then (0 : ℚ) else 1) ≤ (if _ then 0 else 1)
      by_cases old : (Authority.Trace.Lawful.inventory (Selection.readTable model domain fallback pool world second table).native).due.Subperm
          (Authority.Trace.Lawful.inventory (Selection.readTable model domain fallback pool world anchor table).native).due
      · have current := due.trans old
        simp only [if_pos old,if_pos current,le_refl]
      · split <;> simp_all
  · intro all world _ table inside
    let sourceTable : Selection.TableAt model domain fallback pool world := ⟨table,inside⟩
    have nativeInside : Selection.Axis.native world sourceTable second ∈ Selection.axes model domain fallback pool :=
      List.mem_flatMap.mpr ⟨world,List.mem_attach _ _,List.mem_flatMap.mpr
        ⟨sourceTable,List.mem_attach _ _,List.mem_append_right _ (List.mem_map.mpr ⟨second,member,rfl⟩)⟩⟩
    have native := all _ nativeInside
    have reflexive : (Authority.Trace.Lawful.inventory (Selection.readTable model domain fallback pool world second sourceTable).native).due.Subperm
        (Authority.Trace.Lawful.inventory (Selection.readTable model domain fallback pool world second sourceTable).native).due := List.Subperm.refl _
    change (if _ then (0 : ℚ) else 1) ≤ (if _ then 0 else 1) at native
    rw [if_pos reflexive] at native
    have due : (Authority.Trace.Lawful.inventory (Selection.readTable model domain fallback pool world first sourceTable).native).due.Subperm
        (Authority.Trace.Lawful.inventory (Selection.readTable model domain fallback pool world second sourceTable).native).due := by
      split at native
      · assumption
      · norm_num at native
    refine ⟨due,?_⟩
    intro axis generated
    exact all (.economic world sourceTable ⟨axis,generated⟩)
      (List.mem_flatMap.mpr ⟨world,List.mem_attach _ _,List.mem_flatMap.mpr
        ⟨sourceTable,List.mem_attach _ _,List.mem_append_left _ (List.mem_map.mpr ⟨⟨axis,generated⟩,List.mem_attach _ _,rfl⟩)⟩⟩)

def improves (first second : Program model.source.code) : Prop :=
  noWorse model domain fallback pool second first ∧ ¬ noWorse model domain fallback pool first second

instance (first second : Program model.source.code) : Decidable (improves model domain fallback pool first second) := by
  unfold improves
  infer_instance

theorem improves_iff (first second : Program model.source.code) (a : first ∈ pool) (b : second ∈ pool) :
    improves model domain fallback pool first second ↔
      Distributed.Improves (Selection.axes model domain fallback pool) (Selection.benefit model domain fallback pool) first second := by
  simp only [improves,Distributed.Improves,noWorse_iff model domain fallback pool second first a,
    noWorse_iff model domain fallback pool first second b]

/-- This checker receives an original program, never the planner's maximality witness. -/
def verify (reference proposed : Program model.source.code) : Bool :=
  decide (Selection.acceptable model domain fallback pool reference proposed ∧
    ∀ other ∈ pool,Selection.acceptable model domain fallback pool reference other →
      ¬ improves model domain fallback pool proposed other)

theorem verify_exact (reference proposed : Program model.source.code) (member : proposed ∈ pool) :
    verify model domain fallback pool reference proposed = Selection.verify model domain fallback pool reference proposed := by
  apply Bool.eq_iff_iff.mpr
  simp only [verify,Selection.verify,decide_eq_true_eq]
  constructor <;> rintro ⟨accepted,all⟩ <;> refine ⟨accepted,?_⟩
  · intro other inside valid better
    exact all other inside valid ((improves_iff model domain fallback pool proposed other member inside).mpr better)
  · intro other inside valid better
    exact all other inside valid ((improves_iff model domain fallback pool proposed other member inside).mp better)

end Selection.Review

namespace Counted.Installation.Chain
variable (fallback : Rule model.source.code) (basis : Counted.Basis model.source.code)

def independentReview : {fuel : Nat} → {domain : List (Cursor model.source.code)} →
    {reference : Program model.source.code} → Chain model fallback basis fuel domain reference → Bool
  | _,_,_,.exhausted => true
  | _,domain,reference,.blocked rejected _ => Selection.review model domain fallback
      (Pool model fallback basis domain reference) reference (.blocked rejected)
  | _,domain,reference,.selected choice _ tail =>
      Selection.Review.verify model domain fallback (Pool model fallback basis domain reference) reference choice.policy.protocol &&
        independentReview tail

theorem independentReview_exact {fuel : Nat} {domain : List (Cursor model.source.code)}
    {reference : Program model.source.code} (chain : Chain model fallback basis fuel domain reference) :
    chain.independentReview = chain.review := by
  induction chain with
  | exhausted => rfl
  | blocked => rfl
  | selected choice compiled tail ih =>
    simp only [independentReview,review,Selection.review,
      Selection.Review.verify_exact model _ fallback _ _ choice.policy.protocol choice.policy.generated,ih]

theorem every_cut_is_independently_reviewable {fuel : Nat} {domain : List (Cursor model.source.code)}
    {reference : Program model.source.code} (chain : Chain model fallback basis fuel domain reference) :
    chain.independentReview = true := by
  rw [independentReview_exact]
  exact chain.every_compiled_step_is_independently_reviewable

end Counted.Installation.Chain
end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme
