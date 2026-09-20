import Batteries.Data.List.Basic

/-!
# Rooted accounted unfolding

An occurrence is a rooted finite exposure with source-generated branches.
This is the one-constructor kernel beneath arithmetic, homological and
evaluation readouts.  Parallel and dependent branching, frontier/cofiber,
finite observation, relation, cost and evaluation are derived operations;
none is a second source constructor.

The kernel stores no completed future.  `advance` exposes one further finite
patch at every open frontier, preserves the prior roots in the trace and has
one associative flattening law.  Frontier is calculated from the exposure,
not stored as a field.  A readout is an ordinary fold of the sole occurrence
constructor, so no independent receipt schema is needed.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot

universe u v

mutual

/-- One actual occurrence, written as a rooted finite exposure. -/
inductive RootedAccountedUnfolding (Root : Type u) : Type u
  | occur (root : Root) (branches : AccountedBranches Root)

/-- Structural branch storage for the single occurrence constructor.  It has
no arithmetic or domain semantics of its own. -/
inductive AccountedBranches (Root : Type u) : Type u
  | nil
  | cons (head : RootedAccountedUnfolding Root)
      (tail : AccountedBranches Root)

end


namespace AccountedList

theorem congrArgTwo
    {Left : Sort u} {Right : Sort v} {Target : Sort _}
    (operation : Left → Right → Target)
    {left₁ left₂ : Left} {right₁ right₂ : Right}
    (left_eq : left₁ = left₂) (right_eq : right₁ = right₂) :
    operation left₁ right₁ = operation left₂ right₂ := by
  cases left_eq
  cases right_eq
  rfl

/-- Axiom-free local list associativity used by the constructive core. -/
theorem append_assoc {Alpha : Type u} :
    (left middle right : List Alpha) →
      (left ++ middle) ++ right = left ++ (middle ++ right)
  | [], _, _ => rfl
  | head :: tail, middle, right =>
      congrArg (List.cons head) (append_assoc tail middle right)

theorem append_nil {Alpha : Type u} :
    (items : List Alpha) → items ++ [] = items
  | [] => rfl
  | head :: tail => congrArg (List.cons head) (append_nil tail)

/-- Axiom-free distribution of finite dependent branching over siblings. -/
theorem flatMap_append {Alpha : Type u} {Beta : Type v}
    (transform : Alpha → List Beta) :
    (left right : List Alpha) →
      (left ++ right).flatMap transform =
        left.flatMap transform ++ right.flatMap transform
  | [], _ => rfl
  | head :: tail, right =>
      calc
        transform head ++ (tail ++ right).flatMap transform =
            transform head ++
              (tail.flatMap transform ++ right.flatMap transform) :=
          congrArg (fun suffix => transform head ++ suffix)
            (flatMap_append transform tail right)
        _ = (transform head ++ tail.flatMap transform) ++
              right.flatMap transform :=
          (append_assoc (transform head) (tail.flatMap transform)
            (right.flatMap transform)).symm

theorem append_ne_nil_of_left_ne_nil {Alpha : Type u}
    {left right : List Alpha} (left_ne : left ≠ []) :
    left ++ right ≠ [] := by
  cases left with
  | nil => exact False.elim (left_ne rfl)
  | cons head tail =>
      intro impossible
      cases impossible

theorem length_append {Alpha : Type u} :
    (left right : List Alpha) →
      (left ++ right).length = left.length + right.length
  | [], right => (Nat.zero_add right.length).symm
  | _head :: tail, right =>
      (congrArg Nat.succ (length_append tail right)).trans
        (Nat.succ_add tail.length right.length).symm

theorem length_flatMap_const
    {Alpha : Type u} {Beta : Type v}
    (values : List Beta) :
    (items : List Alpha) →
      (items.flatMap (fun _ => values)).length =
        items.length * values.length
  | [] => (Nat.zero_mul values.length).symm
  | _head :: tail => by
      calc
        (values ++ tail.flatMap (fun _ => values)).length =
            values.length +
              (tail.flatMap (fun _ => values)).length :=
          length_append values (tail.flatMap (fun _ => values))
        _ = values.length + tail.length * values.length :=
          congrArg (fun suffix => values.length + suffix)
            (length_flatMap_const values tail)
        _ = Nat.succ tail.length * values.length := by
          rw [Nat.succ_mul, Nat.add_comm]

end AccountedList


namespace AccountedBranches

def singleton {Root : Type u}
    (head : RootedAccountedUnfolding Root) : AccountedBranches Root :=
  .cons head .nil

def append {Root : Type u} :
    AccountedBranches Root → AccountedBranches Root → AccountedBranches Root
  | .nil, right => right
  | .cons head tail, right => .cons head (append tail right)

@[simp] theorem nil_append {Root : Type u}
    (branches : AccountedBranches Root) :
    append .nil branches = branches :=
  rfl

@[simp] theorem append_nil {Root : Type u}
    (branches : AccountedBranches Root) :
    append branches .nil = branches := by
  cases branches with
  | nil => rfl
  | cons head tail =>
      change AccountedBranches.cons head (append tail .nil) =
        AccountedBranches.cons head tail
      rw [append_nil tail]

theorem append_assoc {Root : Type u}
    (left middle right : AccountedBranches Root) :
    append (append left middle) right = append left (append middle right) := by
  cases left with
  | nil => rfl
  | cons head tail =>
      change AccountedBranches.cons head (append (append tail middle) right) =
        AccountedBranches.cons head (append tail (append middle right))
      rw [append_assoc tail middle right]

end AccountedBranches


namespace RootedAccountedUnfolding

def root {Root : Type u} : RootedAccountedUnfolding Root → Root
  | .occur root _ => root

/-- Zero-step finite observation of a root. -/
def zero {Root : Type u} (root : Root) : RootedAccountedUnfolding Root :=
  .occur root .nil

def branches {Root : Type u} :
    RootedAccountedUnfolding Root → AccountedBranches Root
  | .occur _ branches => branches

mutual

/-- Functorial relabelling of one exact occurrence tree.  This is a derived
operation on the sole constructor: it preserves every branch and changes
only the payload carried at each occurrence. -/
def map {Root : Type u} {Target : Type v} (transform : Root → Target) :
    RootedAccountedUnfolding Root → RootedAccountedUnfolding Target
  | .occur root branches =>
      .occur (transform root) (mapBranches transform branches)

def mapBranches {Root : Type u} {Target : Type v}
    (transform : Root → Target) :
    AccountedBranches Root → AccountedBranches Target
  | .nil => .nil
  | .cons head tail =>
      .cons (map transform head) (mapBranches transform tail)

end

@[simp] theorem root_map {Root : Type u} {Target : Type v}
    (transform : Root → Target)
    (occurrence : RootedAccountedUnfolding Root) :
    (occurrence.map transform).root = transform occurrence.root := by
  cases occurrence
  rfl

@[simp] theorem map_zero {Root : Type u} {Target : Type v}
    (transform : Root → Target) (root : Root) :
    (zero root).map transform = zero (transform root) :=
  rfl

mutual

/-- Relabelling an occurrence twice is the same exact branch-preserving
relabelling as the composite transform. -/
theorem map_map {Root : Type u} {Middle : Type v} {Target : Type _}
    (second : Middle → Target) (first : Root → Middle)
    (occurrence : RootedAccountedUnfolding Root) :
    (occurrence.map first).map second =
      occurrence.map (second ∘ first) := by
  cases occurrence with
  | occur root branches =>
      change RootedAccountedUnfolding.occur _
          (mapBranches second (mapBranches first branches)) =
        RootedAccountedUnfolding.occur _
          (mapBranches (second ∘ first) branches)
      rw [mapBranches_map_map]
      rfl

/-- Branch form of `map_map`. -/
theorem mapBranches_map_map
    {Root : Type u} {Middle : Type v} {Target : Type _}
    (second : Middle → Target) (first : Root → Middle)
    (branches : AccountedBranches Root) :
    mapBranches second (mapBranches first branches) =
      mapBranches (second ∘ first) branches := by
  cases branches with
  | nil => rfl
  | cons head tail =>
      change AccountedBranches.cons ((head.map first).map second)
          (mapBranches second (mapBranches first tail)) =
        AccountedBranches.cons (head.map (second ∘ first))
          (mapBranches (second ∘ first) tail)
      rw [map_map, mapBranches_map_map]

end

mutual

/-- Identity relabelling preserves the complete occurrence tree. -/
theorem map_id {Root : Type u}
    (occurrence : RootedAccountedUnfolding Root) :
    occurrence.map id = occurrence := by
  cases occurrence with
  | occur root branches =>
      change RootedAccountedUnfolding.occur root
          (mapBranches id branches) =
        RootedAccountedUnfolding.occur root branches
      rw [mapBranches_id]

/-- Branch form of `map_id`. -/
theorem mapBranches_id {Root : Type u}
    (branches : AccountedBranches Root) :
    mapBranches id branches = branches := by
  cases branches with
  | nil => rfl
  | cons head tail =>
      change AccountedBranches.cons (head.map id)
          (mapBranches id tail) = AccountedBranches.cons head tail
      rw [map_id, mapBranches_id]

end

mutual

private def frontierImpl {Root : Type u} :
    RootedAccountedUnfolding Root → List Root
  | .occur root .nil => [root]
  | .occur _ branches@(.cons _ _) => frontierBranchesImpl branches

private def frontierBranchesImpl {Root : Type u} :
    AccountedBranches Root → List Root
  | .nil => []
  | .cons head tail => frontierImpl head ++ frontierBranchesImpl tail

end

/-- Unresolved leaves of the finite exposure. -/
@[implemented_by frontierImpl]
noncomputable def frontier {Root : Type u} :
    RootedAccountedUnfolding Root → List Root :=
  RootedAccountedUnfolding.rec
    (motive_1 := fun _ => List Root)
    (motive_2 := fun _ => List Root)
    (fun root branches branchFrontier =>
      match branches with
      | .nil => [root]
      | .cons _ _ => branchFrontier)
    []
    (fun _head _tail headFrontier tailFrontier =>
      headFrontier ++ tailFrontier)

@[implemented_by frontierBranchesImpl]
noncomputable def frontierBranches {Root : Type u} :
    AccountedBranches Root → List Root :=
  AccountedBranches.rec
    (motive_1 := fun _ => List Root)
    (motive_2 := fun _ => List Root)
    (fun root branches branchFrontier =>
      match branches with
      | .nil => [root]
      | .cons _ _ => branchFrontier)
    []
    (fun _head _tail headFrontier tailFrontier =>
      headFrontier ++ tailFrontier)


/-- An unresolved frontier cannot silently disappear from a finite
occurrence.  A genuinely settled empty local face must remain represented by
its rooted occurrence rather than by erasing that occurrence. -/
theorem frontier_ne_nil {Root : Type u}
    (occurrence : RootedAccountedUnfolding Root) :
    occurrence.frontier ≠ [] :=
  RootedAccountedUnfolding.rec
    (motive_1 := fun occurrence => occurrence.frontier ≠ [])
    (motive_2 := fun branches =>
      branches = .nil ∨ frontierBranches branches ≠ [])
    (fun origin branches branchResult => by
      cases branches with
      | nil =>
          intro impossible
          cases impossible
      | cons head tail =>
          cases branchResult with
          | inl impossible => cases impossible
          | inr nonempty => exact nonempty)
    (Or.inl rfl)
    (fun _head _tail headNonempty _tailResult =>
      Or.inr (AccountedList.append_ne_nil_of_left_ne_nil headNonempty))
    occurrence

mutual

private def traceImpl {Root : Type u} :
    RootedAccountedUnfolding Root → List Root
  | .occur root branches => root :: traceBranchesImpl branches

private def traceBranchesImpl {Root : Type u} :
    AccountedBranches Root → List Root
  | .nil => []
  | .cons head tail => traceImpl head ++ traceBranchesImpl tail

end

/-- Complete finite provenance trace. -/
@[implemented_by traceImpl]
noncomputable def trace {Root : Type u} :
    RootedAccountedUnfolding Root → List Root :=
  RootedAccountedUnfolding.rec
    (motive_1 := fun _ => List Root)
    (motive_2 := fun _ => List Root)
    (fun root _branches branchTrace => root :: branchTrace)
    []
    (fun _head _tail headTrace tailTrace => headTrace ++ tailTrace)

@[implemented_by traceBranchesImpl]
noncomputable def traceBranches {Root : Type u} :
    AccountedBranches Root → List Root :=
  AccountedBranches.rec
    (motive_1 := fun _ => List Root)
    (motive_2 := fun _ => List Root)
    (fun root _branches branchTrace => root :: branchTrace)
    []
    (fun _head _tail headTrace tailTrace => headTrace ++ tailTrace)


theorem root_mem_trace {Root : Type u}
    (occurrence : RootedAccountedUnfolding Root) :
    occurrence.root ∈ occurrence.trace := by
  cases occurrence with
  | occur origin childBranches =>
      change origin ∈ origin :: traceBranches childBranches
      exact List.mem_cons_self

mutual

private def advanceImpl {Root : Type u}
    (next : Root → RootedAccountedUnfolding Root) :
    RootedAccountedUnfolding Root → RootedAccountedUnfolding Root
  | .occur root .nil =>
      .occur root (.singleton (next root))
  | .occur root branches@(.cons _ _) =>
      .occur root (advanceBranchesImpl next branches)

private def advanceBranchesImpl {Root : Type u}
    (next : Root → RootedAccountedUnfolding Root) :
    AccountedBranches Root → AccountedBranches Root
  | .nil => .nil
  | .cons head tail =>
      .cons (advanceImpl next head) (advanceBranchesImpl next tail)

end

/-- One further source-generated exposure at every open frontier.  The old
leaf remains as the parent of the new patch, so continuation cannot replace
its provenance. -/
@[implemented_by advanceImpl]
noncomputable def advance {Root : Type u}
    (next : Root → RootedAccountedUnfolding Root) :
    RootedAccountedUnfolding Root → RootedAccountedUnfolding Root :=
  RootedAccountedUnfolding.rec
    (motive_1 := fun _ => RootedAccountedUnfolding Root)
    (motive_2 := fun _ => AccountedBranches Root)
    (fun root branches advancedBranches =>
      match branches with
      | .nil => .occur root (.singleton (next root))
      | .cons _ _ => .occur root advancedBranches)
    .nil
    (fun _head _tail advancedHead advancedTail =>
      .cons advancedHead advancedTail)

@[implemented_by advanceBranchesImpl]
noncomputable def advanceBranches {Root : Type u}
    (next : Root → RootedAccountedUnfolding Root) :
    AccountedBranches Root → AccountedBranches Root :=
  AccountedBranches.rec
    (motive_1 := fun _ => RootedAccountedUnfolding Root)
    (motive_2 := fun _ => AccountedBranches Root)
    (fun root branches advancedBranches =>
      match branches with
      | .nil => .occur root (.singleton (next root))
      | .cons _ _ => .occur root advancedBranches)
    .nil
    (fun _head _tail advancedHead advancedTail =>
      .cons advancedHead advancedTail)


@[simp] theorem root_advance {Root : Type u}
    (next : Root → RootedAccountedUnfolding Root)
    (occurrence : RootedAccountedUnfolding Root) :
    (occurrence.advance next).root = occurrence.root := by
  cases occurrence with
  | occur origin childBranches =>
      cases childBranches <;> rfl

/-- The new frontier is exactly the old frontier's generated continuation;
no open branch is silently dropped. -/
theorem frontier_advance {Root : Type u}
    (next : Root → RootedAccountedUnfolding Root)
    (occurrence : RootedAccountedUnfolding Root) :
    (occurrence.advance next).frontier =
      occurrence.frontier.flatMap (fun root => (next root).frontier) :=
  RootedAccountedUnfolding.rec
    (motive_1 := fun occurrence =>
      (occurrence.advance next).frontier =
        occurrence.frontier.flatMap (fun root => (next root).frontier))
    (motive_2 := fun branches =>
      frontierBranches (advanceBranches next branches) =
        (frontierBranches branches).flatMap
          (fun root => (next root).frontier))
    (fun _origin branches branchResult => by
      cases branches with
      | nil => rfl
      | cons _head _tail => exact branchResult)
    rfl
    (fun head tail headResult tailResult =>
      calc
        (head.advance next).frontier ++
            frontierBranches (advanceBranches next tail) =
          head.frontier.flatMap (fun root => (next root).frontier) ++
            (frontierBranches tail).flatMap
              (fun root => (next root).frontier) := by
                exact AccountedList.congrArgTwo (· ++ ·)
                  headResult tailResult
        _ = (head.frontier ++ frontierBranches tail).flatMap
              (fun root => (next root).frontier) :=
          (AccountedList.flatMap_append
            (fun root => (next root).frontier)
            head.frontier (frontierBranches tail)).symm)
    occurrence

theorem frontierBranches_advance {Root : Type u}
    (next : Root → RootedAccountedUnfolding Root)
    (branches : AccountedBranches Root) :
    frontierBranches (advanceBranches next branches) =
      (frontierBranches branches).flatMap
        (fun root => (next root).frontier) :=
  AccountedBranches.rec
    (motive_1 := fun occurrence =>
      (occurrence.advance next).frontier =
        occurrence.frontier.flatMap (fun root => (next root).frontier))
    (motive_2 := fun branches =>
      frontierBranches (advanceBranches next branches) =
        (frontierBranches branches).flatMap
          (fun root => (next root).frontier))
    (fun _origin childBranches branchResult => by
      cases childBranches with
      | nil => rfl
      | cons _head _tail => exact branchResult)
    rfl
    (fun head tail headResult tailResult =>
      calc
        (head.advance next).frontier ++
            frontierBranches (advanceBranches next tail) =
          head.frontier.flatMap (fun root => (next root).frontier) ++
            (frontierBranches tail).flatMap
              (fun root => (next root).frontier) := by
                exact AccountedList.congrArgTwo (· ++ ·)
                  headResult tailResult
        _ = (head.frontier ++ frontierBranches tail).flatMap
              (fun root => (next root).frontier) :=
          (AccountedList.flatMap_append
            (fun root => (next root).frontier)
            head.frontier (frontierBranches tail)).symm)
    branches


/-- Consecutive finite unfoldings have one canonical flattening. -/
theorem advance_assoc {Root : Type u}
    (first second : Root → RootedAccountedUnfolding Root)
    (occurrence : RootedAccountedUnfolding Root) :
    (occurrence.advance first).advance second =
      occurrence.advance (fun root => (first root).advance second) :=
  RootedAccountedUnfolding.rec
    (motive_1 := fun occurrence =>
      (occurrence.advance first).advance second =
        occurrence.advance (fun root => (first root).advance second))
    (motive_2 := fun branches =>
      advanceBranches second (advanceBranches first branches) =
        advanceBranches (fun root => (first root).advance second) branches)
    (fun root branches branchResult => by
      cases branches with
      | nil => rfl
      | cons _head _tail =>
          exact congrArg (RootedAccountedUnfolding.occur root) branchResult)
    rfl
    (fun _head _tail headResult tailResult =>
      AccountedList.congrArgTwo AccountedBranches.cons
        headResult tailResult)
    occurrence

theorem advanceBranches_assoc {Root : Type u}
    (first second : Root → RootedAccountedUnfolding Root)
    (branches : AccountedBranches Root) :
    advanceBranches second (advanceBranches first branches) =
      advanceBranches (fun root => (first root).advance second) branches :=
  AccountedBranches.rec
    (motive_1 := fun occurrence =>
      (occurrence.advance first).advance second =
        occurrence.advance (fun root => (first root).advance second))
    (motive_2 := fun branches =>
      advanceBranches second (advanceBranches first branches) =
        advanceBranches (fun root => (first root).advance second) branches)
    (fun root childBranches branchResult => by
      cases childBranches with
      | nil => rfl
      | cons _head _tail =>
          exact congrArg (RootedAccountedUnfolding.occur root) branchResult)
    rfl
    (fun _head _tail headResult tailResult =>
      AccountedList.congrArgTwo AccountedBranches.cons
        headResult tailResult)
    branches


/-- Sibling branching is the derived parallel position. -/
def parallelAt {Root : Type u}
    (anchor : Root)
    (left right : RootedAccountedUnfolding Root) :
    RootedAccountedUnfolding Root :=
  .occur anchor (AccountedBranches.cons left
    (AccountedBranches.singleton right))

/-- Dependent branching is the derived joint position. -/
def jointAt {Root : Type u}
    (left right : RootedAccountedUnfolding Root) :
    RootedAccountedUnfolding Root :=
  left.advance (fun _ => right)

@[simp] theorem frontier_parallelAt {Root : Type u}
    (anchor : Root)
    (left right : RootedAccountedUnfolding Root) :
    (parallelAt anchor left right).frontier =
      left.frontier ++ right.frontier := by
  change left.frontier ++ (right.frontier ++ []) =
    left.frontier ++ right.frontier
  rw [AccountedList.append_nil]

theorem frontier_jointAt {Root : Type u}
    (left right : RootedAccountedUnfolding Root) :
    (jointAt left right).frontier =
      left.frontier.flatMap (fun _ => right.frontier) :=
  frontier_advance (fun _ => right) left

theorem length_flatMap_const
    {Alpha : Type u} {Beta : Type v}
    (items : List Alpha) (values : List Beta) :
    (items.flatMap (fun _ => values)).length = items.length * values.length :=
  AccountedList.length_flatMap_const values items

/-- Cofiber/frontier is a readout of the occurrence, not a constructor. -/
def cofiber {Root : Type u}
    (occurrence : RootedAccountedUnfolding Root) : List Root :=
  occurrence.frontier

/-- Relation profile is reconstructed from the same finite trace. -/
def reaches {Root : Type u}
    [DecidableEq Root]
    (source : Root) (occurrence : RootedAccountedUnfolding Root) : Prop :=
  source ∈ occurrence.trace

/-- Cofinal observation is pointwise finite generation.  No completed table
of future exposures is stored in an occurrence. -/
def observe {Root : Type u}
    (next : Root → RootedAccountedUnfolding Root)
    (root : Root) : Nat → RootedAccountedUnfolding Root
  | 0 => zero root
  | fuel + 1 => (observe next root fuel).advance next

@[simp] theorem observe_zero {Root : Type u}
    (next : Root → RootedAccountedUnfolding Root) (root : Root) :
    observe next root 0 = zero root :=
  rfl

@[simp] theorem observe_succ {Root : Type u}
    (next : Root → RootedAccountedUnfolding Root)
    (root : Root) (fuel : Nat) :
    observe next root (fuel + 1) = (observe next root fuel).advance next :=
  rfl

mutual

/-- The only evaluation principle: fold the one occurrence constructor. -/
def fold {Root : Type u} {Carrier : Type v}
    (atOccurrence : Root → List Carrier → Carrier) :
    RootedAccountedUnfolding Root → Carrier
  | .occur root branches =>
      atOccurrence root (foldBranches atOccurrence branches)

def foldBranches {Root : Type u} {Carrier : Type v}
    (atOccurrence : Root → List Carrier → Carrier) :
    AccountedBranches Root → List Carrier
  | .nil => []
  | .cons head tail => head.fold atOccurrence :: foldBranches atOccurrence tail

end


def candidateValues {Root : Type u} {Carrier : Type v}
    (candidate : RootedAccountedUnfolding Root → Carrier) :
    AccountedBranches Root → List Carrier
  | .nil => []
  | .cons head tail => candidate head :: candidateValues candidate tail

mutual

/-- Any evaluator respecting the sole constructor factors through `fold`.
The fold itself is the auditable readout; no receipt record is primitive. -/
theorem fold_unique {Root : Type u} {Carrier : Type v}
    (atOccurrence : Root → List Carrier → Carrier)
    (candidate : RootedAccountedUnfolding Root → Carrier)
    (commutes : ∀ (origin : Root) (childBranches : AccountedBranches Root),
      candidate (RootedAccountedUnfolding.occur origin childBranches) =
        atOccurrence origin (candidateValues candidate childBranches))
    (occurrence : RootedAccountedUnfolding Root) :
    candidate occurrence = occurrence.fold atOccurrence := by
  cases occurrence with
  | occur origin childBranches =>
      calc
        candidate (RootedAccountedUnfolding.occur origin childBranches) =
            atOccurrence origin (candidateValues candidate childBranches) :=
          commutes origin childBranches
        _ = atOccurrence origin (foldBranches atOccurrence childBranches) :=
          congrArg (atOccurrence origin)
            (candidateValues_eq_fold atOccurrence candidate commutes childBranches)
        _ = fold atOccurrence
            (RootedAccountedUnfolding.occur origin childBranches) := rfl

theorem candidateValues_eq_fold {Root : Type u} {Carrier : Type v}
    (atOccurrence : Root → List Carrier → Carrier)
    (candidate : RootedAccountedUnfolding Root → Carrier)
    (commutes : ∀ (origin : Root) (childBranches : AccountedBranches Root),
      candidate (RootedAccountedUnfolding.occur origin childBranches) =
        atOccurrence origin (candidateValues candidate childBranches))
    (branches : AccountedBranches Root) :
    candidateValues candidate branches = foldBranches atOccurrence branches := by
  cases branches with
  | nil => rfl
  | cons head tail =>
      change
        candidate head :: candidateValues candidate tail =
          fold atOccurrence head :: foldBranches atOccurrence tail
      rw [fold_unique atOccurrence candidate commutes head,
        candidateValues_eq_fold atOccurrence candidate commutes tail]

end


/-- Arithmetic cardinality is one downstream shadow of the open frontier. -/
def cardinalShadow {Root : Type u}
    (occurrence : RootedAccountedUnfolding Root) : Nat :=
  occurrence.frontier.length

@[simp] theorem cardinalShadow_parallelAt {Root : Type u}
    (anchor : Root)
    (left right : RootedAccountedUnfolding Root) :
    cardinalShadow (parallelAt anchor left right) =
      cardinalShadow left + cardinalShadow right := by
  simp [cardinalShadow]

theorem cardinalShadow_jointAt {Root : Type u}
    (left right : RootedAccountedUnfolding Root) :
    cardinalShadow (jointAt left right) =
      cardinalShadow left * cardinalShadow right := by
  rw [cardinalShadow, frontier_jointAt]
  exact length_flatMap_const left.frontier right.frontier

end RootedAccountedUnfolding
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
