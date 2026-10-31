import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.BoardKernel
import Mathlib.Data.Finset.Dedup
import Lean.Elab.Tactic.Omega

/-!
# Executable component correctness

The finite worklist is the execution engine used by Go rules.  This module
connects its minimal invariants back to the orthogonal-board specification:
the seed survives, every generated component member has the seed's board
value, and the explicit at-most-four neighbour list is exactly orthogonal
adjacency.  It introduces no group identifier or lineage registry.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go

theorem mem_componentWorklist_of_mem_seen {n : Nat} {board : Board n}
    {value : Option Polarity} {point : Point n} :
    ∀ (fuel : Nat) (pending seen : List (Point n)),
      point ∈ seen →
        point ∈ componentWorklist board value fuel pending seen := by
  intro fuel
  induction fuel with
  | zero =>
      intro pending seen member
      exact member
  | succ fuel ih =>
      intro pending seen member
      cases pending with
      | nil => exact member
      | cons current pending =>
          change point ∈ componentWorklist board value fuel
            (pending ++
              (adjacentPointList current).filter
                (fun candidate => board candidate = value ∧ candidate ∉ seen))
            (seen ++
              (adjacentPointList current).filter
                (fun candidate => board candidate = value ∧ candidate ∉ seen))
          exact ih _ _ (List.mem_append_left _ member)

/-- The executable flood never drops its seed. -/
theorem point_mem_componentAt {n : Nat} (board : Board n) (point : Point n) :
    point ∈ componentAt board point := by
  unfold componentAt
  simp only [List.mem_toFinset]
  exact mem_componentWorklist_of_mem_seen _ _ _ (by simp)

theorem componentWorklist_value {n : Nat} {board : Board n}
    {value : Option Polarity} :
    ∀ (fuel : Nat) (pending seen : List (Point n)),
      (∀ point, point ∈ seen → board point = value) →
      ∀ point, point ∈ componentWorklist board value fuel pending seen →
        board point = value := by
  intro fuel
  induction fuel with
  | zero =>
      intro pending seen seen_value point member
      exact seen_value point member
  | succ fuel ih =>
      intro pending seen seen_value point member
      cases pending with
      | nil => exact seen_value point member
      | cons current pending =>
          apply ih
            (pending ++
              (adjacentPointList current).filter
                (fun candidate => board candidate = value ∧ candidate ∉ seen))
            (seen ++
              (adjacentPointList current).filter
                (fun candidate => board candidate = value ∧ candidate ∉ seen))
            (fun candidate candidate_member => ?_)
            point member
          rcases List.mem_append.mp candidate_member with old_member | fresh_member
          · exact seen_value candidate old_member
          · exact (of_decide_eq_true (List.mem_filter.mp fresh_member).2).1

/-- Every generated component member has the seed's exact board value. -/
theorem componentAt_member_value {n : Nat} {board : Board n}
    {seed point : Point n} (member : point ∈ componentAt board seed) :
    board point = board seed := by
  unfold componentAt at member
  have list_member :
      point ∈ componentWorklist board (board seed) (Fintype.card (Point n))
        [seed] [seed] := by
    simpa using member
  exact componentWorklist_value _ _ _
    (fun candidate candidate_member => by
      simp only [List.mem_singleton] at candidate_member
      subst candidate
      rfl)
    point list_member

/-- An occupied seed belongs to its generated snapshot group. -/
theorem occupied_point_mem_groupAt {n : Nat} {board : Board n}
    {point : Point n} {colour : Polarity} (occupied : board point = some colour) :
    point ∈ groupAt board point := by
  unfold groupAt
  rw [occupied]
  exact point_mem_componentAt board point

/-- A generated snapshot group cannot silently contain another colour. -/
theorem groupAt_member_colour {n : Nat} {board : Board n}
    {seed point : Point n} {colour : Polarity}
    (occupied : board seed = some colour)
    (member : point ∈ groupAt board seed) :
    board point = some colour := by
  unfold groupAt at member
  rw [occupied] at member
  exact (componentAt_member_value member).trans occupied

theorem mem_axisPrevious_toList_iff {n : Nat} {source target : Fin n} :
    target ∈ (axisPrevious? source).toList ↔
      0 < source.val ∧ target.val + 1 = source.val := by
  unfold axisPrevious?
  split
  · simp_all [Fin.ext_iff]
    omega
  · simp_all

theorem mem_axisNext_toList_iff {n : Nat} {source target : Fin n} :
    target ∈ (axisNext? source).toList ↔
      source.val + 1 < n ∧ target.val = source.val + 1 := by
  unfold axisNext?
  split
  · simp_all [Fin.ext_iff]
  · simp_all

theorem nat_dist_eq_one_iff (left right : Nat) :
    Nat.dist left right = 1 ↔ left + 1 = right ∨ right + 1 = left := by
  unfold Nat.dist
  omega

/-- The executable neighbour set is exactly the orthogonal-grid relation. -/
theorem mem_adjacentPoints_iff_orthogonallyAdjacent {n : Nat}
    {source target : Point n} :
    target ∈ adjacentPoints source ↔ OrthogonallyAdjacent source target := by
  rcases source with ⟨sourceRow, sourceColumn⟩
  rcases target with ⟨targetRow, targetColumn⟩
  simp only [adjacentPoints, List.mem_toFinset, adjacentPointList,
    List.mem_append, List.mem_map]
  simp only [Prod.mk.injEq]
  have previousRow :
      (∃ row ∈ (axisPrevious? sourceRow).toList,
          row = targetRow ∧ sourceColumn = targetColumn) ↔
        targetRow ∈ (axisPrevious? sourceRow).toList ∧
          sourceColumn = targetColumn := by
    constructor
    · rintro ⟨row, member, rfl, column_eq⟩
      exact ⟨member, column_eq⟩
    · rintro ⟨member, column_eq⟩
      exact ⟨targetRow, member, rfl, column_eq⟩
  have nextRow :
      (∃ row ∈ (axisNext? sourceRow).toList,
          row = targetRow ∧ sourceColumn = targetColumn) ↔
        targetRow ∈ (axisNext? sourceRow).toList ∧
          sourceColumn = targetColumn := by
    constructor
    · rintro ⟨row, member, rfl, column_eq⟩
      exact ⟨member, column_eq⟩
    · rintro ⟨member, column_eq⟩
      exact ⟨targetRow, member, rfl, column_eq⟩
  have previousColumn :
      (∃ column ∈ (axisPrevious? sourceColumn).toList,
          sourceRow = targetRow ∧ column = targetColumn) ↔
        targetColumn ∈ (axisPrevious? sourceColumn).toList ∧
          sourceRow = targetRow := by
    constructor
    · rintro ⟨column, member, row_eq, rfl⟩
      exact ⟨member, row_eq⟩
    · rintro ⟨member, row_eq⟩
      exact ⟨targetColumn, member, row_eq, rfl⟩
  have nextColumn :
      (∃ column ∈ (axisNext? sourceColumn).toList,
          sourceRow = targetRow ∧ column = targetColumn) ↔
        targetColumn ∈ (axisNext? sourceColumn).toList ∧
          sourceRow = targetRow := by
    constructor
    · rintro ⟨column, member, row_eq, rfl⟩
      exact ⟨member, row_eq⟩
    · rintro ⟨member, row_eq⟩
      exact ⟨targetColumn, member, row_eq, rfl⟩
  rw [previousRow, nextRow, previousColumn, nextColumn]
  rw [mem_axisPrevious_toList_iff, mem_axisNext_toList_iff,
    mem_axisPrevious_toList_iff, mem_axisNext_toList_iff]
  simp only [OrthogonallyAdjacent, nat_dist_eq_one_iff, Fin.ext_iff]
  omega

/-! ## Component saturation

The worklist stores every point when it is enqueued.  Its neighbour list is
duplicate-free, and `fuel + seen.length = card + pending.length` is preserved
at every recursive call.  Thus cardinality fuel processes the whole pending
queue, producing the least same-valued adjacency-closed set containing the
seed. -/

theorem adjacentPointList_nodup {n : Nat} (point : Point n) :
    (adjacentPointList point).Nodup := by
  rcases point with ⟨row, column⟩
  simp only [adjacentPointList]
  unfold axisPrevious? axisNext?
  split <;> split <;> split <;> split <;>
    simp_all [Fin.ext_iff] <;> omega

private def componentFresh {n : Nat} (board : Board n)
    (value : Option Polarity) (current : Point n) (seen : List (Point n)) :
    List (Point n) :=
  (adjacentPointList current).filter
    (fun candidate => board candidate = value ∧ candidate ∉ seen)

private theorem mem_componentFresh_iff {n : Nat} {board : Board n}
    {value : Option Polarity} {current candidate : Point n}
    {seen : List (Point n)} :
    candidate ∈ componentFresh board value current seen ↔
      candidate ∈ adjacentPointList current ∧
        board candidate = value ∧ candidate ∉ seen := by
  simp [componentFresh]

private theorem componentFresh_nodup {n : Nat} (board : Board n)
    (value : Option Polarity) (current : Point n) (seen : List (Point n)) :
    (componentFresh board value current seen).Nodup := by
  exact (adjacentPointList_nodup current).filter _

private theorem componentFresh_disjoint_seen {n : Nat} (board : Board n)
    (value : Option Polarity) (current : Point n) (seen : List (Point n)) :
    List.Disjoint seen (componentFresh board value current seen) := by
  rw [List.disjoint_left]
  intro candidate oldMember freshMember
  exact (mem_componentFresh_iff.mp freshMember).2.2 oldMember

private def ComponentProcessedClosed {n : Nat} (board : Board n)
    (value : Option Polarity) (pending seen : List (Point n)) : Prop :=
  ∀ current ∈ seen, current ∉ pending →
    ∀ candidate ∈ adjacentPointList current,
      board candidate = value → candidate ∈ seen

private def ComponentListClosed {n : Nat} (board : Board n)
    (value : Option Polarity) (seen : List (Point n)) : Prop :=
  ∀ current ∈ seen, ∀ candidate ∈ adjacentPointList current,
    board candidate = value → candidate ∈ seen

private theorem componentProcessedClosed_nil_iff {n : Nat} {board : Board n}
    {value : Option Polarity} {seen : List (Point n)} :
    ComponentProcessedClosed board value [] seen ↔
      ComponentListClosed board value seen := by
  simp [ComponentProcessedClosed, ComponentListClosed]

private theorem componentProcessedClosed_step {n : Nat} {board : Board n}
    {value : Option Polarity} {current : Point n}
    {pending seen : List (Point n)}
    (closed : ComponentProcessedClosed board value
      (current :: pending) seen) :
    ComponentProcessedClosed board value
      (pending ++ componentFresh board value current seen)
      (seen ++ componentFresh board value current seen) := by
  intro source sourceMember sourceNotPending candidate candidateAdjacent candidateValue
  rcases List.mem_append.mp sourceMember with oldSource | freshSource
  · by_cases sourceEq : source = current
    · subst source
      by_cases oldCandidate : candidate ∈ seen
      · exact List.mem_append_left _ oldCandidate
      · exact List.mem_append_right _
          (mem_componentFresh_iff.mpr
            ⟨candidateAdjacent, candidateValue, oldCandidate⟩)
    · have sourceNotOldPending : source ∉ current :: pending := by
        simp only [List.mem_cons, not_or]
        exact ⟨sourceEq, fun sourcePending =>
          sourceNotPending (List.mem_append_left _ sourcePending)⟩
      exact List.mem_append_left _
        (closed source oldSource sourceNotOldPending candidate
          candidateAdjacent candidateValue)
  · exact False.elim
      (sourceNotPending (List.mem_append_right _ freshSource))

private theorem componentWorklist_closed_of_invariants {n : Nat}
    {board : Board n} {value : Option Polarity} :
    ∀ (fuel : Nat) (pending seen : List (Point n)),
      seen.Nodup →
      pending.Nodup →
      (∀ point ∈ pending, point ∈ seen) →
      ComponentProcessedClosed board value pending seen →
      fuel + seen.length = Fintype.card (Point n) + pending.length →
      ComponentListClosed board value
        (componentWorklist board value fuel pending seen) := by
  intro fuel
  induction fuel with
  | zero =>
      intro pending seen seenNodup _ _ processedClosed lengthBalance
      have seenLengthBound : seen.length ≤ Fintype.card (Point n) :=
        seenNodup.length_le_card
      have pendingLengthZero : pending.length = 0 := by omega
      have pendingEq : pending = [] := by simpa using pendingLengthZero
      subst pending
      simpa only [componentWorklist] using
        (componentProcessedClosed_nil_iff.mp processedClosed)
  | succ fuel ih =>
      intro pending seen seenNodup pendingNodup pendingSubset
        processedClosed lengthBalance
      cases pending with
      | nil =>
          simpa only [componentWorklist] using
            (componentProcessedClosed_nil_iff.mp processedClosed)
      | cons current pending =>
          let fresh := componentFresh board value current seen
          have freshNodup : fresh.Nodup := by
            exact componentFresh_nodup board value current seen
          have freshDisjointSeen : List.Disjoint seen fresh := by
            exact componentFresh_disjoint_seen board value current seen
          have freshDisjointPending : List.Disjoint pending fresh := by
            rw [List.disjoint_left]
            intro point pointPending pointFresh
            exact freshDisjointSeen
              (pendingSubset point (by simp [pointPending])) pointFresh
          have nextSeenNodup : (seen ++ fresh).Nodup :=
            seenNodup.append freshNodup freshDisjointSeen
          have nextPendingNodup : (pending ++ fresh).Nodup :=
            pendingNodup.of_cons.append freshNodup freshDisjointPending
          have nextPendingSubset :
              ∀ point ∈ pending ++ fresh, point ∈ seen ++ fresh := by
            intro point pointMember
            rcases List.mem_append.mp pointMember with oldPending | newFresh
            · exact List.mem_append_left _
                (pendingSubset point (by simp [oldPending]))
            · exact List.mem_append_right _ newFresh
          have nextProcessedClosed :
              ComponentProcessedClosed board value
                (pending ++ fresh) (seen ++ fresh) := by
            exact componentProcessedClosed_step processedClosed
          have nextLengthBalance :
              fuel + (seen ++ fresh).length =
                Fintype.card (Point n) + (pending ++ fresh).length := by
            simp only [List.length_append, List.length_cons] at lengthBalance ⊢
            omega
          change ComponentListClosed board value
            (componentWorklist board value fuel
              (pending ++ fresh) (seen ++ fresh))
          exact ih (pending ++ fresh) (seen ++ fresh)
            nextSeenNodup nextPendingNodup nextPendingSubset
            nextProcessedClosed nextLengthBalance

/-- A predicate is closed under same-valued orthogonal adjacency. -/
def ComponentPredicateClosed {n : Nat} (board : Board n)
    (value : Option Polarity) (predicate : Point n → Prop) : Prop :=
  ∀ current, board current = value → predicate current →
    ∀ candidate ∈ adjacentPointList current,
      board candidate = value → predicate candidate

private theorem componentWorklist_minimal {n : Nat} {board : Board n}
    {value : Option Polarity} {predicate : Point n → Prop} :
    ∀ (fuel : Nat) (pending seen : List (Point n)),
      (∀ point ∈ pending, point ∈ seen) →
      (∀ point ∈ seen, board point = value) →
      (∀ point ∈ seen, predicate point) →
      ComponentPredicateClosed board value predicate →
      ∀ point ∈ componentWorklist board value fuel pending seen,
        predicate point := by
  intro fuel
  induction fuel with
  | zero =>
      intro pending seen _ _ seenPredicate _ point member
      exact seenPredicate point member
  | succ fuel ih =>
      intro pending seen pendingSubset seenValue seenPredicate predicateClosed
        point member
      cases pending with
      | nil => exact seenPredicate point member
      | cons current pending =>
          let fresh := componentFresh board value current seen
          have currentSeen : current ∈ seen :=
            pendingSubset current (by simp)
          have currentValue : board current = value :=
            seenValue current currentSeen
          have currentPredicate : predicate current :=
            seenPredicate current currentSeen
          have freshPredicate : ∀ candidate ∈ fresh, predicate candidate := by
            intro candidate candidateFresh
            have facts := mem_componentFresh_iff.mp candidateFresh
            exact predicateClosed current currentValue currentPredicate candidate
              facts.1 facts.2.1
          have nextPendingSubset :
              ∀ candidate ∈ pending ++ fresh, candidate ∈ seen ++ fresh := by
            intro candidate candidateMember
            rcases List.mem_append.mp candidateMember with oldPending | newFresh
            · exact List.mem_append_left _
                (pendingSubset candidate (by simp [oldPending]))
            · exact List.mem_append_right _ newFresh
          have nextSeenValue :
              ∀ candidate ∈ seen ++ fresh, board candidate = value := by
            intro candidate candidateMember
            rcases List.mem_append.mp candidateMember with oldSeen | newFresh
            · exact seenValue candidate oldSeen
            · exact (mem_componentFresh_iff.mp newFresh).2.1
          have nextSeenPredicate :
              ∀ candidate ∈ seen ++ fresh, predicate candidate := by
            intro candidate candidateMember
            rcases List.mem_append.mp candidateMember with oldSeen | newFresh
            · exact seenPredicate candidate oldSeen
            · exact freshPredicate candidate newFresh
          apply ih (pending ++ fresh) (seen ++ fresh)
            nextPendingSubset nextSeenValue nextSeenPredicate predicateClosed
            point
          exact member

/-- The bounded worklist result is closed under same-valued orthogonal
adjacency. -/
theorem componentAt_closed {n : Nat} {board : Board n}
    {seed current candidate : Point n}
    (currentMember : current ∈ componentAt board seed)
    (candidateAdjacent : candidate ∈ adjacentPointList current)
    (candidateValue : board candidate = board seed) :
    candidate ∈ componentAt board seed := by
  unfold componentAt at currentMember ⊢
  simp only [List.mem_toFinset] at currentMember ⊢
  have closed := componentWorklist_closed_of_invariants
    (board := board) (value := board seed)
    (Fintype.card (Point n)) [seed] [seed]
    (by simp) (by simp) (by simp)
    (by simp [ComponentProcessedClosed]) (by simp)
  exact closed current currentMember candidate candidateAdjacent candidateValue

/-- The bounded worklist result is contained in every same-valued
adjacency-closed predicate containing its seed. -/
theorem componentAt_minimal {n : Nat} {board : Board n}
    {seed : Point n} {predicate : Point n → Prop}
    (seedPredicate : predicate seed)
    (predicateClosed : ComponentPredicateClosed
      board (board seed) predicate) :
    ∀ point ∈ componentAt board seed, predicate point := by
  intro point member
  unfold componentAt at member
  simp only [List.mem_toFinset] at member
  apply componentWorklist_minimal
    (board := board) (value := board seed)
    (predicate := predicate)
    (Fintype.card (Point n)) [seed] [seed]
    (by simp) (by simp) (by simpa) predicateClosed point member

private theorem mem_adjacentPointList_comm {n : Nat}
    {left right : Point n} :
    right ∈ adjacentPointList left ↔ left ∈ adjacentPointList right := by
  rw [← List.mem_toFinset, ← List.mem_toFinset]
  change right ∈ adjacentPoints left ↔ left ∈ adjacentPoints right
  rw [mem_adjacentPoints_iff_orthogonallyAdjacent,
    mem_adjacentPoints_iff_orthogonallyAdjacent]
  constructor <;> exact orthogonallyAdjacent_symm

/-- Component membership is symmetric: a generated member reaches the
original seed through the same undirected adjacency relation. -/
theorem componentAt_seed_mem_of_mem {n : Nat} {board : Board n}
    {seed point : Point n} (member : point ∈ componentAt board seed) :
    seed ∈ componentAt board point := by
  have pointValue : board point = board seed :=
    componentAt_member_value member
  by_contra seedNotMember
  have complementClosed :
      ComponentPredicateClosed board (board seed)
        (fun candidate => candidate ∉ componentAt board point) := by
    intro current currentValue currentNotMember candidate candidateAdjacent
      candidateValue candidateMember
    apply currentNotMember
    apply componentAt_closed
      (seed := point) (current := candidate) (candidate := current)
      candidateMember
      (mem_adjacentPointList_comm.mp candidateAdjacent)
    exact currentValue.trans pointValue.symm
  have componentOutside := componentAt_minimal
    (board := board) (seed := seed)
    (predicate := fun candidate => candidate ∉ componentAt board point)
    seedNotMember complementClosed
  exact (componentOutside point member) (point_mem_componentAt board point)

/-- Saturation/idempotence of the executable component exposure: any member
is an equivalent seed for the exact same generated finite component. -/
theorem componentAt_eq_of_mem {n : Nat} {board : Board n}
    {seed point : Point n} (member : point ∈ componentAt board seed) :
    componentAt board point = componentAt board seed := by
  have pointValue : board point = board seed :=
    componentAt_member_value member
  have seedMember : seed ∈ componentAt board point :=
    componentAt_seed_mem_of_mem member
  apply Finset.Subset.antisymm
  · apply componentAt_minimal
      (board := board) (seed := point)
      (predicate := fun candidate => candidate ∈ componentAt board seed)
      member
    intro current currentValue currentMember candidate candidateAdjacent
      candidateValue
    apply componentAt_closed currentMember candidateAdjacent
    exact candidateValue.trans pointValue
  · apply componentAt_minimal
      (board := board) (seed := seed)
      (predicate := fun candidate => candidate ∈ componentAt board point)
      seedMember
    intro current currentValue currentMember candidate candidateAdjacent
      candidateValue
    apply componentAt_closed currentMember candidateAdjacent
    exact candidateValue.trans pointValue.symm

/-- Every member of an occupied snapshot group is an equivalent seed for
that exact generated group carrier. -/
theorem groupAt_eq_of_mem {n : Nat} {board : Board n}
    {seed point : Point n} {colour : Polarity}
    (occupied : board seed = some colour)
    (member : point ∈ groupAt board seed) :
    groupAt board point = groupAt board seed := by
  have pointOccupied : board point = some colour :=
    groupAt_member_colour occupied member
  unfold groupAt at member ⊢
  rw [occupied] at member ⊢
  rw [pointOccupied]
  exact componentAt_eq_of_mem member

/-- Membership in the source-generated capture set forces absence in the
generated play board. -/
theorem boardAfterPlay_eq_none_of_mem_captured {n : Nat} {board : Board n}
    {colour : Polarity} {played captured : Point n}
    (member : captured ∈ capturedStonesAfterPlay board colour played) :
    boardAfterPlay board colour played captured = none := by
  simp [boardAfterPlay, member]

/-- Points outside the generated capture set retain the placed-board value. -/
theorem boardAfterPlay_eq_placed_of_not_mem_captured {n : Nat}
    {board : Board n} {colour : Polarity} {played point : Point n}
    (notCaptured : point ∉ capturedStonesAfterPlay board colour played) :
    boardAfterPlay board colour played point =
      Board.set board played (some colour) point := by
  simp [boardAfterPlay, notCaptured]

/-! ## Whole-component preservation across one placement -/

/-- Components depend only on the seed-value fibre of a board. -/
theorem componentAt_eq_of_same_value_fiber {n : Nat}
    {left right : Board n} {seed : Point n}
    (sameFiber : ∀ point,
      left point = left seed ↔ right point = right seed) :
    componentAt left seed = componentAt right seed := by
  apply Finset.Subset.antisymm
  · apply componentAt_minimal
      (board := left) (seed := seed)
      (predicate := fun point => point ∈ componentAt right seed)
      (point_mem_componentAt right seed)
    intro current _currentValue currentMember candidate candidateAdjacent
      candidateValue
    exact componentAt_closed currentMember candidateAdjacent
      ((sameFiber candidate).mp candidateValue)
  · apply componentAt_minimal
      (board := right) (seed := seed)
      (predicate := fun point => point ∈ componentAt left seed)
      (point_mem_componentAt left seed)
    intro current _currentValue currentMember candidate candidateAdjacent
      candidateValue
    exact componentAt_closed currentMember candidateAdjacent
      ((sameFiber candidate).mpr candidateValue)

/-- Placing `colour` at an empty point cannot change an existing opponent
component. -/
theorem groupAt_placed_opponent_eq {n : Nat} {board : Board n}
    {colour : Polarity} {played seed : Point n}
    (empty : board played = none)
    (occupied : board seed = some colour.other) :
    groupAt (Board.set board played (some colour)) seed =
      groupAt board seed := by
  have seed_ne : seed ≠ played := by
    intro equal
    subst seed
    rw [empty] at occupied
    cases occupied
  have placedOccupied :
      Board.set board played (some colour) seed = some colour.other := by
    rw [Board.set_other board (some colour) seed_ne]
    exact occupied
  unfold groupAt
  rw [occupied, placedOccupied]
  apply componentAt_eq_of_same_value_fiber
  intro point
  by_cases point_eq : point = played
  · subst point
    rw [Board.set_self, empty, placedOccupied, occupied]
    cases colour <;> simp
  · rw [Board.set_other board (some colour) point_eq,
      placedOccupied, occupied]

/-- Every point in the compiler-generated capture set has the exact opponent
colour in the placed board. -/
theorem capturedStonesAfterPlay_member_placed_colour {n : Nat}
    {board : Board n} {colour : Polarity} {played point : Point n}
    (captured : point ∈ capturedStonesAfterPlay board colour played) :
    Board.set board played (some colour) point = some colour.other := by
  unfold capturedStonesAfterPlay at captured
  simp only [Finset.mem_biUnion] at captured
  rcases captured with ⟨neighbor, _neighborAdjacent, member⟩
  split at member
  case isTrue capturedGroup =>
    exact groupAt_member_colour capturedGroup.1 member
  · simp at member

/-- The generated capture set is saturated by exact opponent components in
the placed board. -/
theorem mem_capturedStonesAfterPlay_of_same_placed_group {n : Nat}
    {board : Board n} {colour : Polarity}
    {played captured candidate : Point n}
    (capturedMember :
      captured ∈ capturedStonesAfterPlay board colour played)
    (candidateOccupied :
      Board.set board played (some colour) candidate = some colour.other)
    (sameGroup :
      groupAt (Board.set board played (some colour)) candidate =
        groupAt (Board.set board played (some colour)) captured) :
    candidate ∈ capturedStonesAfterPlay board colour played := by
  unfold capturedStonesAfterPlay at capturedMember ⊢
  simp only [Finset.mem_biUnion] at capturedMember ⊢
  rcases capturedMember with ⟨neighbor, neighborAdjacent, member⟩
  refine ⟨neighbor, neighborAdjacent, ?_⟩
  split at member
  · rename_i capturedGroup
    have capturedGroupEq :=
      groupAt_eq_of_mem capturedGroup.1 member
    have candidateSelf := occupied_point_mem_groupAt candidateOccupied
    rw [sameGroup, capturedGroupEq] at candidateSelf
    simpa [capturedGroup] using candidateSelf
  · simp at member

/-- If one stone of an old component survives a placement, no point of that
old component belongs to the generated capture set. -/
theorem source_group_not_captured_of_seed_survives {n : Nat}
    {board : Board n} {colour sourceColour : Polarity}
    {played seed point : Point n}
    (empty : board played = none)
    (seedBefore : board seed = some sourceColour)
    (seedAfter :
      boardAfterPlay board colour played seed = some sourceColour)
    (pointMember : point ∈ groupAt board seed) :
    point ∉ capturedStonesAfterPlay board colour played := by
  intro pointCaptured
  have pointBefore : board point = some sourceColour :=
    groupAt_member_colour seedBefore pointMember
  have point_ne : point ≠ played := by
    intro equal
    subst point
    rw [empty] at pointBefore
    cases pointBefore
  have pointPlaced :
      Board.set board played (some colour) point = some sourceColour := by
    rw [Board.set_other board (some colour) point_ne]
    exact pointBefore
  have pointPlacedOpponent :=
    capturedStonesAfterPlay_member_placed_colour pointCaptured
  have sourceColour_eq : sourceColour = colour.other :=
    Option.some.inj (pointPlaced.symm.trans pointPlacedOpponent)
  subst sourceColour
  have seed_ne : seed ≠ played := by
    intro equal
    subst seed
    rw [empty] at seedBefore
    cases seedBefore
  have seedPlaced :
      Board.set board played (some colour) seed = some colour.other := by
    rw [Board.set_other board (some colour) seed_ne]
    exact seedBefore
  have pointOldGroupEq : groupAt board point = groupAt board seed :=
    groupAt_eq_of_mem seedBefore pointMember
  have pointPlacedGroupEq :=
    groupAt_placed_opponent_eq (board := board) (colour := colour)
      (played := played) (seed := point) empty pointBefore
  have seedPlacedGroupEq :=
    groupAt_placed_opponent_eq (board := board) (colour := colour)
      (played := played) (seed := seed) empty seedBefore
  have samePlacedGroup :
      groupAt (Board.set board played (some colour)) seed =
        groupAt (Board.set board played (some colour)) point :=
    seedPlacedGroupEq.trans
      (pointOldGroupEq.symm.trans pointPlacedGroupEq.symm)
  have seedCaptured :=
    mem_capturedStonesAfterPlay_of_same_placed_group pointCaptured
      seedPlaced samePlacedGroup
  have seedAbsent := boardAfterPlay_eq_none_of_mem_captured seedCaptured
  rw [seedAbsent] at seedAfter
  cases seedAfter

/-- Preserving the seed value on its entire old component embeds that
component into the new generated component. -/
theorem componentAt_subset_of_component_values_preserved {n : Nat}
    {before after : Board n} {seed : Point n}
    (preserved : ∀ point ∈ componentAt before seed,
      after point = after seed) :
    componentAt before seed ⊆ componentAt after seed := by
  intro point pointMember
  have both := componentAt_minimal
      (board := before) (seed := seed)
      (predicate := fun point =>
        point ∈ componentAt before seed ∧
          point ∈ componentAt after seed)
      ⟨point_mem_componentAt before seed,
        point_mem_componentAt after seed⟩
      (by
        intro current currentValue currentMember candidate candidateAdjacent
          candidateValue
        have candidateBefore :=
          componentAt_closed currentMember.1 candidateAdjacent candidateValue
        have candidateAfter := componentAt_closed currentMember.2
          candidateAdjacent (preserved candidate candidateBefore)
        exact ⟨candidateBefore, candidateAfter⟩)
      point pointMember
  exact both.2

/-- A surviving old component embeds whole into the board generated by one
placement; capture cannot remove only a bridge inside that component. -/
theorem componentAt_subset_boardAfterPlay_of_seed_survives {n : Nat}
    {board : Board n} {colour sourceColour : Polarity}
    {played seed : Point n}
    (empty : board played = none)
    (seedBefore : board seed = some sourceColour)
    (seedAfter :
      boardAfterPlay board colour played seed = some sourceColour) :
    componentAt board seed ⊆
      componentAt (boardAfterPlay board colour played) seed := by
  apply componentAt_subset_of_component_values_preserved
  intro point pointMember
  have pointGroupMember : point ∈ groupAt board seed := by
    unfold groupAt
    rw [seedBefore]
    exact pointMember
  have pointNotCaptured :=
    source_group_not_captured_of_seed_survives empty seedBefore seedAfter
      pointGroupMember
  have pointBefore : board point = some sourceColour :=
    (componentAt_member_value pointMember).trans seedBefore
  have point_ne : point ≠ played := by
    intro equal
    subst point
    rw [empty] at pointBefore
    cases pointBefore
  calc
    boardAfterPlay board colour played point =
        Board.set board played (some colour) point :=
      boardAfterPlay_eq_placed_of_not_mem_captured pointNotCaptured
    _ = board point := Board.set_other board (some colour) point_ne
    _ = some sourceColour := pointBefore
    _ = boardAfterPlay board colour played seed := seedAfter.symm

/-- Two surviving stones from one old generated group remain in one generated
group after the placement. -/
theorem boardAfterPlay_groupAt_eq_of_sourceGroup_eq_of_survives {n : Nat}
    {board : Board n} {colour leftColour rightColour : Polarity}
    {played left right : Point n}
    (empty : board played = none)
    (leftBefore : board left = some leftColour)
    (rightBefore : board right = some rightColour)
    (sameBefore : groupAt board left = groupAt board right)
    (leftAfter :
      boardAfterPlay board colour played left = some leftColour)
    (rightAfter :
      boardAfterPlay board colour played right = some rightColour) :
    groupAt (boardAfterPlay board colour played) left =
      groupAt (boardAfterPlay board colour played) right := by
  have rightSelf := occupied_point_mem_groupAt rightBefore
  have rightInLeft : right ∈ groupAt board left := by
    rw [sameBefore]
    exact rightSelf
  have rightFromLeft : board right = some leftColour :=
    groupAt_member_colour leftBefore rightInLeft
  have colours_eq : rightColour = leftColour :=
    Option.some.inj (rightBefore.symm.trans rightFromLeft)
  subst rightColour
  have rightComponentMember : right ∈ componentAt board left := by
    unfold groupAt at rightInLeft
    rw [leftBefore] at rightInLeft
    exact rightInLeft
  have rightAfterMember :=
    componentAt_subset_boardAfterPlay_of_seed_survives empty leftBefore
      leftAfter rightComponentMember
  unfold groupAt
  rw [leftAfter, rightAfter]
  exact (componentAt_eq_of_mem rightAfterMember).symm

end Go
end ProcessGame
end SaturationMonoid
