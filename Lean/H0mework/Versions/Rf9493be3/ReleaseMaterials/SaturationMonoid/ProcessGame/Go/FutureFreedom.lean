import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.SearchExposure

/-!
# Finite relation freedom on the generated Go future cone

Future freedom is compared on the common carrier of bounded move words, not
on frame paths with different roots.  A word enters a relation fibre only
when the fixed `nativeStep?` compiler executes it from the replay-generated
current and the marked relation survives it.

Every admitted word is reconstructed as a dependent `GeneratedReplay`; its
whole state path is then proved to occur in the rooted-path fold of the same
`futureConeAt`.  Thus this file supplies a readout of the G3 cone, not a
second search root, completed future table or actual-write authority.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

universe u

/-! ## Rooted paths as a fold of the existing occurrence -/

/-- The algebra enumerating every finite root-to-generated-node path.  Keeping
all prefixes is the exact finite-horizon interpretation of paths of length at
most `d`; terminal leaves are not padded with fake self-steps. -/
def rootedPathAlgebra {Root : Type u} (root : Root)
    (childPathFamilies : List (List (List Root))) : List (List Root) :=
  [[root]] ++ childPathFamilies.flatten.map (List.cons root)

/-- Every rooted path exposed by the sole occurrence constructor. -/
def rootedPaths {Root : Type u}
    (occurrence : RootedAccountedUnfolding Root) : List (List Root) :=
  occurrence.fold rootedPathAlgebra

@[simp] theorem rootedPaths_zero {Root : Type u} (root : Root) :
    rootedPaths (RootedAccountedUnfolding.zero root) = [[root]] :=
  rfl

private theorem foldBranches_rootedPathAlgebra_exposureBranches
    {Root : Type u}
    (occurrences : List (RootedAccountedUnfolding Root)) :
    RootedAccountedUnfolding.foldBranches rootedPathAlgebra
        (exposureBranches occurrences) =
      occurrences.map rootedPaths := by
  induction occurrences with
  | nil => rfl
  | cons occurrence occurrences ih =>
      change rootedPaths occurrence ::
          RootedAccountedUnfolding.foldBranches rootedPathAlgebra
            (exposureBranches occurrences) =
        rootedPaths occurrence :: occurrences.map rootedPaths
      rw [ih]

/-- Exact fold equation for the positive-fuel cone. -/
theorem rootedPaths_finiteExposureFrom_succ {n : Nat} (law : Law)
    (fuel : Nat) (current : Frame n) :
    rootedPaths (finiteExposureFrom law (fuel + 1) current) =
      [[current]] ++
        (legalTargets law current).flatMap (fun target =>
          (rootedPaths (finiteExposureFrom law fuel target)).map
            (List.cons current)) := by
  rw [finiteExposureFrom_succ_generated]
  unfold rootedPaths
  change rootedPathAlgebra current
      (RootedAccountedUnfolding.foldBranches rootedPathAlgebra
        (exposureBranches
          ((legalTargets law current).map
            (finiteExposureFrom law fuel)))) = _
  rw [foldBranches_rootedPathAlgebra_exposureBranches]
  simp only [rootedPathAlgebra, List.flatten_eq_flatMap, List.flatMap_map,
    List.map_flatMap, id_eq]
  rfl

/-- The zero-length path is always present, independently of search fuel. -/
theorem singleton_root_mem_rootedPaths_finiteExposureFrom {n : Nat}
    (law : Law) (fuel : Nat) (current : Frame n) :
    [current] ∈ rootedPaths (finiteExposureFrom law fuel current) := by
  cases fuel with
  | zero => simp
  | succ fuel =>
      rw [rootedPaths_finiteExposureFrom_succ]
      simp

/-! ## The common bounded move-word carrier -/

/-- All move words of length at most the supplied horizon.  This is only a
finite carrier enumeration; legality is still decided by `replayFrom?`, whose
steps are the fixed `nativeStep?` compiler. -/
def moveWordsUpTo (n : Nat) : Nat → List (List (Move n))
  | 0 => [[]]
  | horizon + 1 =>
      [] :: (allMoves n).flatMap (fun move =>
        (moveWordsUpTo n horizon).map (List.cons move))

theorem mem_moveWordsUpTo_iff_length_le {n : Nat}
    (word : List (Move n)) (horizon : Nat) :
    word ∈ moveWordsUpTo n horizon ↔ word.length ≤ horizon := by
  induction horizon generalizing word with
  | zero =>
      simp [moveWordsUpTo]
  | succ horizon ih =>
      constructor
      · intro member
        rw [moveWordsUpTo] at member
        rcases List.mem_cons.mp member with wordEmpty | member
        · simp [wordEmpty]
        · rcases List.mem_flatMap.mp member with
            ⟨move, _moveMem, wordMember⟩
          rcases List.mem_map.mp wordMember with
            ⟨tail, tailMem, wordEq⟩
          subst word
          simpa using Nat.succ_le_succ ((ih tail).mp tailMem)
      · intro lengthLe
        cases word with
        | nil => simp [moveWordsUpTo]
        | cons move tail =>
            rw [moveWordsUpTo]
            apply List.mem_cons_of_mem
            apply List.mem_flatMap.mpr
            refine ⟨move, move_mem_allMoves move, ?_⟩
            apply List.mem_map.mpr
            refine ⟨tail, (ih tail).mpr ?_, rfl⟩
            simpa using lengthLe

/-! ## Exact compiler execution and occurrence factorization -/

theorem replayFrom_eq_some_of_generatedReplay {n : Nat} {law : Law}
    {start : Frame n} {word : List (Move n)}
    (continuation : GeneratedReplay law start word) :
    replayFrom? law start word = some continuation.final := by
  induction continuation with
  | nil => rfl
  | @cons start next moves move step tail ih =>
      unfold LegalStep at step
      simp only [replayFrom?]
      rw [step]
      exact ih

/-- Success of the fixed executable projection reconstructs an exact
dependent continuation.  This witness has possibility-path authority only;
actual play still requires `GeneratedReplay.ActualPly` from the initial root. -/
theorem exists_generatedReplay_of_replayFrom_eq_some {n : Nat} {law : Law}
    {start target : Frame n} {word : List (Move n)}
    (executes : replayFrom? law start word = some target) :
    ∃ continuation : GeneratedReplay law start word,
      continuation.final = target := by
  induction word generalizing start target with
  | nil =>
      simp only [replayFrom?] at executes
      injection executes with targetEq
      exact ⟨.nil start, targetEq⟩
  | cons move moves ih =>
      simp only [replayFrom?] at executes
      split at executes <;> rename_i generated generatedEq
      · contradiction
      · rcases ih executes with ⟨tail, tailFinal⟩
        exact ⟨.cons move generatedEq tail, tailFinal⟩

/-- An exact generated continuation of bounded length is literally one of the
rooted paths folded from the same finite G3 exposure. -/
theorem generatedReplay_stateTrace_mem_rootedPaths_finiteExposureFrom
    {n : Nat} {law : Law} {start : Frame n} {word : List (Move n)}
    (continuation : GeneratedReplay law start word) {horizon : Nat}
    (bounded : word.length ≤ horizon) :
    continuation.stateTrace ∈
      rootedPaths (finiteExposureFrom law horizon start) := by
  induction continuation generalizing horizon with
  | nil replayStart =>
      simpa [GeneratedReplay.stateTrace] using
        singleton_root_mem_rootedPaths_finiteExposureFrom law horizon replayStart
  | @cons start next moves move step tail ih =>
      cases horizon with
      | zero => simp at bounded
      | succ horizon =>
          rw [rootedPaths_finiteExposureFrom_succ]
          apply List.mem_append.mpr
          apply Or.inr
          apply List.mem_flatMap.mpr
          refine ⟨next, ?_, ?_⟩
          · exact mem_legalTargets_iff.mpr ⟨move, step⟩
          · apply List.mem_map.mpr
            refine ⟨tail.stateTrace, ih ?_, ?_⟩
            · simpa using bounded
            · rfl

/-! ## Relation-survival fibres -/

/-- A marked relation supplies only its current-local truth predicate.  It
deliberately contains no path verdict, player, attack/defense role or
constraint-owner label: path survival is generated by checking every frame of
the exact compiler continuation, and roles are generated downstream. -/
structure RelationProbe (n : Nat) where
  holds : Frame n → Bool

/-- Fixed compiler from one board-generated snapshot group to its persistence
relation.  A frame satisfies the relation exactly when at least one point of
the generated source carrier still bears the generated source polarity.  The
caller cannot install a word-level verdict or tactical phase in this image. -/
def groupRelationProbe {n : Nat} {sourceBoard : Board n}
    (group : SnapshotGroup sourceBoard) : RelationProbe n where
  holds := fun frame => decide (∃ point ∈ group.carrier,
    frame.visible.board point = some group.polarity)

/-- The exact source current satisfies its group-generated relation. -/
theorem groupRelationProbe_holds_source {n : Nat}
    (source : Frame n)
    (group : SnapshotGroup source.visible.board) :
    (groupRelationProbe group).holds source = true := by
  rcases snapshotGroup_has_occupied_member group with
    ⟨stone, belongs, member⟩
  change decide (∃ point ∈ group.carrier,
    source.visible.board point = some group.polarity) = true
  apply decide_eq_true_eq.mpr
  refine ⟨stone.point, member, ?_⟩
  have polarityEq : group.polarity = stone.polarity := by
    rw [← belongs]
    rfl
  rw [polarityEq]
  exact stone.occupied

/-- Fixed source-turn relation generated by an actual replay current.  It is
a tactical constraint face, not a `Player` identity: the latter remains the
G2 lineage fold. -/
def sourceTurnRelationAt {n : Nat} {law : Law}
    {moves : List (Move n)}
    (replay : GeneratedReplay law (Frame.initial n) moves) :
    RelationProbe n where
  holds := fun frame => decide
    (frame.visible.toMove = replay.final.visible.toMove)

@[simp] theorem sourceTurnRelationAt_holds_current {n : Nat} {law : Law}
    {moves : List (Move n)}
    (replay : GeneratedReplay law (Frame.initial n) moves) :
    (sourceTurnRelationAt replay).holds replay.final = true := by
  simp [sourceTurnRelationAt]

/-- Native path survival: the relation must hold at the source and at every
compiler-generated child.  Illegal words fail rather than receiving a caller
verdict. -/
def relationSurvivesWord {n : Nat} (law : Law) (relation : RelationProbe n) :
    Frame n → List (Move n) → Bool
  | current, [] => relation.holds current
  | current, move :: moves =>
      relation.holds current &&
        match nativeStep? law current move with
        | none => false
        | some target => relationSurvivesWord law relation target moves

theorem relationSurvivesWord_eq_stateTrace_all {n : Nat} {law : Law}
    {start : Frame n} {word : List (Move n)}
    (relation : RelationProbe n)
    (continuation : GeneratedReplay law start word) :
    relationSurvivesWord law relation start word =
      continuation.stateTrace.all relation.holds := by
  induction continuation with
  | nil => simp [relationSurvivesWord, GeneratedReplay.stateTrace]
  | @cons start next moves move step tail ih =>
      unfold LegalStep at step
      simp [relationSurvivesWord, GeneratedReplay.stateTrace, step, ih]

/-- The finite freedom fibre `Ω_R^d(H)` on the common move-word carrier. -/
def relationFreedom {n : Nat} {law : Law} {moves : List (Move n)}
    (replay : GeneratedReplay law (Frame.initial n) moves)
    (horizon : Nat) (relation : RelationProbe n) :
    Finset (List (Move n)) :=
  ((moveWordsUpTo n horizon).filter fun word =>
    (replayFrom? law replay.final word).isSome &&
      relationSurvivesWord law relation replay.final word).toFinset

theorem mem_relationFreedom_iff {n : Nat} {law : Law}
    {moves : List (Move n)}
    (replay : GeneratedReplay law (Frame.initial n) moves)
    (horizon : Nat) (relation : RelationProbe n)
    (word : List (Move n)) :
    word ∈ relationFreedom replay horizon relation ↔
      word.length ≤ horizon ∧
      (replayFrom? law replay.final word).isSome = true ∧
      relationSurvivesWord law relation replay.final word = true := by
  simp [relationFreedom, mem_moveWordsUpTo_iff_length_le,
    Bool.and_eq_true]

/-- Public provenance mouth: every freedom element is an exact compiler path
in the fold of the same replay-indexed future cone. -/
theorem relationFreedom_member_factors_through_futureCone {n : Nat}
    {law : Law} {moves : List (Move n)}
    (replay : GeneratedReplay law (Frame.initial n) moves)
    (horizon : Nat) (relation : RelationProbe n)
    {word : List (Move n)}
    (member : word ∈ relationFreedom replay horizon relation) :
    ∃ continuation : GeneratedReplay law replay.final word,
      continuation.stateTrace ∈ rootedPaths (futureConeAt replay horizon) ∧
      continuation.stateTrace.all relation.holds = true := by
  have facts := (mem_relationFreedom_iff replay horizon relation word).mp member
  cases executesEq : replayFrom? law replay.final word with
  | none => simp [executesEq] at facts
  | some target =>
      rcases exists_generatedReplay_of_replayFrom_eq_some executesEq with
        ⟨continuation, _finalEq⟩
      refine ⟨continuation, ?_, ?_⟩
      · exact generatedReplay_stateTrace_mem_rootedPaths_finiteExposureFrom
          continuation facts.1
      · rw [← relationSurvivesWord_eq_stateTrace_all relation continuation]
        exact facts.2.2

/-- Exact converse of the provenance mouth: a bounded compiler continuation
whose entire generated state path satisfies the relation is admitted to the
finite fibre. -/
theorem generatedReplay_mem_relationFreedom_of_all_holds {n : Nat}
    {law : Law} {moves : List (Move n)}
    (replay : GeneratedReplay law (Frame.initial n) moves)
    (horizon : Nat) (relation : RelationProbe n)
    {word : List (Move n)}
    (continuation : GeneratedReplay law replay.final word)
    (bounded : word.length ≤ horizon)
    (allHold : continuation.stateTrace.all relation.holds = true) :
    word ∈ relationFreedom replay horizon relation := by
  apply (mem_relationFreedom_iff replay horizon relation word).mpr
  refine ⟨bounded, ?_, ?_⟩
  · rw [replayFrom_eq_some_of_generatedReplay continuation]
    rfl
  · rw [relationSurvivesWord_eq_stateTrace_all relation continuation]
    exact allHold

/-! ## Strict change and recovery on actual edges -/

/-- Strict inclusion written without relying on a caller-selected cardinality
summary: every left freedom survives on the right, and an exact right-only
word witnesses the change. -/
def StrictFreedomSubset {n : Nat}
    (left right : Finset (List (Move n))) : Prop :=
  left ⊆ right ∧ ∃ word, word ∈ right ∧ word ∉ left

instance {n : Nat} (left right : Finset (List (Move n))) :
    Decidable (StrictFreedomSubset left right) := by
  unfold StrictFreedomSubset
  infer_instance

theorem StrictFreedomSubset.irrefl {n : Nat}
    (freedom : Finset (List (Move n))) :
    ¬ StrictFreedomSubset freedom freedom := by
  rintro ⟨_subset, word, _member, missing⟩
  exact missing _member

/-- Generic same-relation shrink basis: the target cone has strictly fewer
surviving words on the same bounded carrier.  Tactical attack is generated
only after a fixed source relation image and the downstream phase law consume
this comparison. -/
def FreedomShrinksAt {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    (ply : GeneratedReplay.ActualPly replay)
    (horizon : Nat) (relation : RelationProbe n) : Prop :=
  StrictFreedomSubset
    (relationFreedom ply.extended horizon relation)
    (relationFreedom replay horizon relation)

/-- One actual ply enlarges the exact marked-relation freedom fibre. -/
def FreedomGrowsAt {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    (ply : GeneratedReplay.ActualPly replay)
    (horizon : Nat) (relation : RelationProbe n) : Prop :=
  StrictFreedomSubset
    (relationFreedom replay horizon relation)
    (relationFreedom ply.extended horizon relation)

/-- A response recovers future freedom only after an exact preceding
compression.  Besides shrink and grow, a concrete common-carrier word must be
present before pressure, lost under pressure and restored by the response. -/
structure FreedomRecoveryAt {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    (pressure : GeneratedReplay.ActualPly replay)
    (response : GeneratedReplay.ActualPly pressure.extended)
    (horizon : Nat) (relation : RelationProbe n) where
  compressed : FreedomShrinksAt pressure horizon relation
  expanded : FreedomGrowsAt response horizon relation
  recoveredWord : List (Move n)
  presentBefore : recoveredWord ∈ relationFreedom replay horizon relation
  lostUnderPressure :
    recoveredWord ∉ relationFreedom pressure.extended horizon relation
  restoredByResponse :
    recoveredWord ∈ relationFreedom response.extended horizon relation

/-! ## Source-generated group-relation mouths -/

/-- The actual-current-indexed image of the fixed group-relation compiler. -/
def groupRelationFreedomAt {n : Nat} {law : Law}
    {moves : List (Move n)}
    (replay : GeneratedReplay law (Frame.initial n) moves)
    (horizon : Nat)
    (group : SnapshotGroup replay.final.visible.board) :
    Finset (List (Move n)) :=
  relationFreedom replay horizon (groupRelationProbe group)

/-- Group-anchored strict shrink.  The marked relation is generated from one
exact snapshot quotient class at the actual source current. -/
def GroupFreedomShrinksAt {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    (ply : GeneratedReplay.ActualPly replay) (horizon : Nat)
    (group : SnapshotGroup replay.final.visible.board) : Prop :=
  FreedomShrinksAt ply horizon (groupRelationProbe group)

/-- Group-anchored strict growth on the same exact actual edge. -/
def GroupFreedomGrowsAt {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    (ply : GeneratedReplay.ActualPly replay) (horizon : Nat)
    (group : SnapshotGroup replay.final.visible.board) : Prop :=
  FreedomGrowsAt ply horizon (groupRelationProbe group)

/-- Same-relation recovery is indexed by the one baseline generated group and
two consecutive actual plies.  The anchor cannot change between compression
and restoration. -/
abbrev GroupFreedomRecoveryAt {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    (pressure : GeneratedReplay.ActualPly replay)
    (response : GeneratedReplay.ActualPly pressure.extended)
    (horizon : Nat)
    (group : SnapshotGroup replay.final.visible.board) :=
  FreedomRecoveryAt pressure response horizon (groupRelationProbe group)

/-- Strict change of the exact source-turn constraint on one actual edge. -/
def TurnFreedomShrinksAt {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    (ply : GeneratedReplay.ActualPly replay) (horizon : Nat) : Prop :=
  FreedomShrinksAt ply horizon (sourceTurnRelationAt replay)

def TurnFreedomGrowsAt {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    (ply : GeneratedReplay.ActualPly replay) (horizon : Nat) : Prop :=
  FreedomGrowsAt ply horizon (sourceTurnRelationAt replay)

/-- Two consecutive actual plies recover one fixed baseline turn relation;
the relation is not recomputed from the intermediate target. -/
abbrev TurnFreedomRecoveryAt {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    (pressure : GeneratedReplay.ActualPly replay)
    (response : GeneratedReplay.ActualPly pressure.extended)
    (horizon : Nat) :=
  FreedomRecoveryAt pressure response horizon (sourceTurnRelationAt replay)

/-- Every group freedom fibre contains the empty exact continuation because
the fixed group relation holds at its generated source current. -/
theorem empty_mem_groupRelationFreedomAt {n : Nat} {law : Law}
    {moves : List (Move n)}
    (replay : GeneratedReplay law (Frame.initial n) moves)
    (horizon : Nat)
    (group : SnapshotGroup replay.final.visible.board) :
    [] ∈ groupRelationFreedomAt replay horizon group := by
  apply generatedReplay_mem_relationFreedom_of_all_holds replay horizon
    (groupRelationProbe group) (.nil replay.final)
  · simp
  · simpa [GeneratedReplay.stateTrace] using
      groupRelationProbe_holds_source replay.final group

/-- Both ends of a shrink mouth retain same-cone occurrence provenance; the
right-only witness cannot be a fabricated word or a path from another root. -/
theorem FreedomShrinksAt.provenance {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {ply : GeneratedReplay.ActualPly replay}
    {horizon : Nat} {relation : RelationProbe n}
    (shrinks : FreedomShrinksAt ply horizon relation) :
    (∀ word, word ∈ relationFreedom ply.extended horizon relation →
      ∃ continuation : GeneratedReplay law ply.extended.final word,
        continuation.stateTrace ∈
          rootedPaths (futureConeAt ply.extended horizon)) ∧
      ∃ lostWord,
        lostWord ∈ relationFreedom replay horizon relation ∧
        lostWord ∉ relationFreedom ply.extended horizon relation ∧
        ∃ continuation : GeneratedReplay law replay.final lostWord,
          continuation.stateTrace ∈
            rootedPaths (futureConeAt replay horizon) := by
  constructor
  · intro word member
    rcases relationFreedom_member_factors_through_futureCone
        ply.extended horizon relation member with
      ⟨continuation, pathMem, _survives⟩
    exact ⟨continuation, pathMem⟩
  · rcases shrinks.2 with ⟨lostWord, present, lost⟩
    refine ⟨lostWord, present, lost, ?_⟩
    rcases relationFreedom_member_factors_through_futureCone
        replay horizon relation present with
      ⟨continuation, pathMem, _survives⟩
    exact ⟨continuation, pathMem⟩

end Go
end ProcessGame
end SaturationMonoid
