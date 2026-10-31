import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Future.HabitableFreedom
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.TacticalConstraintPhase

/-!
# Exact habitable future freedom on a relation phase edge

Both sides of an exact `RelationPhaseEdge` are read through one finite bounded
move-word carrier.  A code is admitted only by an exact `GeneratedReplay`
whose whole state trace satisfies the side's relation.  The resulting public
word finset is proved equal to the existing `relationFreedom`; this module
therefore adds no search root, actual write or completed future authority.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go
namespace Society
namespace Future

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

/-! ## The two exact edge boundaries -/

inductive RelationEdgeSide where
  | source
  | target
  deriving DecidableEq, Repr

/-- The exact replay at either side of one generated phase edge. -/
def replayAt {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {horizon : Nat} {transport : RelationTransportLaw n}
    {ply : GeneratedReplay.ActualPly replay}
    (_edge : RelationPhaseEdge horizon transport ply) :
    (side : RelationEdgeSide) →
      Σ boundaryMoves : List (Move n),
        GeneratedReplay law (Frame.initial n) boundaryMoves
  | .source => ⟨moves, replay⟩
  | .target => ⟨moves ++ [ply.emitted], ply.extended⟩

/-- The relation occurrence generated at either side of the same edge. -/
def relationAt {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {horizon : Nat} {transport : RelationTransportLaw n}
    {ply : GeneratedReplay.ActualPly replay}
    (edge : RelationPhaseEdge horizon transport ply) :
    RelationEdgeSide → RelationProbe n
  | .source => edge.sourceRelation
  | .target => edge.targetRelation

/-! ## Exact habitation on the common word carrier -/

/-- A bounded possibility code carries its exact compiler continuation and
whole-path relation survival.  No path verdict can be supplied without the
dependent replay that it judges. -/
structure HabitableContinuationAt {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {horizon : Nat} {transport : RelationTransportLaw n}
    {ply : GeneratedReplay.ActualPly replay}
    (edge : RelationPhaseEdge horizon transport ply)
    (side : RelationEdgeSide) (word : List (Move n)) where
  continuation : GeneratedReplay law (replayAt edge side).2.final word
  bounded : word.length ≤ horizon
  relationSurvives :
    continuation.stateTrace.all (relationAt edge side).holds = true

/-- Every inhabitant's exact state path is folded from the same pre-existing
G3 future cone rooted at its edge boundary. -/
theorem HabitableContinuationAt.factors_through_futureCone
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {horizon : Nat} {transport : RelationTransportLaw n}
    {ply : GeneratedReplay.ActualPly replay}
    {edge : RelationPhaseEdge horizon transport ply}
    {side : RelationEdgeSide} {word : List (Move n)}
    (habitable : HabitableContinuationAt edge side word) :
    habitable.continuation.stateTrace ∈
      rootedPaths (futureConeAt (replayAt edge side).2 horizon) := by
  exact generatedReplay_stateTrace_mem_rootedPaths_finiteExposureFrom
    habitable.continuation habitable.bounded

/-- The finite type of words bounded by the edge horizon. -/
abbrev BoundedMoveCode (n horizon : Nat) :=
  ↑((moveWordsUpTo n horizon).toFinset)

/-- Forgetting the bounded-code proof is injective. -/
def boundedMoveCodeEmbedding (n horizon : Nat) :
    BoundedMoveCode n horizon ↪ List (Move n) where
  toFun := Subtype.val
  inj' := Subtype.val_injective

/-- Public exact future codes at one edge side.  This is the injective word
image of the universal finite inhabited-fibre filter. -/
noncomputable def FutureFreedomCodesAt
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {horizon : Nat} {transport : RelationTransportLaw n}
    {ply : GeneratedReplay.ActualPly replay}
    (edge : RelationPhaseEdge horizon transport ply)
    (side : RelationEdgeSide) : Finset (List (Move n)) :=
  (SaturationMonoid.ProcessGame.Society.Future.FutureFreedomCodes
      (fun code : BoundedMoveCode n horizon =>
        HabitableContinuationAt edge side code.1)).map
    (boundedMoveCodeEmbedding n horizon)

/-- Exact public membership mouth: a word is present precisely when its
dependent continuation fibre is inhabited. -/
theorem mem_FutureFreedomCodesAt_iff
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {horizon : Nat} {transport : RelationTransportLaw n}
    {ply : GeneratedReplay.ActualPly replay}
    (edge : RelationPhaseEdge horizon transport ply)
    (side : RelationEdgeSide) (word : List (Move n)) :
    word ∈ FutureFreedomCodesAt edge side ↔
      Nonempty (HabitableContinuationAt edge side word) := by
  classical
  constructor
  · intro member
    rcases Finset.mem_map.mp member with
      ⟨code, codeMember, codeEq⟩
    change (code : List (Move n)) = word at codeEq
    have inhabited :=
      (SaturationMonoid.ProcessGame.Society.Future.mem_FutureFreedomCodes_iff
        (fun bounded : BoundedMoveCode n horizon =>
          HabitableContinuationAt edge side bounded.1) code).mp codeMember
    rcases inhabited with ⟨habitable⟩
    exact ⟨codeEq ▸ habitable⟩
  · rintro ⟨habitable⟩
    have wordMem : word ∈ (moveWordsUpTo n horizon).toFinset := by
      simpa using
        (mem_moveWordsUpTo_iff_length_le word horizon).mpr habitable.bounded
    let code : BoundedMoveCode n horizon := ⟨word, wordMem⟩
    apply Finset.mem_map.mpr
    refine ⟨code, ?_, rfl⟩
    exact
      (SaturationMonoid.ProcessGame.Society.Future.mem_FutureFreedomCodes_iff
        (fun bounded : BoundedMoveCode n horizon =>
          HabitableContinuationAt edge side bounded.1) code).mpr
        ⟨habitable⟩

/-- The inhabited-fibre construction recovers exactly the existing G4
relation-freedom fibre on either side of every phase edge. -/
theorem FutureFreedomCodesAt_eq_relationFreedom
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {horizon : Nat} {transport : RelationTransportLaw n}
    {ply : GeneratedReplay.ActualPly replay}
    (edge : RelationPhaseEdge horizon transport ply)
    (side : RelationEdgeSide) :
    FutureFreedomCodesAt edge side =
      relationFreedom (replayAt edge side).2 horizon
        (relationAt edge side) := by
  classical
  ext word
  rw [mem_FutureFreedomCodesAt_iff]
  constructor
  · rintro ⟨habitable⟩
    exact generatedReplay_mem_relationFreedom_of_all_holds
      (replayAt edge side).2 horizon (relationAt edge side)
      habitable.continuation habitable.bounded habitable.relationSurvives
  · intro member
    rcases relationFreedom_member_factors_through_futureCone
        (replayAt edge side).2 horizon (relationAt edge side) member with
      ⟨continuation, _pathMember, relationSurvives⟩
    exact ⟨{
      continuation := continuation
      bounded :=
        ((mem_relationFreedom_iff (replayAt edge side).2 horizon
          (relationAt edge side) word).mp member).1
      relationSurvives := relationSurvives
    }⟩

/-- Source-side exact future codes. -/
noncomputable abbrev SourceFutureFreedomCodesAt
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {horizon : Nat} {transport : RelationTransportLaw n}
    {ply : GeneratedReplay.ActualPly replay}
    (edge : RelationPhaseEdge horizon transport ply) :=
  FutureFreedomCodesAt edge .source

/-- Target-side exact future codes. -/
noncomputable abbrev TargetFutureFreedomCodesAt
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {horizon : Nat} {transport : RelationTransportLaw n}
    {ply : GeneratedReplay.ActualPly replay}
    (edge : RelationPhaseEdge horizon transport ply) :=
  FutureFreedomCodesAt edge .target

/-! ## Inhabited versus actionable freedom -/

/-- Exact inhabited codes whose move word is not the idle empty word. -/
noncomputable def ActionableFutureFreedomCodesAt
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {horizon : Nat} {transport : RelationTransportLaw n}
    {ply : GeneratedReplay.ActualPly replay}
    (edge : RelationPhaseEdge horizon transport ply)
    (side : RelationEdgeSide) : Finset (List (Move n)) :=
  (SaturationMonoid.ProcessGame.Society.Future.ActionableFutureCodes
      (fun code : BoundedMoveCode n horizon =>
        HabitableContinuationAt edge side code.1)
      (fun code => code.1 = [])).map
    (boundedMoveCodeEmbedding n horizon)

theorem mem_ActionableFutureFreedomCodesAt_iff
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {horizon : Nat} {transport : RelationTransportLaw n}
    {ply : GeneratedReplay.ActualPly replay}
    (edge : RelationPhaseEdge horizon transport ply)
    (side : RelationEdgeSide) (word : List (Move n)) :
    word ∈ ActionableFutureFreedomCodesAt edge side ↔
      Nonempty (HabitableContinuationAt edge side word) ∧ word ≠ [] := by
  classical
  constructor
  · intro member
    rcases Finset.mem_map.mp member with
      ⟨code, codeMember, codeEq⟩
    change (code : List (Move n)) = word at codeEq
    have facts :=
      (SaturationMonoid.ProcessGame.Society.Future.mem_ActionableFutureCodes_iff
        (fun bounded : BoundedMoveCode n horizon =>
          HabitableContinuationAt edge side bounded.1)
        (fun bounded => bounded.1 = []) code).mp codeMember
    rcases facts.1 with ⟨habitable⟩
    refine ⟨⟨codeEq ▸ habitable⟩, ?_⟩
    intro wordEmpty
    exact facts.2 (by simpa [wordEmpty] using codeEq)
  · rintro ⟨⟨habitable⟩, nonemptyWord⟩
    have wordMem : word ∈ (moveWordsUpTo n horizon).toFinset := by
      simpa using
        (mem_moveWordsUpTo_iff_length_le word horizon).mpr habitable.bounded
    let code : BoundedMoveCode n horizon := ⟨word, wordMem⟩
    apply Finset.mem_map.mpr
    refine ⟨code, ?_, rfl⟩
    exact
      (SaturationMonoid.ProcessGame.Society.Future.mem_ActionableFutureCodes_iff
        (fun bounded : BoundedMoveCode n horizon =>
          HabitableContinuationAt edge side bounded.1)
        (fun bounded => bounded.1 = []) code).mpr
        ⟨⟨habitable⟩, nonemptyWord⟩

/-- The idle empty path is always a genuine inhabitant when the generated
relation holds at this exact boundary root. -/
def emptyHabitableContinuationAt
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {horizon : Nat} {transport : RelationTransportLaw n}
    {ply : GeneratedReplay.ActualPly replay}
    (edge : RelationPhaseEdge horizon transport ply)
    (side : RelationEdgeSide)
    (rootHolds :
      (relationAt edge side).holds (replayAt edge side).2.final = true) :
    HabitableContinuationAt edge side [] where
  continuation := .nil (replayAt edge side).2.final
  bounded := by simp
  relationSurvives := by
    simpa [GeneratedReplay.stateTrace] using rootHolds

/-- At horizon zero, a true root relation leaves exactly the idle inhabited
code. -/
theorem FutureFreedomCodesAt_zero_eq_singleton
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {transport : RelationTransportLaw n}
    {ply : GeneratedReplay.ActualPly replay}
    (edge : RelationPhaseEdge 0 transport ply)
    (side : RelationEdgeSide)
    (rootHolds :
      (relationAt edge side).holds (replayAt edge side).2.final = true) :
    FutureFreedomCodesAt edge side = {[]} := by
  classical
  ext word
  rw [mem_FutureFreedomCodesAt_iff]
  constructor
  · rintro ⟨habitable⟩
    have lengthZero : word.length = 0 := Nat.eq_zero_of_le_zero habitable.bounded
    exact Finset.mem_singleton.mpr (List.length_eq_zero_iff.mp lengthZero)
  · intro member
    have wordEmpty : word = [] := Finset.mem_singleton.mp member
    subst word
    exact ⟨emptyHabitableContinuationAt edge side rootHolds⟩

/-- Horizon zero can be inhabited while having no actionable future. -/
theorem horizon_zero_inhabited_but_not_actionable
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {transport : RelationTransportLaw n}
    {ply : GeneratedReplay.ActualPly replay}
    (edge : RelationPhaseEdge 0 transport ply)
    (side : RelationEdgeSide)
    (rootHolds :
      (relationAt edge side).holds (replayAt edge side).2.final = true) :
    (FutureFreedomCodesAt edge side).Nonempty ∧
      ActionableFutureFreedomCodesAt edge side = ∅ := by
  constructor
  · rw [FutureFreedomCodesAt_zero_eq_singleton edge side rootHolds]
    exact ⟨[], by simp⟩
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    intro word member
    have facts :=
      (mem_ActionableFutureFreedomCodesAt_iff edge side word).mp member
    rcases facts.1 with ⟨habitable⟩
    have lengthZero : word.length = 0 :=
      Nat.eq_zero_of_le_zero habitable.bounded
    exact facts.2 (List.length_eq_zero_iff.mp lengthZero)

/-! ## Root-false negative control -/

theorem relationSurvivesWord_eq_false_of_root_false
    {n : Nat} {law : Law} (relation : RelationProbe n)
    (current : Frame n) (word : List (Move n))
    (rootFalse : relation.holds current = false) :
    relationSurvivesWord law relation current word = false := by
  cases word <;> simp [relationSurvivesWord, rootFalse]

/-- A relation false at its generated boundary root has no habitable code at
any horizon. -/
theorem FutureFreedomCodesAt_eq_empty_of_root_false
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {horizon : Nat} {transport : RelationTransportLaw n}
    {ply : GeneratedReplay.ActualPly replay}
    (edge : RelationPhaseEdge horizon transport ply)
    (side : RelationEdgeSide)
    (rootFalse :
      (relationAt edge side).holds (replayAt edge side).2.final = false) :
    FutureFreedomCodesAt edge side = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro word member
  rcases (mem_FutureFreedomCodesAt_iff edge side word).mp member with
    ⟨habitable⟩
  have survives :
      relationSurvivesWord law (relationAt edge side)
          (replayAt edge side).2.final word = true := by
    rw [relationSurvivesWord_eq_stateTrace_all
      (relationAt edge side) habitable.continuation]
    exact habitable.relationSurvives
  rw [relationSurvivesWord_eq_false_of_root_false
    (relationAt edge side) (replayAt edge side).2.final word rootFalse] at survives
  contradiction

end Future
end Society
end Go
end ProcessGame
end SaturationMonoid
