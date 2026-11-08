import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.GeneratedPlayerLineage

/-!
# G2 generated-player lineage regression

One and two pass scripts exercise empty/nonempty generated lineages, exact
ply-index ownership, the `Z2` naming gauge and actual-occurrence advance.  The
two emitted moves have the same `Move` value but opposite owners, so equality
of move values cannot replace exact occurrence identity.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go
namespace G2PlayerLineageRegression

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

def law : Law := Law.positionalSuperko 0

def onePassMoves : List (Move 2) := [.pass]

theorem onePass_generated_isSome :
    (generate? law 2 onePassMoves).isSome = true := by
  decide

def onePassReplay :
    GeneratedReplay law (Frame.initial 2) onePassMoves :=
  (generate? law 2 onePassMoves).get onePass_generated_isSome

def passPassMoves : List (Move 2) := [.pass, .pass]

theorem passPass_generated_isSome :
    (generate? law 2 passPassMoves).isSome = true := by
  decide

def passPassReplay :
    GeneratedReplay law (Frame.initial 2) passPassMoves :=
  (generate? law 2 passPassMoves).get passPass_generated_isSome

def firstPly : Fin passPassMoves.length := ⟨0, by decide⟩

def secondPly : Fin passPassMoves.length := ⟨1, by decide⟩

def onlyPly : Fin onePassMoves.length := ⟨0, by decide⟩

/-- The same occurrence fold generates the alternating unnamed mover
channels. -/
theorem passPass_moverFold :
    passPassReplay.moverFold = [.positive, .negative] := by
  decide

/-- Both generated player carriers are inhabited after two passes. -/
theorem passPass_both_player_carriers_nonempty :
    Nonempty
        (GeneratedReplay.PlayerMoveCarrier passPassReplay
          (passPassReplay.player .positive)) ∧
      Nonempty
        (GeneratedReplay.PlayerMoveCarrier passPassReplay
          (passPassReplay.player .negative)) := by
  constructor
  · exact ⟨⟨firstPly, by decide⟩⟩
  · exact ⟨⟨secondPly, by decide⟩⟩

/-- A short actual prefix can leave the second generated lineage empty
without deleting that player carrier. -/
theorem onePass_negative_events_empty :
    (onePassReplay.lineage .negative).events = [] := by
  decide

theorem onePass_generated_players_still_distinct :
    onePassReplay.player .positive ≠ onePassReplay.player .negative := by
  exact onePassReplay.generatedPlayerEquiv.injective.ne (by decide)

/-- Partition existence is consumed at exact ply indices. -/
theorem passPass_player_partition_exists :
    ∃ owner : Fin passPassMoves.length →
        GeneratedReplay.GeneratedPlayer passPassReplay,
      ∀ index,
        passPassReplay.EventOwnedBy index (owner index) ∧
        ∀ candidate, passPassReplay.EventOwnedBy index candidate →
          candidate = owner index :=
  passPassReplay.playerPartitionExists

theorem passPass_every_move_has_exactly_one_owner
    (index : Fin passPassMoves.length) :
    ∃! generated : GeneratedReplay.GeneratedPlayer passPassReplay,
      passPassReplay.EventOwnedBy index generated :=
  passPassReplay.everyMoveOwnedByExactlyOneGeneratedPlayer index

/-- Negative regression: the two exact plies carry equal `.pass` values, but
their generated owners are opposite.  A value-only identity test would merge
them and is rejected by the index-level carrier. -/
theorem repeated_move_value_does_not_merge_player_lineages :
    (passPassReplay.eventAt firstPly).move =
        (passPassReplay.eventAt secondPly).move ∧
      passPassReplay.EventOwnedBy firstPly
        (passPassReplay.player .positive) ∧
      passPassReplay.EventOwnedBy secondPly
        (passPassReplay.player .negative) ∧
      ¬ passPassReplay.EventOwnedBy secondPly
        (passPassReplay.player .positive) := by
  decide

/-- The positive first ply is present in its exact index-level carrier. -/
theorem firstPly_mem_positive_carrier :
    ∃ owned : GeneratedReplay.PlayerMoveCarrier passPassReplay
        (passPassReplay.player .positive),
      owned.1 = firstPly :=
  (passPassReplay.eventOwnedBy_iff_exactPly_mem_playerMoveCarrier
    firstPly (passPassReplay.player .positive)).mp (by decide)

def gaugeLabel (generated : GeneratedReplay.GeneratedPlayer passPassReplay) : Bool :=
  match generated.1.control with
  | .positive => false
  | .negative => true

def gaugePresentation :
    GeneratedReplay.AnonymousPlayerPresentation passPassReplay where
  label := gaugeLabel
  label_injective := by
    intro left right equal
    apply passPassReplay.generatedPlayerEquiv.symm.injective
    change left.1.control = right.1.control
    cases leftControl : left.1.control <;>
      cases rightControl : right.1.control <;>
      simp_all [gaugeLabel]

def swappedGaugeLabel
    (generated : GeneratedReplay.GeneratedPlayer passPassReplay) : Bool :=
  !gaugeLabel generated

def swappedGaugePresentation :
    GeneratedReplay.AnonymousPlayerPresentation passPassReplay where
  label := swappedGaugeLabel
  label_injective := by
    intro left right equal
    apply gaugePresentation.label_injective
    change gaugeLabel left = gaugeLabel right
    change (!gaugeLabel left) = (!gaugeLabel right) at equal
    cases leftLabel : gaugeLabel left <;>
      cases rightLabel : gaugeLabel right <;>
      simp_all

/-- Black/White-style labels are only a gauge: the swapped presentation is
the nontrivial action and that action is unique. -/
theorem swappedGauge_is_unique_Z2_action :
    ∃! swap : Bool, ∀ generated,
      swappedGaugePresentation.label generated =
        GeneratedReplay.z2Swap swap (gaugePresentation.label generated) :=
  passPassReplay.playerPartitionUniqueUpToSwap
    gaugePresentation swappedGaugePresentation

theorem swappedGauge_is_nontrivial
    (generated : GeneratedReplay.GeneratedPlayer passPassReplay) :
    swappedGaugePresentation.label generated =
      GeneratedReplay.z2Swap true (gaugePresentation.label generated) := by
  rfl

theorem secondPass_generated_isSome :
    (nativeStep? law onePassReplay.final (.pass : Move 2)).isSome = true := by
  decide

def secondPassTarget : Frame 2 :=
  (nativeStep? law onePassReplay.final (.pass : Move 2)).get
    secondPass_generated_isSome

theorem secondPassStep :
    LegalStep law onePassReplay.final (.pass : Move 2) secondPassTarget := by
  unfold LegalStep secondPassTarget
  exact (Option.some_get secondPass_generated_isSome).symm

def advancedReplay :
    GeneratedReplay law (Frame.initial 2) (onePassMoves ++ [.pass]) :=
  onePassReplay.snoc .pass secondPassStep

/-- The appended replay is literally the shared root occurrence's frontier
advance, not a sibling occurrence. -/
theorem advancedReplay_is_sameOccurrence_advance :
    advancedReplay.toOccurrence =
      onePassReplay.toOccurrence.advance
        (fun _ => RootedAccountedUnfolding.zero secondPassTarget) :=
  onePassReplay.toOccurrence_snoc_eq_advance .pass secondPassStep

/-- Direct consumer of explicit generated-player transport: both old
lineages survive, and the second pass appends only to the negative carrier. -/
theorem positive_player_survives_advance :
    (onePassReplay.player .positive).1.events <+:
      (onePassReplay.transportGeneratedPlayerAlongAdvance
        .pass secondPassStep (onePassReplay.player .positive)).1.events :=
  onePassReplay.generatedPlayerLineageSurvivesAdvance
    .pass secondPassStep (onePassReplay.player .positive)

theorem negative_player_survives_advance :
    (onePassReplay.player .negative).1.events <+:
      (onePassReplay.transportGeneratedPlayerAlongAdvance
        .pass secondPassStep (onePassReplay.player .negative)).1.events :=
  onePassReplay.generatedPlayerLineageSurvivesAdvance
    .pass secondPassStep (onePassReplay.player .negative)

theorem advancedReplay_appends_only_negative_lineage :
    advancedReplay.lineageEvents .positive =
        onePassReplay.lineageEvents .positive ∧
      advancedReplay.lineageEvents .negative =
        onePassReplay.lineageEvents .negative ++
          [{ mover := .negative, move := .pass }] := by
  decide

end G2PlayerLineageRegression
end Go
end ProcessGame
end SaturationMonoid
