import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Lineage.GeneratedActorGaugeQuotient
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.GoProcessGameRegression

/-!
# Go consumer of generated-actor maximality

The canonical trace-seed gauge quotient at the exact two-pass Go occurrence
maps bijectively to the existing G2 generated-player carrier.  The quotient
does not replace Go player lineage; it classifies the generic actor image
before the existing goGeneratedActorEquiv readout.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Regression
namespace Society
namespace GoGeneratedActorMaximalityRegression

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Go
open GoProcessGameRegression

abbrev GoTraceSeedGauge :=
  TraceSeedGauge game Polarity goSeedAt goLineage goLineageOf

def goGaugeToGeneratedPlayer :
    GoTraceSeedGauge → GeneratedReplay.GeneratedPlayer replay :=
  fun gauge =>
    goGeneratedActorEquiv replay
      (gaugeToActor game Polarity goSeedAt goLineage goLineageOf gauge)

def positiveGauge : GoTraceSeedGauge :=
  traceSeedGaugeMk game Polarity goSeedAt goLineage goLineageOf positiveSeed

def negativeGauge : GoTraceSeedGauge :=
  traceSeedGaugeMk game Polarity goSeedAt goLineage goLineageOf negativeSeed

theorem go_dancing_generates_dancers :
    DancingGeneratesDancers game Polarity goSeedAt goLineage goLineageOf :=
  dancingGeneratesDancers game Polarity goSeedAt goLineage goLineageOf

theorem go_gauge_to_existing_generatedPlayer_is_bijective :
    Function.Bijective goGaugeToGeneratedPlayer := by
  have gaugeBijective :=
    gaugeToActor_bijective game Polarity goSeedAt goLineage goLineageOf
  constructor
  · intro left right playersEqual
    apply gaugeBijective.1
    apply (goGeneratedActorEquiv replay).injective
    exact playersEqual
  · intro player
    rcases (goGeneratedActorEquiv replay).surjective player with
      ⟨actor, actorImage⟩
    rcases gaugeBijective.2 actor with ⟨gauge, gaugeImage⟩
    refine ⟨gauge, ?_⟩
    change goGeneratedActorEquiv replay
      (gaugeToActor game Polarity goSeedAt goLineage goLineageOf gauge) = player
    rw [gaugeImage, actorImage]

theorem positive_negative_gauges_read_as_existing_players :
    goGaugeToGeneratedPlayer positiveGauge = replay.player .positive ∧
      goGaugeToGeneratedPlayer negativeGauge = replay.player .negative := by
  exact ⟨goGeneratedActorEquiv_generatedActorOf replay .positive,
    goGeneratedActorEquiv_generatedActorOf replay .negative⟩

theorem positive_negative_gauge_classes_are_distinct :
    positiveGauge ≠ negativeGauge := by
  intro gaugesEqual
  have playersEqual := congrArg goGaugeToGeneratedPlayer gaugesEqual
  rw [positive_negative_gauges_read_as_existing_players.1,
    positive_negative_gauges_read_as_existing_players.2] at playersEqual
  exact replay.generatedPlayerEquiv.injective.ne (by decide) playersEqual

theorem both_gauge_classes_retain_same_root_trace_provenance :
    (∃ state ∈ game.occurrence.trace,
      goSeedAt replay state positiveSeed.1) ∧
      (∃ state ∈ game.occurrence.trace,
        goSeedAt replay state negativeSeed.1) :=
  ⟨positiveSeed.2, negativeSeed.2⟩

end GoGeneratedActorMaximalityRegression
end Society
end Regression
end ProcessGame
end SaturationMonoid
