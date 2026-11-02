import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Quantified
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Reserve

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Open

open Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (code : Code Party Good Port Technology Instrument)

structure Control (Technology : Type) where
  technology : Technology
  clock : ℚ
  round : Nat
  deriving DecidableEq

def terminal (policy : code.Policy) (history : History (Party := Party) (Good := Good)
    (Port := Port) (Technology := Technology) (Instrument := Instrument)) (opponent : Opponent code) :=
  code.law.next (code.historyCurrent history) (execution code policy history opponent).word

def control (policy : code.Policy) (history : History (Party := Party) (Good := Good)
    (Port := Port) (Technology := Technology) (Instrument := Instrument)) (opponent : Opponent code) : Control Technology :=
  let after := terminal code policy history opponent
  ⟨after.technology, after.clock, after.round⟩

inductive Axis where
  | raw (axis : Reaction.Axis code)
  | control (history : History (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument)) (table : Table code) (anchor : Control Technology)

def axes : List (Axis code) := (Reaction.axes code).map .raw ++
  code.histories.flatMap fun history => (tables code).flatMap fun table =>
    code.policies.map fun policy => .control history table (control code policy history (respond code table))

def cost (policy : code.Policy) : Axis code → ℚ
  | .raw axis => Reaction.cost code policy axis
  | .control history table anchor => if control code policy history (respond code table) = anchor then 0 else 1

abbrev NonRegression (new old : code.Policy) := NoWorse (axes code) (cost code) new old
abbrev Better (old new : code.Policy) := Improves (axes code) (cost code) old new

theorem control_axis_is_generated (policy : code.Policy) (generated : policy ∈ code.policies)
    (history : History (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
    (original : history ∈ code.histories) (table : Table code) (tableGenerated : table ∈ tables code) :
    Axis.control history table (control code policy history (respond code table)) ∈ axes code := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨history, original, List.mem_flatMap.mpr ⟨table, tableGenerated, ?_⟩⟩
  exact List.mem_map.mpr ⟨policy, generated, rfl⟩

theorem comparison_iff (new old : code.Policy) (oldGenerated : old ∈ code.policies) :
    NonRegression code new old ↔ Reaction.NonRegression code new old ∧
      ∀ history ∈ code.histories, ∀ table ∈ tables code,
        control code new history (respond code table) = control code old history (respond code table) := by
  constructor
  · intro bounded
    refine ⟨fun axis inside => bounded (.raw axis) (List.mem_append_left _ (List.mem_map.mpr ⟨axis, inside, rfl⟩)), ?_⟩
    intro history original table generated
    have checked := bounded _ (control_axis_is_generated code old oldGenerated history original table generated)
    simp only [cost] at checked
    split at checked
    next same => exact same
    next => norm_num at checked
  · rintro ⟨raw, controls⟩ axis inside
    rcases List.mem_append.mp inside with rawAxis | controlAxis
    · obtain ⟨coordinate, original, rfl⟩ := List.mem_map.mp rawAxis
      exact raw coordinate original
    · obtain ⟨history, original, inner⟩ := List.mem_flatMap.mp controlAxis
      obtain ⟨table, generated, inner⟩ := List.mem_flatMap.mp inner
      obtain ⟨policy, _, rfl⟩ := List.mem_map.mp inner
      simp only [cost, controls history original table generated, le_refl]


/-- Equality guards cannot mint a strict dividend. Strict improvement must
occur in the original material, financial, clock or admissibility vector. -/
theorem strictness_iff_original_vector (old new : code.Policy)
    (oldGenerated : old ∈ code.policies) (newGenerated : new ∈ code.policies) :
    Better code old new ↔ Reaction.Better code old new ∧
      ∀ history ∈ code.histories, ∀ table ∈ tables code,
        control code new history (respond code table) = control code old history (respond code table) := by
  constructor
  · rintro ⟨forward, strict⟩
    obtain ⟨raw, controls⟩ := (comparison_iff code new old oldGenerated).mp forward
    refine ⟨⟨raw, ?_⟩, controls⟩
    intro backward
    apply strict
    exact (comparison_iff code old new newGenerated).mpr
      ⟨backward, fun history original table generated => (controls history original table generated).symm⟩
  · rintro ⟨⟨raw, strict⟩, controls⟩
    refine ⟨(comparison_iff code new old oldGenerated).mpr ⟨raw, controls⟩, ?_⟩
    intro backward
    exact strict ((comparison_iff code old new newGenerated).mp backward).1

def AgainstEveryOpponent (new old : code.Policy) : Prop :=
  Reaction.AgainstEveryOpponent code new old ∧
    ∀ opponent : Opponent code, ∀ history ∈ code.histories,
      control code new history opponent = control code old history opponent

theorem finite_comparison_iff_every_same_opponent (new old : code.Policy)
    (newGenerated : new ∈ code.policies) (oldGenerated : old ∈ code.policies) :
    NonRegression code new old ↔ AgainstEveryOpponent code new old := by
  rw [comparison_iff code new old oldGenerated]
  constructor
  · rintro ⟨raw, controls⟩
    refine ⟨(Reaction.finite_comparison_iff_every_same_opponent code new old newGenerated oldGenerated).mp raw, ?_⟩
    intro opponent history original
    obtain ⟨table, generated, same⟩ := every_history_adaptive_opponent_has_one_joint_table code opponent
    have checked := controls history original table generated
    simpa only [control, terminal, execution, same new newGenerated history original,
      same old oldGenerated history original] using checked
  · rintro ⟨raw, controls⟩
    exact ⟨(Reaction.finite_comparison_iff_every_same_opponent code new old newGenerated oldGenerated).mpr raw,
      fun history original table _ => controls (respond code table) history original⟩


def StrictAgainstEveryOpponent (old new : code.Policy) : Prop :=
  AgainstEveryOpponent code new old ∧ ¬ AgainstEveryOpponent code old new

theorem finite_strictness_iff_every_same_opponent (old new : code.Policy)
    (oldGenerated : old ∈ code.policies) (newGenerated : new ∈ code.policies) :
    Better code old new ↔ StrictAgainstEveryOpponent code old new :=
  and_congr (finite_comparison_iff_every_same_opponent code new old newGenerated oldGenerated)
    (not_congr (finite_comparison_iff_every_same_opponent code old new oldGenerated newGenerated))

def reserve (new old : code.Policy) (history : History (Party := Party) (Good := Good)
    (Port := Port) (Technology := Technology) (Instrument := Instrument)) (opponent : Opponent code) :=
  fun party good => (terminal code new history opponent).stock party good - (terminal code old history opponent).stock party good

theorem generated_full_carrier_extension (new old : code.Policy)
    (newGenerated : new ∈ code.policies) (oldGenerated : old ∈ code.policies)
    (bounded : NonRegression code new old) (opponent : Opponent code)
    (history : History (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
    (original : history ∈ code.histories) :
    (∀ party good, 0 ≤ reserve code new old history opponent party good) ∧
      terminal code new history opponent = (terminal code old history opponent).addReserve (reserve code new old history opponent) := by
  have checked := (finite_comparison_iff_every_same_opponent code new old newGenerated oldGenerated).mp bounded
  have inventory (party : Party) (good : Good) := checked.1 opponent history original (.raw (.inventory party good))
  have shares (instrument : Instrument) (debtor creditor : Party) :=
    checked.1 opponent history original (.raw (.liability instrument debtor creditor))
  have claims (instrument : Instrument) (debtor creditor : Party) :=
    checked.1 opponent history original (.raw (.claim instrument debtor creditor))
  have controls := checked.2 opponent history original
  have tech := congrArg Control.technology controls
  have clock := congrArg Control.clock controls
  have round := congrArg Control.round controls
  dsimp only [control] at tech clock round
  refine ⟨?_, ?_⟩
  · intro party good
    have enough := inventory party good
    change -(terminal code new history opponent).stock party good ≤ -(terminal code old history opponent).stock party good at enough
    dsimp [reserve]; linarith
  · apply RawCurrent.ext
    · funext party good
      simp [RawCurrent.addReserve, reserve]
    · funext instrument debtor creditor
      have a := shares instrument debtor creditor
      have b := claims instrument debtor creditor
      change (terminal code new history opponent).claims instrument debtor creditor ≤
        (terminal code old history opponent).claims instrument debtor creditor at a
      change -(terminal code new history opponent).claims instrument debtor creditor ≤
        -(terminal code old history opponent).claims instrument debtor creditor at b
      change (terminal code new history opponent).claims instrument debtor creditor =
        (terminal code old history opponent).claims instrument debtor creditor
      linarith
    · exact tech
    · exact clock
    · exact round

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Open
