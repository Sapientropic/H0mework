import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.Forcing
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.Survival
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.PositionExecution

/-!
Compile a proved native Boolean invariant into the executable survival consumer.
The local closure proof remains the domain construction obligation; own moves
are computed from the original legal expansion, not supplied in that proof.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi

open ComplexityProjection.SATSource.InterferenceProgram

theorem chooseGood_exists {n : Nat} (frame : Frame n) (post : Frame n → Bool)
    (available : ∃ move target, LegalStep (Law.positionalSuperko 0) frame move target ∧
      move ≠ .resign ∧ post target = true) :
    ∃ child, chooseGood? frame post = some child := by
  obtain ⟨move, target, step, scoring, good⟩ := available
  have anyGood : (scoringExpansion frame).any (fun child => post child.2) = true :=
    List.any_eq_true.mpr ⟨(move, target), mem_scoringExpansion_iff.mpr ⟨step, scoring⟩, good⟩
  have someGood : (chooseGood? frame post).isSome = true := by
    simpa [chooseGood?, List.isSome_find?] using anyGood
  exact Option.isSome_iff_exists.mp someGood

def forcedReply {n : Nat} (beneficiary : Polarity) (frame : Frame n)
    (post : Frame n → Bool) (owned : frame.visible.toMove = beneficiary)
    (winning : truth ((preimageProgram beneficiary frame).eval
      (childEnvironment (scoringExpansion frame) post)) = true) : ScoringReply frame :=
  match chosen : chooseGood? frame post with
  | some child =>
      let facts := chooseGood_sound frame post child.1 child.2 chosen
      ⟨child.1, child.2, facts.2.1, facts.1⟩
  | none => False.elim (by
      obtain ⟨child, found⟩ := chooseGood_exists frame post
        ((preimage_own beneficiary frame post owned).mp winning)
      rw [chosen] at found
      contradiction)

theorem forcedReply_good {n : Nat} (beneficiary : Polarity) (frame : Frame n)
    (post : Frame n → Bool) (owned : frame.visible.toMove = beneficiary)
    (winning : truth ((preimageProgram beneficiary frame).eval
      (childEnvironment (scoringExpansion frame) post)) = true) :
    post (forcedReply beneficiary frame post owned winning).target = true := by
  unfold forcedReply
  split
  · rename_i child chosen
    exact (chooseGood_sound frame post child.1 child.2 chosen).2.2
  · contradiction

/-- This is the exact proof obligation over a proposed source Boolean relation. -/
def ClosedUnderNativeForcing {n : Nat} (beneficiary : Polarity) (threshold : Int)
    (invariant : Frame n → Bool) : Prop :=
  ∀ frame, invariant frame = true → forcingRead beneficiary threshold frame invariant = true

/-- Conditional compiler: local source laws supply closure; the compiler supplies executable moves. -/
def compileSurvival {n : Nat} (beneficiary : Polarity) (threshold : Int)
    (invariant : Frame n → Bool)
    (closed : ClosedUnderNativeForcing beneficiary threshold invariant) :
    SurvivalClosure beneficiary (fun frame => invariant frame = true)
      (fun frame => acceptsMargin beneficiary threshold (areaMargin frame.visible.board) = true) where
  ownReply frame inside owned playing :=
    forcedReply beneficiary frame invariant owned (by
      simpa only [forcingRead, playing] using closed frame inside)
  own_preserved frame inside owned playing :=
    forcedReply_good beneficiary frame invariant owned _
  opponent_preserved inside opponent scoring step := by
    have playing := nonresigning_step_playing scoring step
    have forced := closed _ inside
    simp only [forcingRead, playing] at forced
    exact (preimage_opponent _ _ _ opponent).mp forced _ _ step scoring
  finished inside terminal := by
    have forced := closed _ inside
    simpa only [forcingRead, terminal, terminalGood, beq_self_eq_true, Bool.true_and] using forced

/-- A source proof on the positional face feeds the very same whole-play consumer. -/
def compileFaceSurvival {n : Nat} (beneficiary : Polarity) (threshold : Int)
    (invariant : PositionFace.State n → Bool)
    (closed : ∀ frame, invariant (PositionFace.read frame) = true →
      forcingRead beneficiary threshold frame (invariant ∘ PositionFace.read) = true) :=
  compileSurvival beneficiary threshold (invariant ∘ PositionFace.read) closed

/-- The exact delivery mouth: a concrete integer and two programs with unilateral full-play bounds. -/
structure ExactInitialMargin where
  value : Int
  white : ExecutablePolicy 19
  black : ExecutablePolicy 19
  white_guarantee : ∀ opponent : ExecutablePolicy 19,
    areaMargin (initialPlay 19 (versus .negative white opponent)).replay.final.visible.board ≤ value
  black_guarantee : ∀ opponent : ExecutablePolicy 19,
    value ≤ areaMargin (initialPlay 19 (versus .positive black opponent)).replay.final.visible.board

end SaturationMonoid.ProcessGame.Go.CriticalKomi
