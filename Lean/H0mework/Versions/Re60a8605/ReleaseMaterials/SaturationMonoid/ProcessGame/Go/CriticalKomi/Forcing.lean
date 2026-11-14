import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.RootedOccurrence
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.ScoreReadout
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.Boolean
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Effects.Memory

/-!
Source-generated one-ply scoring obligations.  Child ports name exact successful
native compiler images; their truth values are retained downstream obligations,
not existentially quantified future outcomes.  Only the mover's choice is folded.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi

open ComplexityProjection.SATSource
open InterferenceProgram

def scoringExpansion {n : Nat} (frame : Frame n) : List (Move n × Frame n) :=
  (legalExpansion (Law.positionalSuperko 0) frame).filter (fun child => child.1 ≠ .resign)

theorem mem_scoringExpansion_iff {n : Nat} {frame target : Frame n} {move : Move n} :
    (move, target) ∈ scoringExpansion frame ↔
      LegalStep (Law.positionalSuperko 0) frame move target ∧ move ≠ .resign := by
  simp [scoringExpansion, mem_legalExpansion_iff]

/-- Integral scoring coordinate; resignation has a separate terminal reason. -/
def areaMargin {n : Nat} (board : Board n) : Int :=
  (areaScore board .positive : Int) - (areaScore board .negative : Int)

def acceptsMargin (beneficiary : Polarity) (threshold margin : Int) : Bool :=
  match beneficiary with
  | .negative => decide (margin ≤ threshold)
  | .positive => decide (threshold ≤ margin)

def terminalGood {n : Nat} (beneficiary : Polarity) (threshold : Int)
    (frame : Frame n) : Bool :=
  frame.visible.status == .terminal .twoPasses &&
    acceptsMargin beneficiary threshold (areaMargin frame.visible.board)

def anyPorts : Nat → Nat → Fragment
  | 0, _ => .constant 0
  | count + 1, offset =>
      ((Fragment.input offset).not.and (anyPorts count (offset + 1)).not).not

def allPorts : Nat → Nat → Fragment
  | 0, _ => .constant 1
  | count + 1, offset =>
      (Fragment.input offset).and (allPorts count (offset + 1))

theorem anyPorts_eval (count offset : Nat) (environment : Nat → Bool) :
    truth ((anyPorts count offset).eval environment) =
      (List.range' offset count).any environment := by
  induction count generalizing offset with
  | zero => rfl
  | succ count ih =>
      simp only [anyPorts, Fragment.eval_not, truth_bit, Fragment.eval_and,
        Fragment.eval_input, ih, Bool.not_and, Bool.not_not, List.range'_succ,
        List.any_cons]

theorem allPorts_eval (count offset : Nat) (environment : Nat → Bool) :
    truth ((allPorts count offset).eval environment) =
      (List.range' offset count).all environment := by
  induction count generalizing offset with
  | zero => rfl
  | succ count ih =>
      simp only [allPorts, Fragment.eval_and, truth_bit, Fragment.eval_input, ih,
        List.range'_succ, List.all_cons]

/-- Only legal play/pass successors receive ports.  An illegal action cannot
turn a universal obligation into a false counterexample. -/
def preimageProgram {n : Nat} (beneficiary : Polarity) (frame : Frame n) : Program :=
  let count := (scoringExpansion frame).length
  (InterferenceDecision.fromAmplitude
    (if frame.visible.toMove = beneficiary then anyPorts count 0 else allPorts count 0)).share

def childEnvironment {n : Nat} (children : List (Move n × Frame n))
    (post : Frame n → Bool) (address : Nat) : Bool :=
  match children[address]? with
  | none => false
  | some child => post child.2

theorem any_childEnvironment {n : Nat} (children : List (Move n × Frame n))
    (post : Frame n → Bool) :
    (List.range' 0 children.length).any (childEnvironment children post) =
      children.any (fun child => post child.2) := by
  apply Bool.eq_iff_iff.mpr
  simp only [← List.range_eq_range', List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨i, inside, good⟩
    refine ⟨children[i], List.getElem_mem inside, ?_⟩
    simpa [childEnvironment, List.getElem?_eq_getElem inside] using good
  · rintro ⟨child, member, good⟩
    obtain ⟨i, inside, same⟩ := List.getElem_of_mem member
    refine ⟨i, inside, ?_⟩
    simpa [childEnvironment, List.getElem?_eq_getElem inside, same] using good

theorem all_childEnvironment {n : Nat} (children : List (Move n × Frame n))
    (post : Frame n → Bool) :
    (List.range' 0 children.length).all (childEnvironment children post) =
      children.all (fun child => post child.2) := by
  apply Bool.eq_iff_iff.mpr
  simp only [← List.range_eq_range', List.all_eq_true, List.mem_range]
  constructor
  · intro all child member
    obtain ⟨i, inside, same⟩ := List.getElem_of_mem member
    simpa [childEnvironment, List.getElem?_eq_getElem inside, same] using all i inside
  · intro all i inside
    simpa [childEnvironment, List.getElem?_eq_getElem inside] using
      all children[i] (List.getElem_mem inside)

theorem preimageProgram_exact {n : Nat} (beneficiary : Polarity) (frame : Frame n)
    (post : Frame n → Bool) :
    truth ((preimageProgram beneficiary frame).eval
      (childEnvironment (scoringExpansion frame) post)) =
      if frame.visible.toMove = beneficiary then
        (scoringExpansion frame).any (fun child => post child.2)
      else (scoringExpansion frame).all (fun child => post child.2) := by
  unfold preimageProgram
  rw [Program.eval_share, InterferenceDecision.eval_fromAmplitude]
  split
  · rw [anyPorts_eval, any_childEnvironment]
  · rw [allPorts_eval, all_childEnvironment]

/-- Native one-ply forcing, with the actual scoring terminal handled before
quantifier folding.  No observation cutoff is an accepting leaf. -/
def forcingRead {n : Nat} (beneficiary : Polarity) (threshold : Int)
    (frame : Frame n) (post : Frame n → Bool) : Bool :=
  match frame.visible.status with
  | .terminal _ => terminalGood beneficiary threshold frame
  | .playing => truth ((preimageProgram beneficiary frame).eval
      (childEnvironment (scoringExpansion frame) post))

theorem preimage_own {n : Nat} (beneficiary : Polarity) (frame : Frame n)
    (post : Frame n → Bool) (owned : frame.visible.toMove = beneficiary) :
    truth ((preimageProgram beneficiary frame).eval
      (childEnvironment (scoringExpansion frame) post)) = true ↔
      ∃ move target, LegalStep (Law.positionalSuperko 0) frame move target ∧
        move ≠ .resign ∧ post target = true := by
  rw [preimageProgram_exact, if_pos owned, List.any_eq_true]
  constructor
  · rintro ⟨⟨move, target⟩, member, good⟩
    exact ⟨move, target, (mem_scoringExpansion_iff.mp member).1,
      (mem_scoringExpansion_iff.mp member).2, good⟩
  · rintro ⟨move, target, step, scoring, good⟩
    exact ⟨(move, target), mem_scoringExpansion_iff.mpr ⟨step, scoring⟩, good⟩

theorem preimage_opponent {n : Nat} (beneficiary : Polarity) (frame : Frame n)
    (post : Frame n → Bool) (opponent : frame.visible.toMove ≠ beneficiary) :
    truth ((preimageProgram beneficiary frame).eval
      (childEnvironment (scoringExpansion frame) post)) = true ↔
      ∀ move target, LegalStep (Law.positionalSuperko 0) frame move target →
        move ≠ .resign → post target = true := by
  rw [preimageProgram_exact, if_neg opponent, List.all_eq_true]
  constructor
  · intro all move target step scoring
    exact all (move, target) (mem_scoringExpansion_iff.mpr ⟨step, scoring⟩)
  · intro all child member
    exact all child.1 child.2 (mem_scoringExpansion_iff.mp member).1
      (mem_scoringExpansion_iff.mp member).2

def chooseGood? {n : Nat} (frame : Frame n) (post : Frame n → Bool) :
    Option (Move n × Frame n) :=
  (scoringExpansion frame).find? (fun child => post child.2)

theorem chooseGood_sound {n : Nat} (frame : Frame n) (post : Frame n → Bool)
    (move : Move n) (target : Frame n)
    (selected : chooseGood? frame post = some (move, target)) :
    LegalStep (Law.positionalSuperko 0) frame move target ∧ move ≠ .resign ∧
      post target = true := by
  have member := List.mem_of_find?_eq_some selected
  have good := List.find?_some selected
  exact ⟨(mem_scoringExpansion_iff.mp member).1,
    (mem_scoringExpansion_iff.mp member).2, good⟩

theorem preimage_retained_read {n : Nat} (beneficiary : Polarity) (frame : Frame n)
    (post : Frame n → Bool) (memory : EffectMemory.Memory) :
    let program := preimageProgram beneficiary frame
    let environment := childEnvironment (scoringExpansion frame) post
    truth (EffectMemory.amplitude program (EffectMemory.observe program environment memory).memory) =
      truth (program.eval environment) ∧
    (EffectMemory.observe program environment
      (EffectMemory.observe program environment memory).memory).computed = 0 := by
  exact ⟨congrArg truth (EffectMemory.observe_read _ _ _),
    (EffectMemory.observe_reuse _ _ _).2⟩

def initialReplay19 : GeneratedReplay (Law.positionalSuperko 0) (Frame.initial 19) [] :=
  .nil _

end SaturationMonoid.ProcessGame.Go.CriticalKomi
