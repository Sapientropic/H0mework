import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Trace

/-!
# Joint authority from actual internal consents

The producer searches the source's actual permissions for a signer in the
given generated group, retains only original group consents, and rechecks every step.
It retains the original operations.  Its output is a lawful alternative,
not a replacement for the actual history or its original bearers.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program

universe u

variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

def Request.jointlyAuthorize (request : Request Party Good Port Technology Instrument) (group : List Party) (signer : Party) :
    Request Party Good Port Technology Instrument :=
  { request with signer := signer, consents := request.consents.filter (fun person => decide (person ∈ group)) }

omit [DecidableEq Good] [DecidableEq Instrument] in
theorem Request.jointlyAuthorize_consents (request : Request Party Good Port Technology Instrument)
    (group : List Party) (signer person : Party)
    (inside : person ∈ (request.jointlyAuthorize group signer).consents) :
    person ∈ request.consents ∧ person ∈ group := by
  simpa only [Request.jointlyAuthorize, List.mem_filter, decide_eq_true_eq] using inside

omit [DecidableEq Good] [DecidableEq Instrument] in
theorem Request.jointlyAuthorize_self (request : Request Party Good Port Technology Instrument)
    (group : List Party) (internal : ∀ person ∈ request.consents, person ∈ group) :
    request.jointlyAuthorize group request.signer = request := by
  have kept : request.consents.filter (fun person => decide (person ∈ group)) = request.consents := by
    apply List.filter_eq_self.mpr
    intro person inside
    exact decide_eq_true (internal person inside)
  unfold Request.jointlyAuthorize
  rw [kept]

namespace RawLaw

variable (law : RawLaw Party Good Port Technology Instrument)

theorem paidStep_jointlyAuthorize (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) (group : List Party) (signer : Party) :
    law.paidStep current (request.jointlyAuthorize group signer) = law.paidStep current request := rfl

theorem accepted_jointlyAuthorize_same_effect (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) (group : List Party) (signer : Party)
    (original : law.Valid current request) (independent : law.Valid current (request.jointlyAuthorize group signer)) :
    law.step current (request.jointlyAuthorize group signer) = law.step current request := by
  simp only [step, if_pos original, if_pos independent, paidStep_jointlyAuthorize]

def jointSigner (group : List Party) (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) : Option Party :=
  group.find? (fun signer => decide (law.Valid current (request.jointlyAuthorize group signer)))

omit [DecidableEq Instrument] in
theorem jointSigner_sound (group : List Party)
    (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) (signer : Party)
    (found : law.jointSigner group current request = some signer) :
    signer ∈ group ∧ law.Valid current (request.jointlyAuthorize group signer) := by
  have tested : decide (law.Valid current (request.jointlyAuthorize group signer)) = true :=
    List.find?_some (p := fun member => decide (law.Valid current (request.jointlyAuthorize group member))) found
  exact ⟨List.mem_of_find?_eq_some found, of_decide_eq_true tested⟩

/-- Every accepted instruction is rechecked after the preceding actual
effects.  Failed authorization returns no independent programme. -/
def jointWord (group : List Party) (current : RawCurrent Party Good Technology Instrument) :
    RawEvent Party Good Port Technology Instrument → Option (RawEvent Party Good Port Technology Instrument)
  | [] => some []
  | request :: tail =>
      if law.Valid current request then
        match law.jointSigner group current request with
        | none => none
        | some signer =>
            (jointWord group (law.step current request) tail).map
              (request.jointlyAuthorize group signer :: ·)
      else none

theorem jointWord_sound (group : List Party)
    (current : RawCurrent Party Good Technology Instrument)
    (original independent : RawEvent Party Good Port Technology Instrument)
    (produced : law.jointWord group current original = some independent) (index : Nat) :
    (law.execute current index independent).final = (law.execute current index original).final ∧
    (∀ item ∈ (law.execute current index independent).items,
      law.Valid item.before item.request ∧ item.request.signer ∈ group ∧ ∀ person ∈ item.request.consents, person ∈ group) ∧
    independent.map Request.operation = original.map Request.operation := by
  induction original generalizing current independent index with
  | nil =>
      have empty : independent = [] := Option.some.inj produced |>.symm
      subst independent
      exact ⟨rfl, by simp [execute], rfl⟩
  | cons request tail ih =>
      by_cases accepted : law.Valid current request
      · simp only [jointWord, if_pos accepted] at produced
        cases found : law.jointSigner group current request with
        | none => simp only [found] at produced; contradiction
        | some signer =>
            simp only [found] at produced
            cases rest : law.jointWord group (law.step current request) tail with
            | none => simp only [rest, Option.map_none] at produced; contradiction
            | some remaining =>
                simp only [rest, Option.map_some] at produced
                have exactWord := Option.some.inj produced
                subst independent
                obtain ⟨member, legal⟩ := law.jointSigner_sound group current request signer found
                have sameStep := law.accepted_jointlyAuthorize_same_effect current request group signer accepted legal
                obtain ⟨sameFinal, allLegal, sameOperations⟩ := ih _ _ rest (index + 1)
                simp only [execute, sameStep, List.forall_mem_cons, List.map_cons]
                exact ⟨sameFinal, ⟨⟨legal, member, fun person present =>
                    (request.jointlyAuthorize_consents group signer person present).2⟩, allLegal⟩,
                  congrArg (request.operation :: ·) sameOperations⟩
      · simp only [jointWord, if_neg accepted] at produced
        contradiction

theorem jointWord_same_next (group : List Party)
    (current : RawCurrent Party Good Technology Instrument)
    (original independent : RawEvent Party Good Port Technology Instrument)
    (produced : law.jointWord group current original = some independent) :
    law.next current independent = law.next current original := by
  unfold next
  rw [(law.jointWord_sound group current original independent produced 0).1]

/-- Failure is localized to an original instruction.  This is an authority
obstruction for this word, not a claim that no alternative livelihood exists. -/
theorem jointWord_failure_original (group : List Party)
    (current : RawCurrent Party Good Technology Instrument)
    (original : RawEvent Party Good Port Technology Instrument)
    (failed : law.jointWord group current original = none) (index : Nat) :
    ∃ item ∈ (law.execute current index original).items,
      ¬ law.Valid item.before item.request ∨
        ∀ signer ∈ group, ¬ law.Valid item.before (item.request.jointlyAuthorize group signer) := by
  induction original generalizing current index with
  | nil => contradiction
  | cons request tail ih =>
      by_cases accepted : law.Valid current request
      · simp only [jointWord, if_pos accepted] at failed
        cases found : law.jointSigner group current request with
        | none =>
            refine ⟨⟨index, current, request⟩, List.mem_cons_self, Or.inr ?_⟩
            simpa [jointSigner] using found
        | some signer =>
            simp only [found, Option.map_eq_none_iff] at failed
            obtain ⟨item, member, blocked⟩ := ih _ failed (index + 1)
            exact ⟨item, List.mem_cons_of_mem _ member, blocked⟩
      · exact ⟨⟨index, current, request⟩, List.mem_cons_self, Or.inl accepted⟩

theorem jointWord_complete (group : List Party)
    (current : RawCurrent Party Good Technology Instrument)
    (original : RawEvent Party Good Port Technology Instrument)
    (locallyExecutable : ∀ item ∈ law.rawItems current original,
      law.Valid item.before item.request ∧
        ∃ signer ∈ group, law.Valid item.before (item.request.jointlyAuthorize group signer)) :
    law.jointWord group current original ≠ none := by
  intro failed
  obtain ⟨item, member, rejected | blocked⟩ :=
    law.jointWord_failure_original group current original failed 0
  · exact rejected (locallyExecutable item member).1
  · obtain ⟨signer, inside, legal⟩ := (locallyExecutable item member).2
    exact blocked signer inside legal

theorem jointWord_of_internal_execution (group : List Party)
    (current : RawCurrent Party Good Technology Instrument)
    (original : RawEvent Party Good Port Technology Instrument)
    (internal : ∀ item ∈ law.rawItems current original,
      law.Valid item.before item.request ∧ item.request.signer ∈ group ∧
        ∀ person ∈ item.request.consents, person ∈ group) :
    law.jointWord group current original ≠ none := by
  apply law.jointWord_complete
  intro item inside
  obtain ⟨legal, signer, consents⟩ := internal item inside
  refine ⟨legal, item.request.signer, signer, ?_⟩
  rwa [item.request.jointlyAuthorize_self group consents]

#print axioms jointWord_sound
#print axioms jointWord_same_next
#print axioms jointWord_failure_original

end RawLaw
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program
