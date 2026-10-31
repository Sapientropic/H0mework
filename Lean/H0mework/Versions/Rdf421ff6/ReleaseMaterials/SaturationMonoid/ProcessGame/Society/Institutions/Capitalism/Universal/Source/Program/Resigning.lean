import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Trace

/-!
# Executable independent versions of original finite programmes

The producer searches the source's actual permissions for a signer in the
given generated group, removes external consents, and rechecks every step.
It retains the original operations.  Its output is a lawful alternative,
not a replacement for the actual history or its original bearers.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program

universe u

variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

def Request.resign (request : Request Party Good Port Technology Instrument) (signer : Party) :
    Request Party Good Port Technology Instrument :=
  { request with signer := signer, consents := [] }

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] in
theorem Request.resign_self (request : Request Party Good Port Technology Instrument)
    (noExternalConsent : request.consents = []) : request.resign request.signer = request := by
  cases request
  simp_all [Request.resign]

namespace RawLaw

variable (law : RawLaw Party Good Port Technology Instrument)

theorem paidStep_resign (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) (signer : Party) :
    law.paidStep current (request.resign signer) = law.paidStep current request := rfl

theorem accepted_resign_same_effect (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) (signer : Party)
    (original : law.Valid current request) (independent : law.Valid current (request.resign signer)) :
    law.step current (request.resign signer) = law.step current request := by
  simp only [step, if_pos original, if_pos independent, paidStep_resign]

def independentSigner (group : List Party) (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) : Option Party :=
  group.find? (fun signer => decide (law.Valid current (request.resign signer)))

omit [DecidableEq Instrument] in
theorem independentSigner_sound (group : List Party)
    (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) (signer : Party)
    (found : law.independentSigner group current request = some signer) :
    signer ∈ group ∧ law.Valid current (request.resign signer) := by
  have tested : decide (law.Valid current (request.resign signer)) = true :=
    List.find?_some (p := fun member => decide (law.Valid current (request.resign member))) found
  exact ⟨List.mem_of_find?_eq_some found, of_decide_eq_true tested⟩

/-- Every accepted instruction is rechecked after the preceding actual
effects.  Failed authorization returns no independent programme. -/
def independentWord (group : List Party) (current : RawCurrent Party Good Technology Instrument) :
    RawEvent Party Good Port Technology Instrument → Option (RawEvent Party Good Port Technology Instrument)
  | [] => some []
  | request :: tail =>
      if law.Valid current request then
        match law.independentSigner group current request with
        | none => none
        | some signer =>
            (independentWord group (law.step current request) tail).map
              (request.resign signer :: ·)
      else none

theorem independentWord_sound (group : List Party)
    (current : RawCurrent Party Good Technology Instrument)
    (original independent : RawEvent Party Good Port Technology Instrument)
    (produced : law.independentWord group current original = some independent) (index : Nat) :
    (law.execute current index independent).final = (law.execute current index original).final ∧
    (∀ item ∈ (law.execute current index independent).items,
      law.Valid item.before item.request ∧ item.request.signer ∈ group ∧ item.request.consents = []) ∧
    independent.map Request.operation = original.map Request.operation := by
  induction original generalizing current independent index with
  | nil =>
      have empty : independent = [] := Option.some.inj produced |>.symm
      subst independent
      exact ⟨rfl, by simp [execute], rfl⟩
  | cons request tail ih =>
      by_cases accepted : law.Valid current request
      · simp only [independentWord, if_pos accepted] at produced
        cases found : law.independentSigner group current request with
        | none => simp only [found] at produced; contradiction
        | some signer =>
            simp only [found] at produced
            cases rest : law.independentWord group (law.step current request) tail with
            | none => simp only [rest, Option.map_none] at produced; contradiction
            | some remaining =>
                simp only [rest, Option.map_some] at produced
                have exactWord := Option.some.inj produced
                subst independent
                obtain ⟨member, legal⟩ := law.independentSigner_sound group current request signer found
                have sameStep := law.accepted_resign_same_effect current request signer accepted legal
                obtain ⟨sameFinal, allLegal, sameOperations⟩ := ih _ _ rest (index + 1)
                simp only [execute, sameStep, List.forall_mem_cons, List.map_cons]
                exact ⟨sameFinal, ⟨⟨legal, member, rfl⟩, allLegal⟩,
                  congrArg (request.operation :: ·) sameOperations⟩
      · simp only [independentWord, if_neg accepted] at produced
        contradiction

theorem independentWord_same_next (group : List Party)
    (current : RawCurrent Party Good Technology Instrument)
    (original independent : RawEvent Party Good Port Technology Instrument)
    (produced : law.independentWord group current original = some independent) :
    law.next current independent = law.next current original := by
  unfold next
  rw [(law.independentWord_sound group current original independent produced 0).1]

/-- Failure is localized to an original instruction.  This is an authority
obstruction for this word, not a claim that no alternative livelihood exists. -/
theorem independentWord_failure_original (group : List Party)
    (current : RawCurrent Party Good Technology Instrument)
    (original : RawEvent Party Good Port Technology Instrument)
    (failed : law.independentWord group current original = none) (index : Nat) :
    ∃ item ∈ (law.execute current index original).items,
      ¬ law.Valid item.before item.request ∨
        ∀ signer ∈ group, ¬ law.Valid item.before (item.request.resign signer) := by
  induction original generalizing current index with
  | nil => contradiction
  | cons request tail ih =>
      by_cases accepted : law.Valid current request
      · simp only [independentWord, if_pos accepted] at failed
        cases found : law.independentSigner group current request with
        | none =>
            refine ⟨⟨index, current, request⟩, List.mem_cons_self, Or.inr ?_⟩
            simpa [independentSigner] using found
        | some signer =>
            simp only [found, Option.map_eq_none_iff] at failed
            obtain ⟨item, member, blocked⟩ := ih _ failed (index + 1)
            exact ⟨item, List.mem_cons_of_mem _ member, blocked⟩
      · exact ⟨⟨index, current, request⟩, List.mem_cons_self, Or.inl accepted⟩

theorem independentWord_complete (group : List Party)
    (current : RawCurrent Party Good Technology Instrument)
    (original : RawEvent Party Good Port Technology Instrument)
    (locallyExecutable : ∀ item ∈ law.rawItems current original,
      law.Valid item.before item.request ∧
        ∃ signer ∈ group, law.Valid item.before (item.request.resign signer)) :
    law.independentWord group current original ≠ none := by
  intro failed
  obtain ⟨item, member, rejected | blocked⟩ :=
    law.independentWord_failure_original group current original failed 0
  · exact rejected (locallyExecutable item member).1
  · obtain ⟨signer, inside, legal⟩ := (locallyExecutable item member).2
    exact blocked signer inside legal

#print axioms independentWord_sound
#print axioms independentWord_same_next
#print axioms independentWord_failure_original

end RawLaw
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program
