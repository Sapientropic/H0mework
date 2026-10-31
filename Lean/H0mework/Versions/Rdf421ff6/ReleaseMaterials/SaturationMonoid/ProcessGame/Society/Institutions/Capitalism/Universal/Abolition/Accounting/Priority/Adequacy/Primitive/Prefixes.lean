import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Primitive.Envelope

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Primitive

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

theorem execute_append (law : RawLaw Party Good Port Technology Instrument)
    (initial : RawCurrent Party Good Technology Instrument) (index : Nat)
    (front rest : RawEvent Party Good Port Technology Instrument) :
    execute law initial index (front ++ rest) =
      let earlier := execute law initial index front
      let later := execute law earlier.final (index + front.length) rest
      ⟨later.final,earlier.items ++ later.items⟩ := by
  induction front generalizing initial index with
  | nil => simp [execute]
  | cons request tail inherited =>
    simp only [List.cons_append,execute,inherited,List.length_cons]
    have same : index + 1 + tail.length = index + (tail.length + 1) := by omega
    rw [same]

theorem prefix_conditions (law : RawLaw Party Good Port Technology Instrument)
    (initial : RawCurrent Party Good Technology Instrument)
    (front rest : RawEvent Party Good Port Technology Instrument)
    (conditions : Conditions law (execute law initial 0 (front ++ rest)).items) :
    Conditions law (execute law initial 0 front).items := by
  apply conditions.restrict
  rw [execute_append]
  exact fun _ member => List.mem_append_left _ member

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] in
def stepsFrom (front : RawEvent Party Good Port Technology Instrument) :
    RawEvent Party Good Port Technology Instrument →
      List (RawEvent Party Good Port Technology Instrument × Request Party Good Port Technology Instrument)
  | [] => []
  | request :: rest => (front,request) :: stepsFrom (front ++ [request]) rest

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] in
def steps (word : RawEvent Party Good Port Technology Instrument) := stepsFrom [] word

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] in
theorem source_decomposition_is_a_generated_step
    (outer front : RawEvent Party Good Port Technology Instrument)
    (request : Request Party Good Port Technology Instrument) (rest : RawEvent Party Good Port Technology Instrument) :
    (outer ++ front,request) ∈ stepsFrom outer (front ++ request :: rest) := by
  induction front generalizing outer with
  | nil => simp [stepsFrom]
  | cons head tail inherited =>
    simp only [List.cons_append,stepsFrom,List.mem_cons]
    right
    simpa only [List.append_assoc,List.singleton_append] using inherited (outer ++ [head])

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] in
theorem every_source_step_is_a_decomposition
    (outer word : RawEvent Party Good Port Technology Instrument)
    (pair : RawEvent Party Good Port Technology Instrument × Request Party Good Port Technology Instrument)
    (member : pair ∈ stepsFrom outer word) :
    ∃ middle rest, pair.1 = outer ++ middle ∧ word = middle ++ pair.2 :: rest := by
  induction word generalizing outer with
  | nil => cases member
  | cons request tail inherited =>
    rcases List.mem_cons.mp member with same | later
    · cases same
      exact ⟨[],tail,by simp,rfl⟩
    · obtain ⟨middle,rest,frontEq,wordEq⟩ := inherited (outer ++ [request]) later
      refine ⟨request :: middle,rest,?_,?_⟩
      · simpa only [List.append_assoc,List.singleton_append] using frontEq
      · simp only [wordEq,List.cons_append]

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Primitive
