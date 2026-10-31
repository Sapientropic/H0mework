import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Policy.Evaluation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Policy

open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {source : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : source.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (claim : Responsibility.Family.Claim source past nature response)
  (state : Responsibility.Family.State claim) (law : RawLaw Party Good Port Technology Instrument)
  (members : List Party)

theorem accepted_prefix_is_valid_in_the_original_inventory
    {word : RawEvent Party Good Port Technology Instrument}
    (accepted : AcceptedPrefix claim state law members word) :
    ∀ item ∈ law.rawItems state.raw word, law.Valid item.before item.request := by
  induction accepted with
  | nil => simp [RawLaw.rawItems,RawLaw.execute]
  | snoc front request earlier declared standing material valid amount control inherited =>
    change ∀ item ∈ (law.execute state.raw 0 (front ++ [request])).items, _
    rw [law.execute_append]
    simp only [RawLaw.execute,List.mem_append,List.mem_singleton]
    intro item inside
    rcases inside with old | same
    · exact inherited item old
    · subst item
      exact valid

theorem accepted_prefix_retains_its_original_material_source
    {word : RawEvent Party Good Port Technology Instrument}
    (accepted : AcceptedPrefix claim state law members word) :
    ∀ request ∈ word, Responsibility.Family.materialOperation
      (Responsibility.controllerCohort source past nature response)
      (Responsibility.Family.positiveScope source past nature response) request := by
  induction accepted with
  | nil => simp
  | snoc front request earlier declared standing material valid amount control inherited =>
    intro next inside
    rcases List.mem_append.mp inside with old | same
    · exact inherited next old
    · exact (List.mem_singleton.mp same) ▸ material

omit [DecidableEq Instrument] in
private theorem inspect_source_recognizes_the_actual_source
    (cohort : List Party) (victims : List (Party × Good)) (word : RawEvent Party Good Port Technology Instrument)
    (material : ∀ request ∈ word, Responsibility.Family.materialOperation cohort victims request) :
    Responsibility.Family.inspectSource cohort victims word = .accepted material := by
  induction word with
  | nil => rfl
  | cons request rest inherited =>
    simp only [Responsibility.Family.inspectSource,dif_pos (material request List.mem_cons_self)]
    rw [inherited (fun next member => material next (List.mem_cons_of_mem request member))]

omit [DecidableEq Instrument] in
private theorem inspect_material_recognizes_the_actual_inventory
    (items : List (ExecutionItem Party Good Port Technology Instrument))
    (valid : ∀ item ∈ items, law.Valid item.before item.request) :
    Responsibility.inspectMaterial law items = .accepted valid := by
  induction items with
  | nil => rfl
  | cons item rest inherited =>
    simp only [Responsibility.inspectMaterial,dif_pos (valid item List.mem_cons_self)]
    rw [inherited (fun next member => valid next (List.mem_cons_of_mem item member))]

variable {proposal : RawEvent Party Good Port Technology Instrument}

theorem evaluation_is_the_same_accepted_actual_attempt
    (evaluation : Evaluation claim state law members proposal) :
    Responsibility.Family.State.attempt claim state law evaluation.executableWord =
      .accepted
        (accepted_prefix_is_valid_in_the_original_inventory claim state law members evaluation.accepted)
        (accepted_prefix_retains_its_original_material_source claim state law members evaluation.accepted) := by
  unfold Responsibility.Family.State.attempt Responsibility.Family.inspectAttempt
  rw [inspect_source_recognizes_the_actual_source _ _ _
      (accepted_prefix_retains_its_original_material_source claim state law members evaluation.accepted),
    inspect_material_recognizes_the_actual_inventory law _
      (accepted_prefix_is_valid_in_the_original_inventory claim state law members evaluation.accepted)]

theorem evaluation_actual_word_is_the_original_executable_word
    (evaluation : Evaluation claim state law members proposal) : evaluation.actualWord = evaluation.executableWord := by
  unfold Evaluation.actualWord
  rw [evaluation_is_the_same_accepted_actual_attempt claim state law members evaluation]
  rfl

theorem evaluation_updates_the_original_physical_cursor
    (evaluation : Evaluation claim state law members proposal) :
    evaluation.updated.raw = law.next state.raw evaluation.executableWord := by
  change (Responsibility.Family.State.attempt claim state law evaluation.executableWord).cursor = _
  rw [evaluation_is_the_same_accepted_actual_attempt claim state law members evaluation]
  rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Policy
