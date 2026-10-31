import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Capacity.Inspection.Recipe

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Capacity

open Source.Program Innovation Inspection

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  [DecidableEq Technology] [DecidableEq Port]
  {source : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : source.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (claim : Responsibility.Family.Claim source past nature response)
  (state : Responsibility.Family.State claim) (law : RawLaw Party Good Port Technology Instrument)
  (members : List Party) (word : RawEvent Party Good Port Technology Instrument)

inductive RoutingFailure (front : RawEvent Party Good Port Technology Instrument)
    (request : Request Party Good Port Technology Instrument) : Type
  | standing (failed : ¬ Policy.known members request)
  | material (failed : ¬ Responsibility.Family.materialOperation
      (Responsibility.controllerCohort source past nature response)
      (Responsibility.Family.positiveScope source past nature response) request)
  | quota (failed : ¬ RawAmount claim state law members front request)
  | control (failed : ¬ RawControl claim state law members front request)

inductive ResourceIssue : Type
  | recipe (item : ExecutionItem Party Good Port Technology Instrument)
      (original : item ∈ (Primitive.execute law state.raw 0 word).items) (issue : RecipeFailure law item)
  | startup (item : ExecutionItem Party Good Port Technology Instrument)
      (original : item ∈ (Primitive.execute law state.raw 0 word).items)
      (entry : (Party × Good) × ℚ) (debited : entry ∈ law.debit item.before item.request)
      (shortage : state.raw.stock entry.1.1 entry.1.2 <
        Primitive.requiredStock law state.raw (Primitive.execute law state.raw 0 word).items entry.1.1 entry.1.2)
  | routing (pair : RawEvent Party Good Port Technology Instrument × Request Party Good Port Technology Instrument)
      (original : pair ∈ Primitive.steps word) (issue : RoutingFailure claim state law members pair.1 pair.2)
  | necessity (actor : Party) (original : actor ∈ members)
      (missing : ¬ Bill word actor (law.necessities state.raw actor) .necessity)
  | maintenance (actor : Party) (original : actor ∈ members)
      (missing : ¬ Bill word actor (law.mandatoryMaintenance state.raw actor) .maintenance)
  | capacity (key : Party × Good) (original : key ∈ Responsibility.Family.positiveScope source past nature response)
      (shortage : Primitive.net law (Primitive.execute law state.raw 0 word).items key.1 key.2 < state.remaining key)

inductive ResourceResult : Type
  | ready (resources : Resources claim state law members word)
  | blocked (issue : ResourceIssue claim state law members word)

def inspectResources : ResourceResult claim state law members word := by
  match inspectAll (fun item => RecipeFacts law [item]) (Primitive.execute law state.raw 0 word).items with
  | .blocked item original failed =>
    match inspectRecipeAt law item with
    | .ready facts => exact (failed facts).elim
    | .blocked issue => exact .blocked (.recipe item original issue)
  | .ready recipe =>
    match inspectAll (fun item : ExecutionItem Party Good Port Technology Instrument =>
        ∀ entry ∈ law.debit item.before item.request,
          Primitive.requiredStock law state.raw (Primitive.execute law state.raw 0 word).items entry.1.1 entry.1.2 ≤
            state.raw.stock entry.1.1 entry.1.2) (Primitive.execute law state.raw 0 word).items with
    | .blocked item original failed =>
      match inspectAll (fun entry : (Party × Good) × ℚ =>
          Primitive.requiredStock law state.raw (Primitive.execute law state.raw 0 word).items entry.1.1 entry.1.2 ≤
            state.raw.stock entry.1.1 entry.1.2) (law.debit item.before item.request) with
      | .ready affordable => exact (failed affordable).elim
      | .blocked entry debited shortage => exact .blocked (.startup item original entry debited (lt_of_not_ge shortage))
    | .ready startup =>
      match inspectAll (fun pair : RawEvent Party Good Port Technology Instrument × Request Party Good Port Technology Instrument =>
          Policy.known members pair.2 ∧ Responsibility.Family.materialOperation
            (Responsibility.controllerCohort source past nature response)
            (Responsibility.Family.positiveScope source past nature response) pair.2 ∧
          RawAmount claim state law members pair.1 pair.2 ∧ RawControl claim state law members pair.1 pair.2) (Primitive.steps word) with
      | .blocked pair original failed =>
        if known : Policy.known members pair.2 then
          if material : Responsibility.Family.materialOperation (Responsibility.controllerCohort source past nature response)
              (Responsibility.Family.positiveScope source past nature response) pair.2 then
            if quota : RawAmount claim state law members pair.1 pair.2 then
              exact .blocked (.routing pair original (.control (fun control => failed ⟨known,material,quota,control⟩)))
            else exact .blocked (.routing pair original (.quota quota))
          else exact .blocked (.routing pair original (.material material))
        else exact .blocked (.routing pair original (.standing known))
      | .ready routing =>
        match inspectAll (fun actor => Bill word actor (law.necessities state.raw actor) .necessity ∧
            Bill word actor (law.mandatoryMaintenance state.raw actor) .maintenance) members with
        | .blocked actor original failed =>
          if necessity : Bill word actor (law.necessities state.raw actor) .necessity then
            exact .blocked (.maintenance actor original (fun maintenance => failed ⟨necessity,maintenance⟩))
          else exact .blocked (.necessity actor original necessity)
        | .ready needs =>
          match inspectAll (fun key => state.remaining key ≤ Primitive.net law
              (Primitive.execute law state.raw 0 word).items key.1 key.2)
              (Responsibility.Family.positiveScope source past nature response) with
          | .blocked key original shortage => exact .blocked (.capacity key original (lt_of_not_ge shortage))
          | .ready net => exact .ready ⟨fun item member => recipe item member item List.mem_cons_self,startup,routing,needs,net⟩

omit [DecidableEq Technology] [DecidableEq Port] in
theorem resource_failure_is_exactly_about_the_same_source_plan
    (issue : ResourceIssue claim state law members word) : ¬ Resources claim state law members word := by
  intro resources
  cases issue with
  | recipe item original issue =>
    apply recipe_failure_is_the_original_raw_source_failure law item issue
    intro next member
    cases List.mem_singleton.mp member
    exact resources.recipe item original
  | startup item original entry debited shortage => exact not_le_of_gt shortage (resources.startup item original entry debited)
  | routing pair original issue =>
    obtain ⟨known,material,quota,control⟩ := resources.routing pair original
    cases issue with
    | standing failed => exact failed known
    | material failed => exact failed material
    | quota failed => exact failed quota
    | control failed => exact failed control
  | necessity actor original missing => exact missing (resources.bills actor original).1
  | maintenance actor original missing => exact missing (resources.bills actor original).2
  | capacity key original shortage => exact not_le_of_gt shortage (resources.net key original)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Capacity
