import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Planning.Guarantee
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Capacity.Inspection.Recipe

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Planning

open Source.Program Innovation Priority.Adequacy.Capacity Priority.Adequacy.Capacity.Inspection

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (window seed)) (current : Current seed claim)
  (word : RawEvent Party Good Port Technology Instrument)

inductive ResourceIssue : Type
  | recipe (item : ExecutionItem Party Good Port Technology Instrument)
      (original : item ∈ primitiveItems seed claim current word) (issue : RecipeFailure (actualLaw seed) item)
  | startup (item : ExecutionItem Party Good Port Technology Instrument)
      (original : item ∈ primitiveItems seed claim current word)
      (entry : (Party × Good) × ℚ) (debited : entry ∈ (actualLaw seed).debit item.before item.request)
      (shortage : current.raw.stock entry.1.1 entry.1.2 < Priority.Adequacy.Primitive.requiredStock
        (actualLaw seed) current.raw (primitiveItems seed claim current word) entry.1.1 entry.1.2)
  | necessity (actor : Party) (original : actor ∈ seed.current.members)
      (missing : ¬ Bill word actor ((actualLaw seed).necessities current.raw actor) .necessity)
  | maintenance (actor : Party) (original : actor ∈ seed.current.members)
      (missing : ¬ Bill word actor ((actualLaw seed).mandatoryMaintenance current.raw actor) .maintenance)
  | productive (key : Party × Good) (original : key ∈ Responsibility.Family.positiveScope mechanism past nature response)
      (shortage : max 0 ((primitiveAnalysis seed claim current word).netProductive key) < current.productive key)
  | gross (key : Entitlement.Duty.Key (Party := Party) (Good := Good))
      (original : key ∈ Entitlement.Duty.scope (window seed))
      (shortage : grossCredits seed claim current word key < current.gross key)

inductive ResourceResult : Type
  | ready (resources : Resources seed claim current word)
  | blocked (issue : ResourceIssue seed claim current word)

variable [DecidableEq Technology]

def inspectResources : ResourceResult seed claim current word := by
  match inspectAll (fun item => RecipeFacts (actualLaw seed) [item]) (primitiveItems seed claim current word) with
  | .blocked item original failed =>
    match inspectRecipeAt (actualLaw seed) item with
    | .ready facts => exact (failed facts).elim
    | .blocked issue => exact .blocked (.recipe item original issue)
  | .ready recipe =>
    match inspectAll (fun item : ExecutionItem Party Good Port Technology Instrument =>
      ∀ entry ∈ (actualLaw seed).debit item.before item.request,
        Priority.Adequacy.Primitive.requiredStock (actualLaw seed) current.raw (primitiveItems seed claim current word)
          entry.1.1 entry.1.2 ≤ current.raw.stock entry.1.1 entry.1.2) (primitiveItems seed claim current word) with
    | .blocked item original failed =>
      match inspectAll (fun entry : (Party × Good) × ℚ => Priority.Adequacy.Primitive.requiredStock
        (actualLaw seed) current.raw (primitiveItems seed claim current word) entry.1.1 entry.1.2 ≤
          current.raw.stock entry.1.1 entry.1.2) ((actualLaw seed).debit item.before item.request) with
      | .ready enough => exact (failed enough).elim
      | .blocked entry debited shortage => exact .blocked (.startup item original entry debited (lt_of_not_ge shortage))
    | .ready startup =>
      match inspectAll (fun actor => Bill word actor ((actualLaw seed).necessities current.raw actor) .necessity ∧
        Bill word actor ((actualLaw seed).mandatoryMaintenance current.raw actor) .maintenance) seed.current.members with
      | .blocked actor original failed =>
        if paid : Bill word actor ((actualLaw seed).necessities current.raw actor) .necessity then
          exact .blocked (.maintenance actor original (fun maintenance => failed ⟨paid,maintenance⟩))
        else exact .blocked (.necessity actor original paid)
      | .ready needs =>
        match inspectAll (fun key => current.productive key ≤ max 0 ((primitiveAnalysis seed claim current word).netProductive key))
          (Responsibility.Family.positiveScope mechanism past nature response) with
        | .blocked key original shortage => exact .blocked (.productive key original (lt_of_not_ge shortage))
        | .ready productive =>
          match inspectAll (fun key => current.gross key ≤ grossCredits seed claim current word key)
            (Entitlement.Duty.scope (window seed)) with
          | .blocked key original shortage => exact .blocked (.gross key original (lt_of_not_ge shortage))
          | .ready gross => exact .ready ⟨fun item original => recipe item original item List.mem_cons_self,startup,needs,productive,gross⟩

omit [DecidableEq Technology] in
theorem blocked_resources_expose_the_same_original_source_obligation (issue : ResourceIssue seed claim current word) :
    ¬ Resources seed claim current word := by
  intro resources
  cases issue with
  | recipe item original issue =>
    apply recipe_failure_is_the_original_raw_source_failure (actualLaw seed) item issue
    intro next member
    cases List.mem_singleton.mp member
    exact resources.recipe item original
  | startup item original entry debited shortage => exact not_le_of_gt shortage (resources.startup item original entry debited)
  | necessity actor original missing => exact missing (resources.needs actor original).1
  | maintenance actor original missing => exact missing (resources.needs actor original).2
  | productive key original shortage => exact not_le_of_gt shortage (resources.productive key original)
  | gross key original shortage => exact not_le_of_gt shortage (resources.gross key original)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Planning
