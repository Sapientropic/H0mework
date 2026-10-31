import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Observed

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Observed

open Institutions.Capitalism.Universal.Source.Program ResponsibilityLifecycle

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
  {currentAt otherCurrent : Nat → RawCurrent Party Good (State Party Technology) Instrument}
  {wordAt otherWord : Nat → RawEvent Party Good Port (State Party Technology) Instrument}
  {birth : Nat}
  {grant : Grant base scope (currentAt birth) (wordAt birth)}
  {otherGrant : Grant base scope (otherCurrent birth) (otherWord birth)}


inductive BoundaryEvidence (base : RawLaw Party Good Port Technology Instrument)
    (scope : Scope (Party := Party) (Good := Good) (Port := Port)) where
  | command (visit birth acceptedIndex : Nat)
      (current : RawCurrent Party Good (State Party Technology) Instrument)
      (word : RawEvent Party Good Port (State Party Technology) Instrument)
      (actual : ActualCommand base scope current word)
      (later : birth < visit ∨ (birth = visit ∧ acceptedIndex < actual.item.val.index))
      (kind : IsBoundary actual.command)
  | handoff (visit birth acceptedIndex : Nat)
      (current : RawCurrent Party Good (State Party Technology) Instrument)
      (word : RawEvent Party Good Port (State Party Technology) Instrument)
      (next : Grant base scope current word)
      (later : birth < visit ∨ (birth = visit ∧ acceptedIndex < next.acceptance.item.val.index))
  | refused (visit birth acceptedIndex : Nat)
      (current : RawCurrent Party Good (State Party Technology) Instrument)
      (word : RawEvent Party Good Port (State Party Technology) Instrument)
      (item : {item // item ∈ (law base scope).rawItems current word})
      (operator : Party) (target : State Party Technology) (command : Command Party)
      (operation : item.val.request.operation = .revise operator target)
      (marked : target.last = some command)
      (authentic : Authentic scope item.val.before item.val.request operator target command)
      (refused : ¬ (law base scope).Valid item.val.before item.val.request)
      (later : birth < visit ∨ (birth = visit ∧ acceptedIndex < item.val.index))
      (kind : IsBoundary command)

def acceptedEvidence {obligation : AdmittedObligation (vocabulary (Party := Party) (Port := Port))}
    (event : Lifecycle.Event base scope currentAt wordAt birth grant obligation) : BoundaryEvidence base scope := by
  rcases event with ⟨visit, actual, later, kind, origin⟩ | ⟨visit, next, later, origin⟩
  · exact .command visit birth grant.acceptance.item.val.index _ _ actual later kind
  · exact .handoff visit birth grant.acceptance.item.val.index _ _ next later

def Event.evidence {obligation : AdmittedObligation (vocabulary (Party := Party) (Port := Port))}
    (event : Event base scope currentAt wordAt birth grant obligation) : BoundaryEvidence base scope := by
  rcases event with ⟨accepted⟩ | ⟨refused⟩
  · exact acceptedEvidence accepted
  · exact .refused refused.visit birth grant.acceptance.item.val.index _ _ refused.item refused.operator
      refused.target refused.command refused.operation refused.marked refused.authentic refused.refused refused.later refused.kind

def effect {obligation : AdmittedObligation (vocabulary (Party := Party) (Port := Port))}
    (event : Event base scope currentAt wordAt birth grant obligation) :=
  (event.evidence, event.disposition, event.next)

def commandEffect (obligation : AdmittedObligation (vocabulary (Party := Party) (Port := Port)))
    (birth acceptedIndex visit : Nat)
    (current : RawCurrent Party Good (State Party Technology) Instrument)
    (word : RawEvent Party Good Port (State Party Technology) Instrument)
    (actual : ActualCommand base scope current word) :
    Option (BoundaryEvidence base scope × BoundaryDisposition (vocabulary (Party := Party) (Port := Port)) obligation obligation.admission.sourceEvent × AdmittedObligation (vocabulary (Party := Party) (Port := Port))) :=
  if later : birth < visit ∨ (birth = visit ∧ acceptedIndex < actual.item.val.index) then
    if kind : IsBoundary actual.command then
      some (.command visit birth acceptedIndex current word actual later kind, (if @Eq (Option Party) actual.item.val.before.technology.holder (some obligation.bearer) ∧
        ¬ @Eq (Option Party) actual.after.technology.holder (some obligation.bearer) then
          .bearerRelease (.jurisdictionEndedWithResidue .generated .generated)
        else .carry (.maintained .generated)), obligation)
    else if actual.command = .accept then
      ((grantsAt base scope current word).filterMap fun next =>
        if position : next.acceptance.item.val.index = actual.item.val.index then
          some (.handoff visit birth acceptedIndex current word next (position ▸ later),
            (.carry (.transferred next.candidate .generated)), {obligation with bearer := next.candidate})
        else none).head?
    else none
  else none

private theorem accepted_read_effect
    (obligation : AdmittedObligation (vocabulary (Party := Party) (Port := Port)))
    (origin : obligation = {original base scope currentAt wordAt birth grant with bearer := obligation.bearer})
    (visit : Nat) (actual : ActualCommand base scope (currentAt visit) (wordAt visit)) :
    ((Lifecycle.readEvent obligation origin visit actual).map
      (fun event => (acceptedEvidence event, acceptedDisposition event, event.next))) =
      commandEffect obligation birth grant.acceptance.item.val.index visit _ _ actual := by
  unfold Lifecycle.readEvent commandEffect
  by_cases later : birth < visit ∨ (birth = visit ∧ grant.acceptance.item.val.index < actual.item.val.index)
  · have admitted : Later base scope currentAt wordAt birth grant visit actual.item.val.index := later
    rw [dif_pos admitted, dif_pos later]
    by_cases boundary : IsBoundary actual.command
    · simp only [dif_pos boundary]; rfl
    · simp only [dif_neg boundary]
      by_cases accept : actual.command = .accept
      · rw [if_pos accept, if_pos accept]
        simp only [List.head?_filterMap, List.map_findSome?]
        congr 1
        funext next
        dsimp only [Function.comp_apply]
        by_cases position : next.acceptance.item.val.index = actual.item.val.index
        · rw [dif_pos position, dif_pos position]; rfl
        · rw [dif_neg position, dif_neg position]; rfl
      · rw [if_neg accept, if_neg accept]; rfl
  · have denied : ¬ Later base scope currentAt wordAt birth grant visit actual.item.val.index := later
    rw [dif_neg denied, dif_neg later]; rfl

def itemEffect (obligation : AdmittedObligation (vocabulary (Party := Party) (Port := Port)))
    (birth acceptedIndex visit : Nat)
    (current : RawCurrent Party Good (State Party Technology) Instrument)
    (word : RawEvent Party Good Port (State Party Technology) Instrument)
    (item : {item // item ∈ (law base scope).rawItems current word}) :
    Option (BoundaryEvidence base scope × BoundaryDisposition (vocabulary (Party := Party) (Port := Port)) obligation obligation.admission.sourceEvent × AdmittedObligation (vocabulary (Party := Party) (Port := Port))) :=
  match recognize base scope current word item with
  | some actual => commandEffect obligation birth acceptedIndex visit current word actual
  | none =>
      match operation : item.val.request.operation with
      | .revise operator target => match marked : target.last with
        | some command =>
          if refused : ¬ (law base scope).Valid item.val.before item.val.request then
            if later : birth < visit ∨ (birth = visit ∧ acceptedIndex < item.val.index) then
              if kind : IsBoundary command then
                if authentic : Authentic scope item.val.before item.val.request operator target command then
                  some (.refused visit birth acceptedIndex current word item operator target command
                    operation marked authentic refused later kind, .carry (.deferred .generated), obligation)
                else none
              else none
            else none
          else none
        | none => none
      | _ => none

theorem read_effect_is_local
    (obligation : AdmittedObligation (vocabulary (Party := Party) (Port := Port)))
    (origin : obligation = {original base scope currentAt wordAt birth grant with bearer := obligation.bearer})
    (visit : Nat)
    (item : {item // item ∈ (law base scope).rawItems (currentAt visit) (wordAt visit)}) :
    (readEvent obligation origin visit item).map effect =
      itemEffect obligation birth grant.acceptance.item.val.index visit _ _ item := by
  unfold readEvent itemEffect
  cases recognized : recognize base scope (currentAt visit) (wordAt visit) item with
  | some actual =>
    simp only [Option.map_map]
    exact accepted_read_effect obligation origin visit actual
  | none =>
    rcases item with ⟨⟨index, before, request⟩, member⟩
    cases request with
    | mk signer consents purpose gates operation =>
      cases operation <;> try rfl
      rename_i operator target
      cases target with
      | mk technology version holder offered last =>
        cases last
        · rfl
        · rename_i command
          dsimp only
          by_cases refused : ¬ (law base scope).Valid before ⟨signer, consents, purpose, gates,
              .revise operator ⟨technology, version, holder, offered, some command⟩⟩
          · simp only [dif_pos refused]
            by_cases later : birth < visit ∨ (birth = visit ∧ grant.acceptance.item.val.index < index)
            · have earlier : Later base scope currentAt wordAt birth grant visit index := later
              simp only [dif_pos earlier, dif_pos later]
              by_cases boundary : IsBoundary command
              · simp only [dif_pos boundary]
                by_cases authentic : Authentic scope before ⟨signer, consents, purpose, gates,
                    .revise operator ⟨technology, version, holder, offered, some command⟩⟩
                    operator ⟨technology, version, holder, offered, some command⟩ command
                · simp only [dif_pos authentic]; rfl
                · simp only [dif_neg authentic]; rfl
              · simp only [dif_neg boundary]; rfl
            · have earlier : ¬ Later base scope currentAt wordAt birth grant visit index := later
              simp only [dif_neg earlier, dif_neg later]
              rfl
          · simp only [dif_neg refused]; rfl


private theorem item_effect_congr
    (obligation : AdmittedObligation (vocabulary (Party := Party) (Port := Port)))
    (birth firstIndex secondIndex visit : Nat) (sameIndex : secondIndex = firstIndex)
    (first second : RawCurrent Party Good (State Party Technology) Instrument)
    (firstWord secondWord : RawEvent Party Good Port (State Party Technology) Instrument)
    (sameCurrent : second = first) (sameWord : secondWord = firstWord)
    (oldItem : {item // item ∈ (law base scope).rawItems first firstWord})
    (newItem : {item // item ∈ (law base scope).rawItems second secondWord})
    (sameItem : newItem.val = oldItem.val) :
    itemEffect obligation birth secondIndex visit second secondWord newItem =
      itemEffect obligation birth firstIndex visit first firstWord oldItem := by
  cases sameIndex
  cases sameCurrent
  cases sameWord
  have equal : newItem = oldItem := Subtype.ext sameItem
  cases equal
  rfl

theorem read_effect_congr
    (sameIndex : otherGrant.acceptance.item.val.index = grant.acceptance.item.val.index)
    (obligation : AdmittedObligation (vocabulary (Party := Party) (Port := Port)))
    (oldOrigin : obligation = {original base scope currentAt wordAt birth grant with bearer := obligation.bearer})
    (newOrigin : obligation = {original base scope otherCurrent otherWord birth otherGrant with bearer := obligation.bearer})
    (visit : Nat) (sameCurrent : otherCurrent visit = currentAt visit) (sameWord : otherWord visit = wordAt visit)
    (oldItem : {item // item ∈ (law base scope).rawItems (currentAt visit) (wordAt visit)})
    (newItem : {item // item ∈ (law base scope).rawItems (otherCurrent visit) (otherWord visit)})
    (sameItem : newItem.val = oldItem.val) :
    (readEvent obligation newOrigin visit newItem).map effect =
      (readEvent obligation oldOrigin visit oldItem).map effect := by
  rw [read_effect_is_local, read_effect_is_local]
  exact item_effect_congr obligation birth _ _ visit sameIndex _ _ _ _ sameCurrent sameWord oldItem newItem sameItem


end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Observed
