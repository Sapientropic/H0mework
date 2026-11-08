import H0mework.Versions.Rcb211392.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Synthesis.Settlement.Stream.Resume.Regen.Selection

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery

open Institutions.Capitalism.Universal.Source.Program

inductive Recipe where
  | ordinary | recycle | factory
  deriving DecidableEq

inductive Route where
  | local (recipe : Recipe)
  | reserve (recipe : Recipe)
  deriving DecidableEq

def Route.all : List Route :=
  [.local .ordinary, .local .recycle, .local .factory,
    .reserve .ordinary, .reserve .recycle, .reserve .factory]

theorem Route.mem_all (route : Route) : route ∈ Route.all := by
  cases route <;> rename_i recipe <;> cases recipe <;> simp [Route.all]

def recipeWord (scope : Scope) (before : Current) : Recipe → List JointAction
  | .ordinary => Supply.lot scope before .normal
  | .recycle => Supply.lot scope before .refeed
  | .factory => Productive.word scope .normal before

def routeWord (scope : Scope) (permission : Material.Mode) (before : Current) : Route → List JointAction
  | .local recipe => recipeWord scope before recipe
  | .reserve recipe =>
    let offer := Material.offer permission
    offer ++ recipeWord scope (Productive.execute scope before 0 offer).final recipe

def Offered (permission : Material.Mode) : Route → Prop
  | .local _ => True
  | .reserve _ => permission ≠ .withheld

instance (permission : Material.Mode) (route : Route) : Decidable (Offered permission route) := by
  cases route <;> unfold Offered <;> infer_instance

def owed (before : Current) : ℚ := before.claims .delivery supplier receiver

/-- Settling the live balance preserves every other claim coordinate. -/
def RetainsClaims (action : JointAction) : Prop :=
  match action.operation with
  | .settle instrument debtor holder _ =>
    instrument = .delivery ∧ debtor = supplier ∧ holder = receiver
  | .assign .. | .issue .. => False
  | _ => True

instance (action : JointAction) : Decidable (RetainsClaims action) := by
  unfold RetainsClaims
  cases action.operation <;> infer_instance

private def claimRefusal? (word : List JointAction) :
    Option { action // action ∈ word ∧ ¬ RetainsClaims action } :=
  word.attach.findSome? fun action =>
    if refused : ¬ RetainsClaims action.val then
      some ⟨action.val, action.property, refused⟩
    else none

private theorem retains_each_claim (word : List JointAction) (accepted : claimRefusal? word = none) :
    ∀ action ∈ word, RetainsClaims action := by
  unfold claimRefusal? at accepted
  rw [List.findSome?_eq_none_iff] at accepted
  intro action member
  by_contra refused
  have checked := accepted ⟨action, member⟩ (by simp)
  simp [dif_pos refused] at checked

variable (scope : Scope) (permission : Material.Mode) (before : Current) (route : Route)

def quotedItems : List Item := (law scope).rawItems before (routeWord scope permission before route)
def quotedAfter : Current := (law scope).next before (routeWord scope permission before route)

def Available : Prop :=
  0 < owed before ∧ Offered permission route ∧
    (∀ row ∈ quotedItems scope permission before route, (law scope).Valid row.before row.request) ∧
    (∀ action ∈ routeWord scope permission before route, RetainsClaims action) ∧
    owed (quotedAfter scope permission before route) = 0

inductive Obstruction where
  | noLivePrincipal (nonpositive : ¬ 0 < owed before)
  | offerWithheld (unregistered : ¬ Offered permission route)
  | refused (row : Item) (original : row ∈ quotedItems scope permission before route)
      (invalid : ¬ (law scope).Valid row.before row.request)
  | altersOtherClaims (action : JointAction) (original : action ∈ routeWord scope permission before route)
      (invalid : ¬ RetainsClaims action)
  | unsettled (remaining : owed (quotedAfter scope permission before route) ≠ 0)

theorem Obstruction.excludes
    (obstruction : Obstruction scope permission before route) : ¬ Available scope permission before route := by
  rintro ⟨positive, offer, valid, retained, paid⟩
  cases obstruction with
  | noLivePrincipal unavailable => exact unavailable positive
  | offerWithheld absent => exact absent offer
  | refused row original invalid => exact invalid (valid row original)
  | altersOtherClaims action original invalid => exact invalid (retained action original)
  | unsettled remaining => exact remaining paid

def inspect :
    PLift (Available scope permission before route) ⊕ Obstruction scope permission before route :=
  if positive : 0 < owed before then
    if offer : Offered permission route then
      match checked : firstRefusal scope (quotedItems scope permission before route) with
      | some row => .inr (.refused row.val row.property.1 row.property.2)
      | none =>
        match retained : claimRefusal? (routeWord scope permission before route) with
        | some action =>
          .inr (.altersOtherClaims action.val action.property.1 action.property.2)
        | none =>
          if settled : owed (quotedAfter scope permission before route) = 0 then
            .inl ⟨positive, offer, (no_refusal_iff_every_original_row_is_paid scope _).1 checked,
              retains_each_claim _ retained, settled⟩
          else .inr (.unsettled settled)
    else .inr (.offerWithheld offer)
  else .inr (.noLivePrincipal positive)

abbrev OptionAt := { route // Available scope permission before route }

def admitted? : Option (OptionAt scope permission before) :=
  match inspect scope permission before route with
  | .inl available => some ⟨route, available.down⟩
  | .inr _ => none

def usable : List (OptionAt scope permission before) :=
  Route.all.filterMap (admitted? scope permission before)

theorem usable_exact (route : Route) :
    (∃ choice ∈ usable scope permission before, choice.val = route) ↔ Available scope permission before route := by
  constructor
  · rintro ⟨⟨chosen, proof⟩, _, rfl⟩
    exact proof
  · intro available
    cases inspected : inspect scope permission before route with
    | inl proof =>
      refine ⟨⟨route, proof.down⟩, ?_, rfl⟩
      exact List.mem_filterMap.mpr ⟨route, route.mem_all, by simp [admitted?, inspected]⟩
    | inr blocked => exact ((blocked.excludes scope permission before route) available).elim

def select? : Option (OptionAt scope permission before) := (usable scope permission before).head?

theorem the_ordinary_route_is_selected_when_available
    (available : Available scope permission before (.local .ordinary)) :
    ∃ proof, select? scope permission before = some ⟨.local .ordinary, proof⟩ := by
  cases admitted : inspect scope permission before (.local .ordinary) with
  | inl checked =>
    refine ⟨checked.down, ?_⟩
    simp [select?, usable, Route.all, admitted?, admitted]
  | inr blocked => exact ((blocked.excludes scope permission before _) available).elim

theorem no_choice_has_a_named_obstruction_for_each_route
    (unavailable : select? scope permission before = none) :
    ∀ route, Nonempty (Obstruction scope permission before route) := by
  intro route
  cases checked : inspect scope permission before route with
  | inr blocked => exact ⟨blocked⟩
  | inl available =>
    obtain ⟨choice, present, _⟩ := (usable_exact scope permission before route).2 available.down
    have empty : usable scope permission before = [] := List.head?_eq_none_iff.mp unavailable
    rw [empty] at present
    exact (List.not_mem_nil present).elim

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery
