import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Word

/-! An unrecognized private gate is not an independent gate.  The finite
source check below retains it on its original item even when the controller
belongs to the group and could execute the entire programme. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl

open Program
universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (current : RawCurrent Party Good Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)
  (family : OriginalItem law current word → List Port) (group : List Party)

def SharedAt (item : OriginalItem law current word) (port : Port) : Prop :=
  ∀ person ∈ group, law.allowed item.val.before.technology port person = true

instance (item : OriginalItem law current word) (port : Port) :
    Decidable (SharedAt law current word group item port) := by unfold SharedAt; infer_instance

def UnresolvedAt (item : OriginalItem law current word) : Prop :=
  Blocked law current word group item ∨
    ∃ port ∈ law.requiredPorts item.val.before item.val.request,
      port ∉ family item ∧ ¬ SharedAt law current word group item port

instance (item : OriginalItem law current word) :
    Decidable (UnresolvedAt law current word family group item) := by
  unfold UnresolvedAt
  infer_instance

abbrev UnresolvedItem :=
  { item : OriginalItem law current word // UnresolvedAt law current word family group item }

def unresolvedInventory : List (UnresolvedItem law current word family group) :=
  (law.rawItems current word).attach.filterMap (fun item =>
    if unsettled : UnresolvedAt law current word family group item then some ⟨item, unsettled⟩ else none)

theorem unresolvedInventory_complete (item : OriginalItem law current word)
    (unsettled : UnresolvedAt law current word family group item) :
    (⟨item, unsettled⟩ : UnresolvedItem law current word family group) ∈
      unresolvedInventory law current word family group :=
  List.mem_filterMap.mpr ⟨item, List.mem_attach _ _, dif_pos unsettled⟩

theorem empty_unresolved_excludes (empty : unresolvedInventory law current word family group = [])
    (item : OriginalItem law current word) : ¬ UnresolvedAt law current word family group item := by
  intro unsettled
  have included := unresolvedInventory_complete law current word family group item unsettled
  rw [empty] at included
  exact List.not_mem_nil included

/-- The actual word is legal and contains no classified control or
unclassified exclusion.  Joint reauthorization is a separate capability. -/
structure PortIndependent where
  originalValid : ∀ item : OriginalItem law current word, law.Valid item.val.before item.val.request
  noControl : ∀ item : OriginalItem law current word,
    ∀ port ∈ law.requiredPorts item.val.before item.val.request, port ∉ family item
  shared : ∀ item : OriginalItem law current word,
    ∀ port ∈ law.requiredPorts item.val.before item.val.request, SharedAt law current word group item port
  alternative : RawEvent Party Good Port Technology Instrument
  generated : law.jointWord group current word = some alternative

private theorem no_unresolved_joint_success
    (empty : unresolvedInventory law current word family group = []) :
    law.jointWord group current word ≠ none := by
  apply law.jointWord_complete
  intro item member
  have clear := empty_unresolved_excludes law current word family group empty ⟨item, member⟩
  have accepted : law.Valid item.before item.request := by
    by_contra refused
    exact clear (Or.inl (Or.inl refused))
  refine ⟨accepted, ?_⟩
  cases found : law.jointSigner group item.before item.request with
  | none => exact False.elim (clear (Or.inl (Or.inr found)))
  | some signer =>
      obtain ⟨inside, legal⟩ := law.jointSigner_sound group _ _ signer found
      exact ⟨signer, inside, legal⟩

def independentOfComplete
    (noControls : controlInventory law current word family = [])
    (noUnresolved : unresolvedInventory law current word family group = []) :
    PortIndependent law current word family group := by
  have clear := empty_unresolved_excludes law current word family group noUnresolved
  have accepted : ∀ item : OriginalItem law current word, law.Valid item.val.before item.val.request := by
    intro item
    by_contra refused
    exact clear item (Or.inl (Or.inl refused))
  have noControl := empty_controlInventory_excludes_every_control law current word family noControls
  have shared : ∀ item : OriginalItem law current word,
      ∀ port ∈ law.requiredPorts item.val.before item.val.request, SharedAt law current word group item port := by
    intro item port required
    by_contra excluded
    exact clear item (Or.inr ⟨port, required, noControl item (accepted item) port required, excluded⟩)
  cases generated : law.jointWord group current word with
  | none => exact False.elim (no_unresolved_joint_success law current word family group noUnresolved generated)
  | some alternative =>
      exact ⟨accepted, fun item => noControl item (accepted item), shared, alternative, generated⟩

inductive CompleteOutcome : Type u
  | controlled (use : ControlUse law current word family)
  | unresolved (item : UnresolvedItem law current word family group)
  | independent (programme : PortIndependent law current word family group)

def classifyComplete : CompleteOutcome law current word family group :=
  match controls : controlInventory law current word family with
  | use :: _ => .controlled use
  | [] =>
      match pending : unresolvedInventory law current word family group with
      | item :: _ => .unresolved item
      | [] => .independent (independentOfComplete law current word family group controls pending)

omit [DecidableEq Port] in
theorem unknown_exclusion_cannot_be_independent
    (programme : PortIndependent law current word family group)
    (item : OriginalItem law current word) (port : Port)
    (required : port ∈ law.requiredPorts item.val.before item.val.request)
    (person : Party) (inside : person ∈ group)
    (excluded : law.allowed item.val.before.technology port person = false) : False := by
  have allowed := programme.shared item port required person inside
  exact Bool.noConfusion (allowed.symm.trans excluded)

#print axioms classifyComplete
#print axioms unknown_exclusion_cannot_be_independent

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl
