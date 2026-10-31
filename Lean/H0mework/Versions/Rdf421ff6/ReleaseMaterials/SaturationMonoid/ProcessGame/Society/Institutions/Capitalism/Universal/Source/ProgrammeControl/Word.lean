import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.JointAuthority

/-! Full-word control readout.  The relative control family is an original
source relation inventory; it is not inferred from an acquisition amount.
Production, use, maintenance and revision therefore pass through one scan.
Failure of re-signing remains an original instruction obstruction. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl

open Program

universe u

variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (current : RawCurrent Party Good Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)

abbrev OriginalItem :=
  { item : ExecutionItem Party Good Port Technology Instrument // item ∈ law.rawItems current word }


def itemAt (index : Fin word.length) : OriginalItem law current word :=
  ⟨(law.rawItems current word).get
      ⟨index.val, by simpa only [RawLaw.rawItems, RawLaw.inventory_length] using index.isLt⟩,
    List.get_mem _ _⟩

structure ControlUse (controlledPorts : OriginalItem law current word → List Port) where
  item : OriginalItem law current word
  accepted : law.Valid item.val.before item.val.request
  port : Port
  required : port ∈ law.requiredPorts item.val.before item.val.request
  controlled : port ∈ controlledPorts item

def controlInventory (controlledPorts : OriginalItem law current word → List Port) :
    List (ControlUse law current word controlledPorts) :=
  (law.rawItems current word).attach.flatMap (fun item =>
    if accepted : law.Valid item.val.before item.val.request then
      (law.requiredPorts item.val.before item.val.request).attach.filterMap (fun port =>
        if controlled : port.val ∈ controlledPorts item then
          some ⟨item, accepted, port.val, port.property, controlled⟩ else none)
    else [])

theorem controlInventory_complete (controlledPorts : OriginalItem law current word → List Port)
    (item : OriginalItem law current word) (accepted : law.Valid item.val.before item.val.request)
    (port : Port) (required : port ∈ law.requiredPorts item.val.before item.val.request)
    (controlled : port ∈ controlledPorts item) :
    (⟨item, accepted, port, required, controlled⟩ : ControlUse law current word controlledPorts) ∈
      controlInventory law current word controlledPorts := by
  apply List.mem_flatMap.mpr
  refine ⟨item, List.mem_attach _ _, ?_⟩
  rw [dif_pos accepted]
  apply List.mem_filterMap.mpr
  exact ⟨⟨port, required⟩, List.mem_attach _ _, dif_pos controlled⟩

theorem empty_controlInventory_excludes_every_control (controlledPorts : OriginalItem law current word → List Port)
    (empty : controlInventory law current word controlledPorts = [])
    (item : OriginalItem law current word) (accepted : law.Valid item.val.before item.val.request)
    (port : Port) (required : port ∈ law.requiredPorts item.val.before item.val.request) :
    port ∉ controlledPorts item := by
  intro controlled
  have member := controlInventory_complete law current word controlledPorts item accepted port required controlled
  rw [empty] at member
  exact List.not_mem_nil member

def Blocked (group : List Party) (item : OriginalItem law current word) : Prop :=
  ¬ law.Valid item.val.before item.val.request ∨
    law.jointSigner group item.val.before item.val.request = none

instance (group : List Party) (item : OriginalItem law current word) :
    Decidable (Blocked law current word group item) := by
  unfold Blocked
  infer_instance

abbrev ObstructedItem (group : List Party) :=
  { item : OriginalItem law current word // Blocked law current word group item }

def obstructionInventory (group : List Party) : List (ObstructedItem law current word group) :=
  (law.rawItems current word).attach.filterMap (fun item =>
    if blocked : Blocked law current word group item then some ⟨item, blocked⟩ else none)

omit [DecidableEq Port] in
theorem failure_has_original_obstruction (group : List Party)
    (failed : law.jointWord group current word = none) :
    obstructionInventory law current word group ≠ [] := by
  obtain ⟨item, member, reason⟩ := law.jointWord_failure_original group current word failed 0
  have blocked : Blocked law current word group ⟨item, member⟩ := by
    rcases reason with refused | unavailable
    · exact Or.inl refused
    · right
      simpa [RawLaw.jointSigner] using unavailable
  have included : (⟨⟨item, member⟩, blocked⟩ : ObstructedItem law current word group) ∈
      obstructionInventory law current word group := by
    exact List.mem_filterMap.mpr ⟨⟨item, member⟩, List.mem_attach _ _, dif_pos blocked⟩
  intro empty
  rw [empty] at included
  exact List.not_mem_nil included

inductive Outcome (controlledPorts : OriginalItem law current word → List Port) (group : List Party) : Type u
  | controlled (use : ControlUse law current word controlledPorts)
  | independent (alternative : RawEvent Party Good Port Technology Instrument)
      (generated : law.jointWord group current word = some alternative)
      (controlFree : controlInventory law current word controlledPorts = [])
  | unresolved (item : ObstructedItem law current word group)

def classify (controlledPorts : OriginalItem law current word → List Port) (group : List Party) :
    Outcome law current word controlledPorts group :=
  match controls : controlInventory law current word controlledPorts with
  | use :: _ => .controlled use
  | [] =>
      match attempted : law.jointWord group current word with
      | some alternative => .independent alternative attempted controls
      | none => .unresolved ((obstructionInventory law current word group).head
          (failure_has_original_obstruction law current word group attempted))

theorem independent_preserves_complete_next (controlledPorts : OriginalItem law current word → List Port) (group : List Party)
    (alternative : RawEvent Party Good Port Technology Instrument)
    (generated : law.jointWord group current word = some alternative)
    (controlFree : controlInventory law current word controlledPorts = []) :
    law.next current alternative = law.next current word ∧
    (∀ item ∈ law.rawItems current alternative,
      law.Valid item.before item.request ∧ item.request.signer ∈ group ∧ ∀ person ∈ item.request.consents, person ∈ group) ∧
    (∀ item : OriginalItem law current word,
      law.Valid item.val.before item.val.request →
      ∀ port ∈ law.requiredPorts item.val.before item.val.request, port ∉ controlledPorts item) :=
  ⟨law.jointWord_same_next group current word alternative generated,
    (law.jointWord_sound group current word alternative generated 0).2.1,
    empty_controlInventory_excludes_every_control law current word controlledPorts controlFree⟩

#print axioms classify
#print axioms independent_preserves_complete_next

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl
