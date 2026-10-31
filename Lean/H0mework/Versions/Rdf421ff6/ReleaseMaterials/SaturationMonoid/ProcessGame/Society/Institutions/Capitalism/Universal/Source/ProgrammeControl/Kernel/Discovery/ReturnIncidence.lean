import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Discovery.Detector

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Discovery.ReturnIncidence

open Program
universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (current : RawCurrent Party Good Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)

/-- Every occurred direct return is also offered as its own one-leg route.
This keeps later payments visible even when routeBetween stored an earlier path. -/
def directReturns (access : AccessProposal law current word) : List (ReciprocityProposal law current word) :=
  (law.rawItems current word).attach.flatMap fun item =>
    match item.val.request.operation with
    | .transfer payer receiver _ =>
        if payer = access.recipient ∧ receiver = access.controller law current word then
          (law.actualCredit item.val.before item.val.request).filterMap fun lot =>
            if lot.1.1 = receiver ∧ 0 < lot.2 then
              some (.returnFlow lot.1.2 lot.1.2 [⟨item,lot.1⟩])
            else none
        else []
    | _ => []

def reciprocities (access : AccessProposal law current word) :=
  Discovery.reciprocities law current word access ++ directReturns law current word access

/-- Keep every successful source candidate; the first detector is not a census. -/
def kernels : List (CapitalRelationKernel law current word) :=
  (accesses law current word).flatMap fun access =>
    (reciprocities law current word access).flatMap fun reciprocity =>
      (disposals law current word access).filterMap fun disposal =>
        Kernel.compile law current word ⟨access,reciprocity,disposal⟩

theorem kernels_exact (kernel : CapitalRelationKernel law current word) :
    kernel ∈ kernels law current word ↔
      ∃ access ∈ accesses law current word,
        ∃ reciprocity ∈ reciprocities law current word access,
          ∃ disposal ∈ disposals law current word access,
            Kernel.compile law current word ⟨access,reciprocity,disposal⟩ = some kernel := by
  simp only [kernels,List.mem_flatMap,List.mem_filterMap]

theorem every_successfully_compiled_direct_return_is_in_the_census
    (access : AccessProposal law current word) (listed : access ∈ accesses law current word)
    (reciprocity : ReciprocityProposal law current word) (direct : reciprocity ∈ directReturns law current word access)
    (disposal : DisposalProposal law current word) (available : disposal ∈ disposals law current word access)
    (kernel : CapitalRelationKernel law current word)
    (checked : Kernel.compile law current word ⟨access,reciprocity,disposal⟩ = some kernel) :
    kernel ∈ kernels law current word :=
  (kernels_exact law current word kernel).mpr ⟨access,listed,reciprocity,
    List.mem_append_right _ direct,disposal,available,checked⟩

def route (kernel : CapitalRelationKernel law current word) : List (RouteLeg law current word) :=
  match kernel.proposal.reciprocity with
  | .returnFlow _ _ actual => actual
  | _ => []

/-- Only an occurred direct transfer from the access recipient to its original
controller is selected. A local disposal alternative is never a payment. -/
def direct (kernel : CapitalRelationKernel law current word) (leg : RouteLeg law current word) : Bool :=
  match leg.item.val.request.operation with
  | .transfer payer receiver _ => decide (payer = kernel.proposal.access.recipient ∧
      receiver = kernel.proposal.access.controller law current word)
  | _ => false

def positionsOf (found : List (CapitalRelationKernel law current word)) : List Nat :=
  found.flatMap fun kernel => (route law current word kernel).filterMap fun leg =>
    if direct law current word kernel leg then some leg.item.val.index else none

def positions := positionsOf law current word (kernels law current word)
def selectedBy (found : List (CapitalRelationKernel law current word)) (index : Nat) : Bool :=
  (positionsOf law current word found).any fun original => original == index
def selected := selectedBy law current word (kernels law current word)

omit [DecidableEq Port] in
theorem selectedBy_exact (found : List (CapitalRelationKernel law current word)) (index : Nat) :
    selectedBy law current word found index = true ↔
      ∃ kernel ∈ found, ∃ leg ∈ route law current word kernel,
        direct law current word kernel leg = true ∧ leg.item.val.index = index := by
  simp only [selectedBy,positionsOf,List.any_eq_true,List.mem_flatMap,List.mem_filterMap]
  constructor
  · rintro ⟨position,⟨kernel,member,leg,inside,hit⟩,same⟩
    split at hit
    · rename_i positive
      cases Option.some.inj hit
      exact ⟨kernel,member,leg,inside,positive,beq_iff_eq.mp same⟩
    · cases hit
  · rintro ⟨kernel,member,leg,inside,positive,same⟩
    exact ⟨index,⟨kernel,member,leg,inside,by simp [positive,same]⟩,beq_iff_eq.mpr rfl⟩

theorem selected_exact (index : Nat) :
    selected law current word index = true ↔
      ∃ kernel ∈ kernels law current word, ∃ leg ∈ route law current word kernel,
        direct law current word kernel leg = true ∧ leg.item.val.index = index :=
  selectedBy_exact law current word _ _

omit [DecidableEq Port] in
theorem duplicate_explanations_do_not_select_another_payment
    (found : List (CapitalRelationKernel law current word)) (index : Nat) :
    selectedBy law current word (found ++ found) index = selectedBy law current word found index := by
  simp only [selectedBy,positionsOf,List.flatMap_append,List.any_append,Bool.or_self]

omit [DecidableEq Port] in
private theorem follows_keeps_actual_validity
    (trail : List (RouteLeg law current word)) (source target : Party × Good) (lower upper : Nat)
    (follows : Follows law current word source lower trail target upper)
    (leg : RouteLeg law current word) (inside : leg ∈ trail) :
    law.Valid leg.item.val.before leg.item.val.request := by
  induction trail generalizing source lower with
  | nil => cases inside
  | cons head rest ih =>
      rcases List.mem_cons.mp inside with same | later
      · subst leg; exact follows.2.1
      · exact ih head.destination (head.item.val.index + 1) follows.2.2.2.2 later

omit [DecidableEq Port] in
theorem every_return_leg_is_an_actual_accepted_item
    (kernel : CapitalRelationKernel law current word)
    (leg : RouteLeg law current word) (inside : leg ∈ route law current word kernel) :
    law.Valid leg.item.val.before leg.item.val.request := by
  have checked := kernel.checked.2.1
  cases original : kernel.proposal.reciprocity with
  | productiveInput => simp [route,original] at inside
  | claim => simp [route,original] at inside
  | returnFlow fromGood returnGood trail =>
      rw [original] at checked
      simp only [route,original] at inside
      exact follows_keeps_actual_validity law current word trail _ _ _ _ checked.2 leg inside

theorem selected_payment_keeps_original_control_and_both_actual_items (index : Nat)
    (marked : selected law current word index = true) :
    ∃ kernel ∈ kernels law current word, ∃ leg ∈ route law current word kernel,
      kernel.proposal.Checks law current word ∧
      kernel.proposal.access.access.val ∈ law.rawItems current word ∧
      leg.item.val ∈ law.rawItems current word ∧ leg.item.val.index = index ∧
      ∃ goods, leg.item.val.request.operation = .transfer kernel.proposal.access.recipient
        (kernel.proposal.access.controller law current word) goods := by
  obtain ⟨kernel,member,leg,inside,directed,same⟩ := (selected_exact law current word index).mp marked
  refine ⟨kernel,member,leg,inside,kernel.checked,kernel.proposal.access.access.property,
    leg.item.property,same,?_⟩
  unfold direct at directed
  split at directed
  · rename_i payer receiver goods operation
    obtain ⟨rfl,rfl⟩ := of_decide_eq_true directed
    exact ⟨goods,operation⟩
  all_goals cases directed

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Discovery.ReturnIncidence
