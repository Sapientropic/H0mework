import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Discovery.Detector

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Profit

open Source.Program Source.ProgrammeControl Source.ProgrammeControl.Kernel

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (initial : RawCurrent Party Good Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)

/-- Read the entire original compiler image, rather than stopping at its first explanation. -/
def originalControlImage : List (CapitalRelationKernel law initial word) :=
  (Discovery.accesses law initial word).flatMap fun access =>
    (Discovery.reciprocities law initial word access).flatMap fun reciprocity =>
      (Discovery.disposals law initial word access).filterMap fun disposal =>
        Kernel.compile law initial word ⟨access,reciprocity,disposal⟩

theorem original_control_image_is_exact (kernel : CapitalRelationKernel law initial word) :
    kernel ∈ originalControlImage law initial word ↔
      ∃ access ∈ Discovery.accesses law initial word,
        ∃ reciprocal ∈ Discovery.reciprocities law initial word access,
          ∃ disposal ∈ Discovery.disposals law initial word access,
            Kernel.compile law initial word ⟨access,reciprocal,disposal⟩ = some kernel := by
  simp only [originalControlImage,List.mem_flatMap,List.mem_filterMap]

/-- These are actual request addresses, including the original advance and
reverse-flow legs. Hypothetical disposal alternatives never enter the income fold. -/
def originalReciprocalIndices : ReciprocityProposal law initial word → List Nat
  | .productiveInput producer _ _ _ route => producer.val.index :: route.map (fun leg => leg.item.val.index)
  | .returnFlow _ _ route => route.map (fun leg => leg.item.val.index)
  | .claim item => [item.val.index]

def originalControlIndices (kernel : CapitalRelationKernel law initial word) : List Nat :=
  kernel.proposal.access.access.val.index :: originalReciprocalIndices law initial word kernel.proposal.reciprocity

def markedBy (image : List (CapitalRelationKernel law initial word)) (position : Nat) : Bool :=
  image.any fun kernel => position ∈ originalControlIndices law initial word kernel

def sourceMarked (position : Nat) : Bool :=
  markedBy law initial word (originalControlImage law initial word) position

def sourceOwnerMarked (position : Nat) (person : Party) : Bool :=
  (originalControlImage law initial word).any fun kernel =>
    decide (position ∈ originalControlIndices law initial word kernel ∧
      person = kernel.proposal.access.controller law initial word)

theorem an_owner_mark_is_its_original_controller_and_actual_position
    (position : Nat) (person : Party) (marked : sourceOwnerMarked law initial word position person = true) :
    ∃ kernel ∈ originalControlImage law initial word,
      position ∈ originalControlIndices law initial word kernel ∧
      person = law.controller kernel.proposal.access.access.val.before.technology kernel.proposal.access.port ∧
      kernel.proposal.Checks law initial word := by
  obtain ⟨kernel,member,selected⟩ := List.any_eq_true.mp marked
  have original := of_decide_eq_true selected
  exact ⟨kernel,member,original.1,original.2,kernel.checked⟩

theorem a_source_mark_has_its_original_checked_control
    (position : Nat) (marked : sourceMarked law initial word position = true) :
    ∃ kernel ∈ originalControlImage law initial word,
      position ∈ originalControlIndices law initial word kernel ∧
      kernel.proposal.Checks law initial word := by
  obtain ⟨kernel,member,selected⟩ := List.any_eq_true.mp marked
  exact ⟨kernel,member,of_decide_eq_true selected,kernel.checked⟩

omit [DecidableEq Port] in
theorem repeated_control_explanations_cannot_double_bill_the_same_original_position
    (image : List (CapitalRelationKernel law initial word)) (position : Nat) :
    markedBy law initial word (image ++ image) position = markedBy law initial word image position := by
  simp only [markedBy,List.any_append,Bool.or_self]

theorem source_mark_retains_the_actual_required_port_and_distinct_controller
    (position : Nat) (marked : sourceMarked law initial word position = true) :
    ∃ kernel ∈ originalControlImage law initial word,
      law.Valid kernel.proposal.access.access.val.before kernel.proposal.access.access.val.request ∧
      kernel.proposal.access.port ∈ law.requiredPorts kernel.proposal.access.access.val.before
        kernel.proposal.access.access.val.request ∧
      law.controller kernel.proposal.access.access.val.before.technology kernel.proposal.access.port ≠
        kernel.proposal.access.recipient := by
  obtain ⟨kernel,member,_,_⟩ := a_source_mark_has_its_original_checked_control law initial word position marked
  have actual := kernel.original_control_and_reproduced_phase law initial word
  exact ⟨kernel,member,actual.1,actual.2.1,
    private_phase_separates_controller law _ _ _ actual.2.2.1⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Profit
