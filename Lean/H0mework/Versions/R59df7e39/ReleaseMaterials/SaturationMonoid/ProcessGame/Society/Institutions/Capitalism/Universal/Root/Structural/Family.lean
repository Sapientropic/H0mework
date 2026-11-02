import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History.Binding
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.ActualSurplus.Discovery
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.GeneratedLaw.Members

/-! The root supplies the family from its original source and history.
Title transport, actual surplus and cross-word reproduction are independent
source witnesses; no caller supplies a capitalism label or actor registry. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Structural

open Source.Program Source.ProgrammeControl
open Source.ProgrammeControl.Kernel.AssetAuthority

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

def familyAtVisit (visit : RootFace.Visit input) (item : RootFace.Item input visit) : List Port :=
  generatedFamily input.law (ProgrammeSource.rawCurrent input visit.current)
      (ProgrammeSource.rawEvent input visit.current) input.localAttempts item ++
    Kernel.ActualSurplus.familyAt input.law (ProgrammeSource.rawCurrent input visit.current)
      (ProgrammeSource.rawEvent input visit.current) item ++
    History.generatedFamily input visit item

def originalItem (cut offset : Nat) (item : At (GeneratedLaw.programAt input cut) offset) :
    RootFace.Item input (ProgrammeHistory.visitAt input (cut + offset + 1)) :=
  ⟨item.val, by
    rw [GeneratedLaw.original_instruction_trace_is_literal input cut offset]
    exact item.property⟩

def family (cut offset : Nat) (item : At (GeneratedLaw.programAt input cut) offset) : List Port :=
  familyAtVisit input (ProgrammeHistory.visitAt input (cut + offset + 1)) (originalItem input cut offset item)

def originalOrigin (cut offset : Nat) (item : At (GeneratedLaw.programAt input cut) offset) :
    Financial.InstructionOrigin input :=
  RootFace.original input (ProgrammeHistory.visitAt input (cut + offset + 1)) (originalItem input cut offset item)

omit [DecidableEq Port] in
theorem original_item_is_not_replayed (cut offset : Nat) (item : At (GeneratedLaw.programAt input cut) offset) :
    (originalItem input cut offset item).val = item.val ∧
      (originalOrigin input cut offset item).instruction? input = some item.val :=
  ⟨rfl, RootFace.original_decodes_exact_item input _ _⟩

theorem family_has_original_source_provenance (visit : RootFace.Visit input) (item : RootFace.Item input visit)
    (port : Port) (member : port ∈ familyAtVisit input visit item) :
    (∃ capital ∈ discovered input.law (ProgrammeSource.rawCurrent input visit.current)
        (ProgrammeSource.rawEvent input visit.current) input.localAttempts,
      capital.dependency.proposal.access.port = port ∧
        PrivatePhase input.law item.val.before port capital.dependency.proposal.access.recipient) ∨
    (∃ capital ∈ Kernel.ActualSurplus.discovered input.law (ProgrammeSource.rawCurrent input visit.current)
        (ProgrammeSource.rawEvent input visit.current),
      capital.dependency.proposal.access.port = port ∧
        PrivatePhase input.law item.val.before port capital.dependency.proposal.access.recipient) ∨
    (∃ capital ∈ History.Discovery.discovered input (History.actual input visit),
      capital.access.port = port ∧ History.FreshControl input port item.val) := by
  simp only [familyAtVisit, List.mem_append] at member
  rcases member with (title | surplus) | history
  · exact Or.inl (generatedFamily_original_provenance input.law _ _ input.localAttempts item port title)
  · exact Or.inr (Or.inl (Kernel.ActualSurplus.familyAt_has_original_witness input.law _ _ item port surplus))
  · exact Or.inr (Or.inr (History.generatedFamily_actual_control input visit item port history))

#print axioms original_item_is_not_replayed
#print axioms family_has_original_source_provenance

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Structural
