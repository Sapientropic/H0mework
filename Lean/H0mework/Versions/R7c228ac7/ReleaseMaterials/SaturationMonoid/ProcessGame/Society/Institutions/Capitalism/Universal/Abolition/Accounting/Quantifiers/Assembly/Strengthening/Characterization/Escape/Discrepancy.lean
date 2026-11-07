import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Support.Local
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Native.Handler

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Escape

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program Source.ProgrammeControl
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Evolution
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (current : Evolving.NativeCurrent (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

theorem every_private_phase_reveals_an_exact_active_interpretation_change
    (claimed : RawLaw Party Good Port Technology Instrument)
    (raw : RawCurrent Party Good Technology Instrument) (port : Port) (person : Party)
    (phase : PrivatePhase claimed raw port person) :
    claimed.allowed raw.technology port person = false ∧
      current.handlerFace.rootRead.allowed raw.technology port person = true ∧
      claimed.allowed raw.technology port person ≠ current.handlerFace.rootRead.allowed raw.technology port person := by
  have active : current.handlerFace.rootRead.allowed raw.technology port person = true := rfl
  exact ⟨phase.2,active,fun same => Bool.noConfusion (phase.2.symm.trans (same.trans active))⟩

/-- The witness itself selects the changed permission address. Renaming
the mechanism or presenting a different law cannot conceal that address. -/
theorem every_regenerated_kernel_locates_its_exact_source_permission_change
    (claimed : RawLaw Party Good Port Technology Instrument)
    (raw : RawCurrent Party Good Technology Instrument) (word : RawEvent Party Good Port Technology Instrument)
    (capital : Kernel.CapitalRelationKernel claimed raw word) :
    claimed.allowed capital.proposal.access.access.val.before.technology capital.proposal.access.port
        capital.proposal.access.recipient = false ∧
      current.handlerFace.rootRead.allowed capital.proposal.access.access.val.before.technology capital.proposal.access.port
        capital.proposal.access.recipient = true ∧
      claimed ≠ current.handlerFace.rootRead := by
  have delta := every_private_phase_reveals_an_exact_active_interpretation_change current claimed _ _ _ capital.checked.1.2.2.1
  refine ⟨delta.1,delta.2.1,?_⟩
  intro same
  apply delta.2.2
  exact congrArg (fun law : RawLaw Party Good Port Technology Instrument => law.allowed
    capital.proposal.access.access.val.before.technology capital.proposal.access.port capital.proposal.access.recipient) same

theorem code_or_history_alone_cannot_regenerate_the_actual_capital_kernel
    (raw : RawCurrent Party Good Technology Instrument) (word : RawEvent Party Good Port Technology Instrument) :
    ¬ Nonempty (Kernel.CapitalRelationKernel current.handlerFace.rootRead raw word) :=
  current.the_actual_root_interpreter_excludes_every_capital_relation.kernel raw word

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Escape
