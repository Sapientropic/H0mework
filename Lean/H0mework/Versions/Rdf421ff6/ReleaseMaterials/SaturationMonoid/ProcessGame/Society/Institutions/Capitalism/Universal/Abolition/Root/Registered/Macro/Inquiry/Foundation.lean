import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Frame
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.InstalledFoundation
import H0mework.Versions.R2.Foundation.Inquiry.Protocol

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Inquiry

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion DebtActivationWorld
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

structure Basis (N : WorldRelationNetwork) where
  entry : (support : N.Support) → OpenResponsibilityAt N support
  disposition : (support : N.Support) → (kind : WorldDispositionKind) → N.DispositionAt support kind

namespace Basis
variable {N : WorldRelationNetwork} (basis : Basis N)

def U7 (_basis : Basis N) : U7ProducerCalculus N where
  DemandAt := fun _ => PUnit
  generateDemand := fun _ => PUnit.unit

def source : U7ActualSuccessorSource N basis.U7 where
  EventAt := SourceGeneratedU7DemandAt basis.U7
  emit := fun obstruction => .canonical obstruction
  demandGeneratedAt := id
  demandEntryAt := fun {support} {_} {_} _ => basis.entry support

def calculus : U7ObstructionEvolutionCalculus N basis.U7 where
  source := basis.source
  compile := fun {support} {obstruction} {_} _ => {
    disposition := .redirected (successor := obstruction) ⟨basis.disposition support _, rfl⟩
    demandEntryDisposition := ⟨.transferred (basis.disposition support _) rfl rfl (Nat.le_refl _), rfl⟩ }

end Basis

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat)
  (start : Physical.Cursor Party Good Port Technology Instrument)
  (proposal : Compile.RawInput Party Good Port Technology Instrument) (sourcePosition : Nat)
  (review : Option (ReviewPhase.ContextAt input) := none)

abbrev Cursor := Accounting.Current (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
abbrev Answer := Cursor (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition ×
  Cursor (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition

def answer (frame : NativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
    (current : frame.V.Current) : Answer (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition :=
  ⟨frame.cursor current, Accounting.next (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition (frame.cursor current)⟩

def baseBasis : Basis (Accounting.N (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition) where
  entry := Epoch.Finance.Future.Installed.canonicalEntry input depth count sourceDepth sourceCount
    (Accounting.seedRun (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
  disposition := Epoch.Finance.Future.Installed.canonicalDisposition input depth count sourceDepth sourceCount
    (Accounting.seedRun (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Inquiry
