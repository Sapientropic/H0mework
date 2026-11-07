import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.Thread
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native.Micro.History

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.PublicFunction
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Registered Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

/-- Only a creator can supply this descriptor. Its index is the Input that
the creator itself emits; no displayed task or reconstructed GS is accepted. -/
inductive OriginAt : ProgrammeSource.Input Party Good Port Technology Instrument → Type
  | source (code : SourceCode Party Good Port Technology Instrument) : OriginAt code.input
  | outstanding (original : OutstandingSource Party Good Port Technology Instrument) : OriginAt original.input

namespace OriginAt

variable {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  (origin : OriginAt input)

def task : PublicTaskSpec Party Good := match origin with
  | .source code => originalTask code
  | .outstanding original => original.seed.task

def Slot : Type := match origin with
  | .source code => Native.Slot code
  | .outstanding original => original.Slot

variable [DecidableEq Port] (depth count : Nat)

def vocabulary : ResponsibilityLifecycle.Vocabulary := match origin with
  | .source code => V code
  | .outstanding original => OutstandingSource.History.NativeService.V original
      (Macro.Services.Native.originalWords original depth count)

def process : NativeResponsibilityProcess (origin.vocabulary depth count) := match origin with
  | .source code => Native.process code
  | .outstanding original => OutstandingSource.History.NativeService.threadProcess original
      (Macro.Services.Native.originalWords original depth count)

def Thread : origin.Slot → Type := match origin with
  | .source code => Native.Thread code
  | .outstanding original => Macro.Services.Native.Micro.Attached original
      (Macro.Services.Native.originalWords original depth count)

def seed : (index : origin.Slot) → origin.Thread depth count index := match origin with
  | .source code => fun index => Native.Thread.fromPrefix code index
      (historyAt code index (Settlement.physicalIndex code.input depth count - 1))
  | .outstanding original => fun index => Macro.Services.Native.Micro.initial original depth count index

def state : {index : origin.Slot} → origin.Thread depth count index →
    (origin.process depth count).GeneratedState := by
  cases origin with
  | source code => exact fun prior => prior.state
  | outstanding original => exact fun prior => prior.state

def advance : {index : origin.Slot} → origin.Thread depth count index →
    SourceInput (Party := Party) (Good := Good) (Port := Port) (Technology := Technology)
      (Instrument := Instrument) → origin.Thread depth count index := by
  cases origin with
  | source code => exact fun prior actual => prior.advance code actual
  | outstanding original =>
      exact fun prior actual => prior.advance
        ⟨actual.portDecidable, actual.depth, actual.count, actual.prefixLimit, actual.renewalLimit, actual.cursor⟩

def run {index : origin.Slot} (prior : origin.Thread depth count index)
    (actual : SourceInput (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument)) :
    (origin.process depth count).Run (origin.state depth count prior).current
      (origin.state depth count (origin.advance depth count prior actual)).current := by
  cases origin with
  | source code => exact prior.nativeRun code actual
  | outstanding original => exact prior.actualRun _

theorem source_seed_is_the_literal_original_history
    (code : SourceCode Party Good Port Technology Instrument) (index : Native.Slot code) :
    (OriginAt.source code).state depth count ((OriginAt.source code).seed depth count index) =
      (historyAt code index (Settlement.physicalIndex code.input depth count - 1)).state := rfl

theorem legacy_seed_is_the_literal_original_native_state
    (original : OutstandingSource Party Good Port Technology Instrument) (index : original.Slot) :
    (OriginAt.outstanding original).state depth count ((OriginAt.outstanding original).seed depth count index) =
      (Macro.Services.Native.originalThread original depth count index).state := rfl

end OriginAt

#print axioms OriginAt.run
#print axioms OriginAt.source_seed_is_the_literal_original_history
#print axioms OriginAt.legacy_seed_is_the_literal_original_native_state

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native
