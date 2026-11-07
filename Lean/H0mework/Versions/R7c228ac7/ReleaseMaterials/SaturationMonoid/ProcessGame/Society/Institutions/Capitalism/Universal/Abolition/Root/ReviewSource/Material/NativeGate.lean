import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Declaration
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.ReviewPhase.Context
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration.Check

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Material

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Registered Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (current : Physical.Cursor Party Good Port Technology Instrument)
  (pair : Abolition.Material.Migration.CodePair Party Good Port Technology Instrument)
  (review : Option (ReviewPhase.ContextAt input))

/-- This checks only the already registered legacy source scope. A ready
legacy scope does not identify a different raw report task with its slots;
that declaration still requires its own source-native lifecycle link. -/
inductive NativeGate : Type
  | scopeUndisclosed (notInstalled : review = none)
  | rejected (context : ReviewPhase.ContextAt input) (installed : review = some context)
      (issue : Macro.Services.Migration.Problem context.source depth count prefixLimit renewalLimit current pair)
  | ready (context : ReviewPhase.ContextAt input) (installed : review = some context)
      (checked : Macro.Services.Migration.Checks context.source depth count prefixLimit renewalLimit current pair)

def nativeGate : NativeGate input depth count prefixLimit renewalLimit current pair review :=
  match review with
  | none => .scopeUndisclosed rfl
  | some context => match Macro.Services.Migration.inspect context.source depth count prefixLimit renewalLimit current pair with
    | .accepted checked => .ready context rfl checked
    | .refused issue => .rejected context rfl issue

def NativeGate.legacyScopeReady : NativeGate input depth count prefixLimit renewalLimit current pair review → Bool
  | .ready .. => true
  | .scopeUndisclosed .. | .rejected .. => false

def nativeResponsibilityEntry :=
  ProgrammeSource.sourceEntry input (Settlement.committedVisit input depth count).current .inherited

theorem missing_native_scope_retains_its_original_row (missing : review = none) :
    (nativeGate input depth count prefixLimit renewalLimit current pair review).legacyScopeReady = false ∧
    ((ProgrammeLedger.evolution input (Settlement.committedVisit input depth count).current).destination
      (nativeResponsibilityEntry input depth count)).1 =
        ProgrammeSource.targetEntry input (Settlement.committedVisit input depth count).current .inherited := by
  constructor
  · subst review
    rfl
  · unfold nativeResponsibilityEntry
    cases (Settlement.committedVisit input depth count).current <;>
      exact ProgrammeLedger.destination_exact input _ _

theorem the_registered_scope_reads_the_same_actual_material_current (context : ReviewPhase.ContextAt input) :
    Physical.stateAt context.source.input depth count prefixLimit renewalLimit current.past =
      Physical.stateAt input depth count prefixLimit renewalLimit current.past :=
  congrArg (fun source => Physical.stateAt source depth count prefixLimit renewalLimit current.past) context.source_eq

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Material

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Material.nativeGate
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Material.missing_native_scope_retains_its_original_row
