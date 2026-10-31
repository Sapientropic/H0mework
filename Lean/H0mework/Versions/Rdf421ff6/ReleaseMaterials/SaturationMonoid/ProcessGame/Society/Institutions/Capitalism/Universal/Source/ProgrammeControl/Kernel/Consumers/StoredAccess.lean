import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Core

set_option autoImplicit false
set_option maxRecDepth 4096

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Consumers.StoredAccess

open Program
abbrev Current := RawCurrent Bool Unit Unit Unit
abbrev Input := Request Bool Unit Bool Unit Unit

def law : RawLaw Bool Unit Bool Unit Unit where
  technique := fun _ _ => ⟨[], [], [], []⟩
  controller := fun _ port => port
  allowed := fun _ port actor => decide (port = actor)
  stockPort := fun _ holder _ => holder
  revisionPort := fun _ => false
  revisionCost := fun _ _ => []
  settlementUnit := fun _ => ()
  settlementRate := fun _ => 1
  issuerPort := fun _ => false
  necessities := fun _ person => if person then [((), 1)] else []
  mandatoryMaintenance := fun _ _ => []
  duration := fun _ => 1

def current : Current := ⟨(fun person _ => if person then 1 else 2), (fun _ _ _ => 0), (), 0, 0⟩
def body : List Input :=
  [⟨false, [], false, [], .transfer false true [((), 1)]⟩,
   ⟨true, [], true, [], .transfer true false [((), 1)]⟩,
   ⟨true, [], true, [], .use true [((), 1)] .necessity⟩]

def item (index : Fin 3) := itemAt law current body index

def proposal : Proposal law current body where
  access := {
    access := item 0
    necessity := item 2
    mode := .acquired
    accessHolder := true
    recipient := true
    port := false
    accessGood := ()
    necessityGood := ()
    delivery := [] }
  reciprocity := .returnFlow () () [⟨item 1, (false, ())⟩]
  disposal := {
    position := item 0
    request := ⟨false, [], false, [], .use false [((), 1)] .external⟩
    good := () }

theorem source_checks : proposal.Checks law current body := by decide +kernel

def generated : CapitalRelationKernel law current body :=
  (compile law current body proposal).get (by simp [compile, source_checks])

theorem source_generates_controlled_existing_stock_access :
    compile law current body proposal = some generated ∧
    ∀ request ∈ body, ∀ person, request.operation ≠ .produce person := by
  refine ⟨?_, ?_⟩
  · simp [generated, compile, source_checks]
  · simp [body]

#print axioms source_generates_controlled_existing_stock_access

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Consumers.StoredAccess
