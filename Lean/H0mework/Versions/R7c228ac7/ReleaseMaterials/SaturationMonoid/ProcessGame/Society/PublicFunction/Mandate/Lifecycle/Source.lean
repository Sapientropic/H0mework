import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.NativeRuntime
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.History

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 5000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Source

open Institutions.Capitalism.Universal.Source.Program
open Mandate.Source

def initial : Current := {Mandate.Source.initial with stock := fun _ _ => 10}

/-- Primitive requests use the preceding actual step, including its resource
debit. This bootstrap is executed; its success is not a source premise. -/
def bootstrap : List Action := Id.run do
  let proposal := request scope initial false (.propose true)
  let offered := Mandate.Source.law.step initial proposal
  let acceptance := request scope offered true .accept
  let held := Mandate.Source.law.step offered acceptance
  let proposalAgain := request scope held false (.propose true)
  let reoffered := Mandate.Source.law.step held proposalAgain
  let renewal := request scope reoffered true .renew
  let renewed := Mandate.Source.law.step reoffered renewal
  let exit := request scope renewed true .exit
  let exited := Mandate.Source.law.step renewed exit
  return [proposal, acceptance, proposalAgain, renewal, exit, request scope exited false .review]

def alphabet (current : Current) : List Action :=
  offerAcceptanceAlphabet base scope current [false] ++
    [{necessity with signer := false}, {maintenance with signer := false}]

def source : OutstandingSource Bool Unit Port (State Bool Unit) Unit where
  seed := {
    law := Mandate.Source.law
    initial := initial
    task := task
    actionsAt := alphabet
    budget := 4
    original := oldRequest :: bootstrap
    refused := by decide +kernel }
  positive := positive_task

def bound : BoundSource base scope := ⟨source, rfl⟩
def currentAt (visit : Nat) := source.currentAt (visit + 1)
def wordAt (visit : Nat) := (source.actualExecution visit).submitted
def grants (visit : Nat) := grantsAt base scope (currentAt visit) (wordAt visit)

theorem one_original_grant : (grants 0).length = 1 := by decide +kernel

def grant : Grant base scope (currentAt 0) (wordAt 0) :=
  (grants 0).get ⟨0, by rw [one_original_grant]; decide⟩

def admitted := admitGrant base scope _ _ grant
def history (last : Nat) := through (base := base) (scope := scope)
  (currentAt := currentAt) (wordAt := wordAt) (birth := 0) (grant := grant) last

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Source
