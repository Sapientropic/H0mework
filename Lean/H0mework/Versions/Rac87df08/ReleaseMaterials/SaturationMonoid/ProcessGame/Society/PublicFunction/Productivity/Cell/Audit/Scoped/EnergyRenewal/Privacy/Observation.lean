import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy.Windows
import Lean.Data.Json

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root Lean

abbrev Item := ExecutionItem Party Good AuditPort (Mandate.State Party Technology) Unit

def snapshot (current : AuditCurrent) : Json := Json.mkObj
  [("clock",toJson (toString current.clock)),("round",toJson current.round),
   ("holder",toJson current.technology.holder),("offered",toJson current.technology.offered),
   ("version",toJson current.technology.version),
   ("energy",toJson ((List.range 4).map fun actor => toString (current.stock actor .energy))),
   ("labor",toJson ((List.range 4).map fun actor => toString (current.stock actor .labor)))]

def kind : Operation Party Good (Mandate.State Party Technology) Unit → String
  | .present => "submission" | .transfer .. => "transfer" | .use .. => "use"
  | .revise _ target => match target.last with
    | some .revoke => "revoke" | some (.propose _) => "propose" | some .accept => "accept" | _ => "revision"
  | _ => "other"

def rowJson (scope : Scope) (item : Item) : Json :=
  Json.mkObj [("index",toJson item.index),("signer",toJson item.request.signer),
    ("kind",toJson (kind item.request.operation)),("accepted",toJson (decide ((law scope).Valid item.before item.request))),
    ("energyDebit",toJson ((List.range 4).map fun actor => toString (flowAt ((law scope).actualDebit item.before item.request) actor .energy))),
    ("energyCredit",toJson ((List.range 4).map fun actor => toString (flowAt ((law scope).actualCredit item.before item.request) actor .energy)))]

theorem Twin.snapshot {left right : AuditCurrent} (same : Twin left right) : snapshot left = snapshot right := by
  simp only [Privacy.snapshot,same.clock,same.round,same.technology,
    same.stock _ .energy (by decide),same.stock _ .labor (by decide)]

structure ItemTwin (left right : Item) : Prop where
  index : left.index = right.index
  request : left.request = right.request
  before : Twin left.before right.before
  energy : EnergyAction left.request

theorem ItemTwin.row {left right : Item} (same : ItemTwin left right) (scope : Scope)
    (cost : scope.revisionCost = [(.energy,1)]) : rowJson scope left = rowJson scope right := by
  have valid := same.before.valid scope left.request (energy_public scope cost _ _ same.energy)
  simp only [rowJson,RawLaw.actualDebit,RawLaw.actualCredit,← same.request,valid,
    same.before.debit scope left.request,same.before.credit scope left.request,same.index]

theorem Twin.items {left right : AuditCurrent} (same : Twin left right) (scope : Scope)
    (cost : scope.revisionCost = [(.energy,1)]) (word : List Action)
    (energy : ∀ action ∈ word,EnergyAction action) (index : Nat) :
    List.Forall₂ ItemTwin ((law scope).execute left index word).items ((law scope).execute right index word).items := by
  induction word generalizing left right index with
  | nil => exact .nil
  | cons action rest ih =>
    apply List.Forall₂.cons
    · exact ⟨rfl,rfl,same,energy _ (by simp)⟩
    · exact ih (same.step _ _ (energy_public _ cost _ _ (energy _ (by simp))))
        (fun action inside => energy _ (List.mem_cons_of_mem _ inside)) (index+1)

theorem Twin.rows {left right : AuditCurrent} (same : Twin left right) (scope : Scope)
    (cost : scope.revisionCost = [(.energy,1)]) (word : List Action)
    (energy : ∀ action ∈ word,EnergyAction action) :
    ((law scope).rawItems left word).map (rowJson scope) = ((law scope).rawItems right word).map (rowJson scope) := by
  have mapped : ∀ {xs ys : List Item}, List.Forall₂ ItemTwin xs ys →
      xs.map (rowJson scope) = ys.map (rowJson scope) := by
    intro xs ys items
    induction items with
    | nil => rfl
    | cons h _ ih => simp only [List.map_cons,h.row scope cost,ih]
  exact mapped (same.items scope cost word energy 0)

/-- The complete stage is the original serializer's stage, with no field removed. -/
def stageJson (scope : Scope) (ordinal : Nat) (before : AuditCurrent) (word : List Action) : Json :=
  Json.mkObj [("ordinal",toJson ordinal),("before",snapshot before),
    ("rows",toJson (((law scope).rawItems before word).map (rowJson scope))),
    ("next",snapshot ((law scope).next before word))]

theorem Twin.stage {left right : AuditCurrent} (same : Twin left right) (scope : Scope)
    (cost : scope.revisionCost = [(.energy,1)]) (word : List Action)
    (energy : ∀ action ∈ word,EnergyAction action) (ordinal : Nat) :
    stageJson scope ordinal left word = stageJson scope ordinal right word := by
  simp only [stageJson,same.snapshot,same.rows scope cost word energy,
    (same.next scope cost word energy).snapshot]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy
