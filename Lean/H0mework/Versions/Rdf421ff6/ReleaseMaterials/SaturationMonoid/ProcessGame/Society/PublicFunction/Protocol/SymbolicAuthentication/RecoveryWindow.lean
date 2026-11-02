import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SupplyService

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecoveryWindow

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code) (observed : BatchReentry.Stages model) (retainedAt : Nat)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)
  (target : Fin model.source.code.sites)

abbrev entry := observed.take retainedAt
abbrev fuel := (EventStep.seed (EventHistory.execute start observed)).remaining
def supplyCount := min (2 * model.source.code.sites) (fuel model start observed)
def serviceCount := min (2 * model.source.code.sites) (fuel model start observed - supplyCount model start observed)
abbrev supplyEnd := observed.length + supplyCount model start observed

-- Only the source clock fixes the two local phases; no hypothetical future is run.
def program : List (Rule model.source.code) :=
  List.replicate (supplyCount model start observed) (LocalSupply.protocol vocabulary law start observed) ++
    List.replicate (serviceCount model start observed)
      (RetainedIntent.protocol vocabulary encoding law start (entry model observed retainedAt))

theorem the_source_clock_bounds_the_complete_local_program :
    (program model start observed retainedAt vocabulary encoding law).length ≤ fuel model start observed ∧
    (program model start observed retainedAt vocabulary encoding law).length ≤ 4 * model.source.code.sites := by
  simp only [program, List.length_append, List.length_replicate]
  have first := Nat.min_le_left (2 * model.source.code.sites) (fuel model start observed)
  have second := Nat.min_le_left (2 * model.source.code.sites) (fuel model start observed - supplyCount model start observed)
  have firstFuel : supplyCount model start observed ≤ fuel model start observed := Nat.min_le_right _ _
  have secondFuel : serviceCount model start observed ≤ fuel model start observed - supplyCount model start observed := Nat.min_le_right _ _
  change supplyCount model start observed ≤ _ at first
  change serviceCount model start observed ≤ _ at second
  omega

def supplyRows (past : BatchReentry.Stages model) :=
  (((StageTrace.records start past).drop observed.length).take (supplyCount model start observed)).filter
    (fun row => row.submitted != [] && (StageTrace.activation row).isSome)

def served (past : BatchReentry.Stages model) : Prop :=
  ∃ index ∈ List.range past.length, supplyEnd model start observed ≤ index ∧ ∃ row,
    (StageTrace.records start past)[index]? = some row ∧ StageTrace.activation row = some target ∧
    row.submitted = RetainedIntent.intent vocabulary encoding law start (entry model observed retainedAt) target ∧
    (∀ item ∈ StageTrace.items row, model.source.code.law.Valid item.before item.request) ∧
    ∃ stage, past[index]? = some stage ∧ IncidentResponse.sameRule model stage.1
      (RetainedIntent.protocol vocabulary encoding law start (entry model observed retainedAt)) = true
instance (past : BatchReentry.Stages model) : Decidable (served model start observed retainedAt vocabulary encoding law target past) := by
  unfold served; infer_instance

def Goal (past : BatchReentry.Stages model) : Prop :=
  retainedAt ≤ observed.length ∧ supplyEnd model start observed ≤ past.length ∧
    RetainedIntent.intent vocabulary encoding law start (entry model observed retainedAt) target ≠ [] ∧
    ¬ (∀ item ∈ model.source.code.law.rawItems (EventStep.seed (EventHistory.execute start observed)).current
      (RetainedIntent.intent vocabulary encoding law start (entry model observed retainedAt) target),
        model.source.code.law.Valid item.before item.request) ∧
    served model start observed retainedAt vocabulary encoding law target past ∧
    (supplyRows model start observed past).isEmpty = false ∧
    ∀ row ∈ supplyRows model start observed past,
      SupplyService.toTarget model start observed retainedAt vocabulary encoding law target row = true ∧
      ∀ item ∈ StageTrace.items row, model.source.code.law.Valid item.before item.request
instance (past : BatchReentry.Stages model) : Decidable (Goal model start observed retainedAt vocabulary encoding law target past) := by
  unfold Goal; infer_instance

def fulfilled (past : BatchReentry.Stages model) := decide (Goal model start observed retainedAt vocabulary encoding law target past)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecoveryWindow
