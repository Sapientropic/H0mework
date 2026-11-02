import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CompletionState

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InterferenceValidity

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)

open CompletionState

def served (entry past : BatchReentry.Stages model) (site : Fin model.source.code.sites) : Prop :=
  ∃ index ∈ List.range past.length,
    entry.length ≤ index ∧ ∃ row, (StageTrace.records start past)[index]? = some row ∧
      StageTrace.activation row = some site ∧
      row.submitted = RetainedIntent.intent vocabulary encoding law start entry site ∧
      (∀ item ∈ StageTrace.items row, model.source.code.law.Valid item.before item.request) ∧
      ∃ stage, past[index]? = some stage ∧
        IncidentResponse.sameRule model stage.1 (RetainedIntent.protocol vocabulary encoding law start entry) = true
instance (entry past : BatchReentry.Stages model) (site : Fin model.source.code.sites) :
    Decidable (served model start vocabulary encoding law entry past site) := by
  unfold served; infer_instance

def closed (state : State model) : Prop :=
  ∀ entry ∈ state.batches, ∀ site,
    RetainedIntent.intent vocabulary encoding law start entry site ≠ [] →
      served model start vocabulary encoding law entry state.past site
instance (state : State model) : Decidable (closed model start vocabulary encoding law state) := by
  unfold closed; infer_instance

def Goal (state : State model) : Prop :=
  CompletionState.Goal model start vocabulary encoding law state ∧ closed model start vocabulary encoding law state
instance (state : State model) : Decidable (Goal model start vocabulary encoding law state) := by
  unfold Goal; infer_instance

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InterferenceValidity
