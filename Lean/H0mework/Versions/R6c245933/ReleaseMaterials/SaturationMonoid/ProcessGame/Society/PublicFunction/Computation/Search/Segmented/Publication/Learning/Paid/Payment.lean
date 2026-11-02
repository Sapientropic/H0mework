import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Charge

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Payment
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (reader : Fin model.source.code.sites)
  (quote : Charge.Quote (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (point : View (code := model.source.code)) (rival : Opponent model.source.code)

theorem a_ready_actual_request_generates_its_own_charge_receipt
    (ready : Cut.Ready reader (Replay.inspect reader (Charge.fee quote) point rival)) :
    Charge.paid quote model reader point rival (Charge.endAt quote model reader point rival) := by
  have result : (Charge.trace quote reader point rival).result = some (.accepted (fun _ _ => trivial)) := by
    have ready' : Cut.Ready reader (Replay.inspect reader ((Charge.tariff quote).word () 1) point rival) := by
      have word : (Charge.tariff quote).word () 1 = Charge.fee quote := List.append_nil _
      rw [word]
      exact ready
    cases seen : Replay.inspect reader ((Charge.tariff quote).word () 1) point rival with
    | unsupported | withheld | refused => simp only [seen,Cut.Ready] at ready'
    | paid supported emitted legal =>
        have active : Cut.Ready reader (Replay.Attempt.paid supported emitted legal) := by simpa only [seen] using ready'
        have room := active.1
        simp only [Charge.trace,dif_neg room,seen,dif_pos active,Cut.Trace.result]
  unfold Charge.paid
  change ∃ checked, (Cut.Consumer.read model reader Charge.holds [()] (Charge.tariff quote) point rival
    (Charge.trace quote reader point rival) (Charge.endAt quote model reader point rival)).1 = some (.accepted checked)
  rw [Cut.Consumer.read_is_the_arrived_source_generated_outcome]
  change ∃ checked, (if Charge.endAt quote model reader point rival ≤ Charge.endAt quote model reader point rival
    then (Charge.trace quote reader point rival).result else none) = some (.accepted checked)
  rw [if_pos (Nat.le_refl _),result]
  exact ⟨_,rfl⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Payment
