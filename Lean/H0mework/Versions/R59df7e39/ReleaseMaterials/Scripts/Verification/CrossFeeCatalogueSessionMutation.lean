import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering.Quoted
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option linter.unusedVariables false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering.CatalogueSource
variable {A : Type} {input : Input A}
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionMutation.case001 (made : Execution input) : True := by
  fail_if_success exact (⟨made.endpoint,made.work,made.history,made.stopped⟩ : Execution input)
  trivial
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionMutation.case002 (session : Session input) : True := by
  fail_if_success exact (⟨session.current,session.work,session.history⟩ : Session input)
  trivial
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionMutation.case003 (other : Input A) (made : Execution input) : True := by
  fail_if_success exact (made : Execution other)
  trivial
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionMutation.case004 (other : Input A) (session : Session input) : True := by
  fail_if_success exact (session : Session other)
  trivial
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionMutation.case005 (endpoint : Cursor A) : True := by
  fail_if_success exact (⟨endpoint,[]⟩ : Execution input)
  trivial
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionMutation.case006 (endpoint : Cursor A) : True := by
  fail_if_success exact (⟨endpoint,[]⟩ : Session input)
  trivial
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionMutation.case007 : (execute (⟨[1,2],9,2,[0],3⟩ : Input Nat)).rows = [[],[1],[1,1],[1,2],[2],[2,1],[2,2]] := by rw [Execution.rows_exact];rfl
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionMutation.case008 : (execute (⟨[1,1],9,1,[0],0⟩ : Input Nat)).rows = [[],[1],[1]] := by rw [Execution.rows_exact];rfl
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionMutation.case009 : (execute (⟨[],9,3,[0,1,2],2⟩ : Input Nat)).rows = [[],[9],[9,9]] := by rw [Execution.rows_exact];rfl
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionMutation.case010 : (execute (⟨[1],9,1,[0,0],0⟩ : Input Nat)).rows = [[],[1],[],[1]] := by rw [Execution.rows_exact];rfl
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionMutation.case011 : (execute (⟨[1],9,2,[],4⟩ : Input Nat)).rows = [] := by rw [Execution.rows_exact];rfl
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionMutation.case012 : (execute (⟨[],9,3,[2],2⟩ : Input Nat)).units = 12 := by rw [Execution.units_exact,Execution.rows_exact];rfl
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionMutation.case013 (input : Input A) : (Session.initial input).completed = none := rfl
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionMutation.case014 (input : Input A) : (Session.initial {input with counts := []}).move.map Prod.fst = some .closed := rfl
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionMutation.case015 (input : Input A) (count : Nat) (rest : List Nat) : (Session.initial {input with counts := count::rest}).move.map Prod.fst = some (.counted count) := rfl
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionMutation.case016 (input : Input A) (count : Nat) (rest : List Nat) : ((Session.initial {input with counts := count::rest}).move.bind (fun made => made.2.move.map Prod.fst)) = some (.emitted (List.replicate count input.work)) := by cases input with | mk menu work depth counts pending => cases depth <;> simp [Session.initial,Session.move,CatalogueSource.initial,Cursor.move]
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering.CatalogueSource

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering.NativeProgram
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {old : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {R : Type} {depth : Nat} {code : Code (old := old) R depth}
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionMutation.case017 (value : R) : True := by
  fail_if_success exact (Execution.done value : Execution (.done value : Code (old := old) R depth))
  trivial
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionMutation.case018 (session : Session code) : True := by
  fail_if_success exact (⟨session.current,session.history⟩ : Session code)
  trivial
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionMutation.case019 (other : Code (old := old) R depth) (session : Session code) : True := by
  fail_if_success exact (session : Session other)
  trivial
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionMutation.case020 (other : Code (old := old) R depth) (made : Execution code) : True := by
  fail_if_success exact (made : Execution other)
  trivial
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionMutation.case021 (input : CatalogueSource.Input (Action old)) (value : R) : True := by
  fail_if_success exact (CatalogueSource.execute input : Execution (.done value : Code (old := old) R depth))
  trivial
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionMutation.case022 (input : CatalogueSource.Input (Action old)) (value : R) : True := by
  fail_if_success exact (CatalogueSource.Session.initial input : Session (.done value : Code (old := old) R depth))
  trivial
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionMutation.case023 (input : CatalogueSource.Input (Action old)) (next : CatalogueSource.Execution input → Code (old := old) R depth) :
    (Session.initial (.catalogue input next)).completed = none := rfl
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionMutation.case024 (input : CatalogueSource.Input (Action old)) (next : CatalogueSource.Execution input → Code (old := old) R depth) :
    (Cursor.cataloguing (next := next) (CatalogueSource.Session.initial input)).completed = none := rfl
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionMutation.case025 (input : CatalogueSource.Input (Action old)) (next : CatalogueSource.Execution {input with counts := []} → Code (old := old) R depth) :
    (Cursor.ready (.catalogue {input with counts := []} next)).move.map Prod.fst = some (.catalogue .closed) := by
  simp [Cursor.move,CatalogueSource.Session.initial,CatalogueSource.Session.move,CatalogueSource.Cursor.move,CatalogueSource.initial]
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionMutation.case026 (input : CatalogueSource.Input (Action old)) (count : Nat) (rest : List Nat)
    (next : CatalogueSource.Execution {input with counts := count::rest} → Code (old := old) R depth) :
    (Cursor.ready (.catalogue {input with counts := count::rest} next)).move.map Prod.fst = some (.catalogue (.counted count)) := by
  simp [Cursor.move,CatalogueSource.Session.initial,CatalogueSource.Session.move,CatalogueSource.Cursor.move,CatalogueSource.initial]
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering.NativeProgram
