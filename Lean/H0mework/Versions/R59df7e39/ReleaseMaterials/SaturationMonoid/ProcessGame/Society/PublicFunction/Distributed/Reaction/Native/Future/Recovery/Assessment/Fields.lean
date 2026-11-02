import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Assessment
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Window.Report.Manifest
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Assessment.Fields
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {old : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {oldDepth count : Nat} {target : Authority.Sources old.base old.scope} {word : List (Action old)}
  {receipt : Receipt old oldDepth target count word} (made : Output receipt) (start : Nat)
abbrev Cursor := Window.Report.Manifest.Cursor made.bound start (made.walk.finish.depth-start)
abbrev Completed := Window.Report.Manifest.Completed made.bound start (made.walk.finish.depth-start)
abbrev Event := Window.Report.Manifest.Event made.bound start (made.walk.finish.depth-start)
def initial : Cursor made start := Window.Report.Manifest.initial made.bound start (made.walk.finish.depth-start)
noncomputable def capacity := Window.Report.Manifest.capacity made.bound start (made.walk.finish.depth-start)
theorem initial_rank : (initial made start).rank = capacity made start := Window.Report.Manifest.initial_rank
private theorem transport_trans {α : Sort _} {F : α → Sort _} {a b c : α}
    (first : a = b) (second : b = c) (value : F a) :
    (first.trans second ▸ value : F c) = second ▸ (first ▸ value : F b) := by
  cases first;cases second;rfl
def report (sameCode : target.val.code = old.source.code) (cache : Completed made start) : Report old :=
  ⟨made.walk.finish.consumed.length,(made.source_code_is_the_target_code.trans sameCode) ▸ cache.evaluation⟩
theorem report_exact (sameCode : target.val.code = old.source.code) (cache : Completed made start) :
    report made start sameCode cache = reportFrom made start sameCode := by
  unfold report reportFrom Output.evaluationFrom
  rw [cache.evaluation_exact]
  congr 1
  exact transport_trans made.source_code_is_the_target_code sameCode _
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Assessment.Fields
