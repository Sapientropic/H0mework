import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Run.History

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]

local notation "History" => Script Party Good Port Technology Instrument

variable {seed : Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

/-- Continue from a retained visit. Each new input takes the whole prior
state, including the original positions and already paid dispositions. -/
def resume {past : History} (state : State seed community past) (suffix : History) :
    State seed community (past ++ suffix) :=
  List.reverseRecOn (motive := fun tail => State seed community (past ++ tail)) suffix
    ((List.append_nil past).symm ▸ state)
    (fun front input previous => List.append_assoc past front [input] ▸ advance previous input)

private theorem run_reindex {before after : History} (same : before = after) :
    (same ▸ run seed community before : State seed community after) = run seed community after := by
  cases same
  rfl

theorem resume_consumes_the_original_ledger (past suffix : History) :
    resume (run seed community past) suffix = run seed community (past ++ suffix) := by
  induction suffix using List.reverseRecOn with
  | nil => rw [resume, List.reverseRecOn_nil]; exact run_reindex _
  | append_singleton front input earlier =>
    rw [resume, List.reverseRecOn_concat]
    change (List.append_assoc past front [input] ▸ advance (resume (run seed community past) front) input :
      State seed community (past ++ (front ++ [input]))) = _
    rw [earlier, ← run_snoc]
    exact run_reindex _

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual
