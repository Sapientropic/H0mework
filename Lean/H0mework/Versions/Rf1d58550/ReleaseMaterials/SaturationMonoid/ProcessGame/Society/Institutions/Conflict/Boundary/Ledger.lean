import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary.Defence
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Composition
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Advance

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]

local notation "primitive" => Quantities.Execution.primitiveScript
local notation "endAt" => Quantities.Execution.endAt

variable {source : Root.Cut Party Good Port Technology Instrument}
  {attackWord response continuation : RawEvent Party Good Port Technology Instrument}
  {community : Party → Community}
  {attack : AggressionAt source attackWord community}

/-- Three consecutive original occurrences write one composed ledger. The
exit cut is the generated successor of the actual defensive payment. -/
theorem DefenceAt.the_same_root_writes_attack_defence_and_exit
    (defended : DefenceAt attack response continuation) :
    Quantities.Settled source (primitive (attackWord ++ response ++ continuation)) ∧
      endAt source (primitive (attackWord ++ response ++ continuation)) =
        Root.terminal (Root.terminal attack.after response) continuation := by
  simp only [Quantities.Execution.primitiveScript_append, Quantities.Execution.endAt_append]
  have maintained := Quantities.Due.Production.append_settled source (primitive attackWord) (primitive response)
    attack.paid.whole defended.responsePaid.whole
  refine ⟨Quantities.Due.Production.append_settled source _ (primitive continuation) maintained ?_, trivial⟩
  rw [Quantities.Execution.endAt_append]
  exact defended.independentExit.paid.whole

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary
