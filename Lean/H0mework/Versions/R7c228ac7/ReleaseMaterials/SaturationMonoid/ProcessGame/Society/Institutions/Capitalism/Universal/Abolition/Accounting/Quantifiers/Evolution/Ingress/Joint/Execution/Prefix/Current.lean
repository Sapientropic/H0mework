import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Prefix.Cut
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Prefix.Priority
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Global.Seed
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Prefix
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Prefix

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))

def baseFrame := Abolition.Accounting.Completion.currentFamily seed.input seed.depth seed.count seed.claim []

def sourcePast : List (Compile.RawInput Party Good Port Technology Instrument) :=
  cutPast seed.input seed.depth seed.count ++ [.execute []] ++
    priorityPast seed.input seed.claim (baseFrame seed) seed.inputs

def sharedState := Physical.Public.stateAt seed.input seed.depth seed.count 0 0 [] (sourcePast seed)
def sharedCursor := Physical.Prefix.cursor (sourcePast seed)

theorem the_initial_repair_has_the_original_full_empty_period :
    (Abolition.Accounting.Root.Reentry.Frame.state seed.claim (baseFrame seed)).raw =
      (Physical.Public.interpreter seed.input).next (sourceRaw seed.input seed.depth seed.count) [] := by
  unfold baseFrame
  rw [Abolition.Accounting.Completion.current_family_is_the_actual_observed_row]
  rfl

theorem the_complete_actual_source_history_reads_the_single_shared_raw :
    (sharedState seed).raw = (Abolition.Accounting.Root.Reentry.Frame.state seed.claim seed.current).raw := by
  have emptyPeriod := the_original_public_compiler_accepts_its_checked_word seed.input
    (cutState seed.input seed.depth seed.count) [] (by simp) (by simp [RawLaw.rawItems,RawLaw.execute])
  have initialRaw :
      (Physical.Public.compile seed.input (cutState seed.input seed.depth seed.count) (.execute [])).next.raw =
        (Abolition.Accounting.Root.Reentry.Frame.state seed.claim (baseFrame seed)).raw := by
    rw [emptyPeriod.2,the_source_generated_prefix_reads_the_original_financial_next]
    exact (the_initial_repair_has_the_original_full_empty_period seed).symm
  have actual := the_actual_priority_history_generates_its_own_public_representation seed.input seed.claim
    (baseFrame seed) seed.inputs _ initialRaw rfl
  simpa only [sharedState,sourcePast,Physical.Public.stateAt,cutState,Global.Seed.current,
    baseFrame,List.foldl_append,List.foldl_cons,List.foldl_nil] using actual

def tag (word : RawEvent Party Good Port Technology Instrument) : Epoch.Interface.Tag seed.input seed.depth seed.count :=
  .publicActual 0 0 [] (Physical.receive (sharedCursor seed) (.execute word))

def visit (word : RawEvent Party Good Port Technology Instrument) :=
  (Epoch.Interface.root seed.input seed.depth seed.count (tag seed word)).initialVisit

theorem the_public_financial_visit_reads_the_original_live_shared_current
    (word : RawEvent Party Good Port Technology Instrument) :
    Epoch.Interface.rawAt seed.input seed.depth seed.count (tag seed word) (visit seed word).current =
      (Abolition.Accounting.Root.Reentry.Frame.state seed.claim seed.current).raw := by
  change (Physical.Public.stateAt seed.input seed.depth seed.count 0 0 [] (sharedCursor seed).past).raw = _
  unfold sharedCursor
  rw [Physical.Prefix.past_readback]
  exact the_complete_actual_source_history_reads_the_single_shared_raw seed

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Prefix
