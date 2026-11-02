import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Assembly.Current
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Replay.Public

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Assembly

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root
open Registered Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}

local notation "F" => Macro.Runtime.ActivatedFrame (review := review)
  input depth count prefixLimit renewalLimit sourceDepth sourceCount

/-- Read the existing physical occurrence used by this frame's native
inventory. No new occurrence identity or replacement account is constructed. -/
def sourceTag : F → Epoch.Interface.Tag input depth count
  | .original current => Macro.Inventory.tag (review := review) input depth count prefixLimit renewalLimit
      current.start current.proposal
  | .enacted origin _ current => Macro.Public.Accounting.tag input depth count prefixLimit renewalLimit
      origin.germ.snapshot.past current.start

def sourceVisit (state : F) := (Epoch.Interface.root input depth count (sourceTag state)).initialVisit
def sourceBody (state : F) := Epoch.Interface.body input depth count (sourceTag state) (sourceVisit state)

theorem the_function_source_uses_the_actual_interpreter (state : F) :
    Epoch.Interface.interpreter input depth count (sourceTag state) = state.interpreter := by
  cases state <;> rfl

/-- Prepayment, investment, coordination, risk, innovation and settlement
use the original instruction inventory and full material/claim state. Their
public replay preserves services and every original position without C. -/
theorem every_function_in_the_actual_source_has_a_public_functional_replacement
    (state : F) (members : List Party) (task : PublicFunction.PublicTaskSpec Party Good) :
    type_of% (Functions.Replay.every_actual_word_has_a_source_generated_public_functional_replay
      state.interpreter (sourceBody state).1 (sourceBody state).2 members task) ∧
      type_of% (Functions.Replay.every_replay_port_is_open_without_controller_consents
        state.interpreter (sourceBody state).1 (sourceBody state).2) :=
  ⟨Functions.Replay.every_actual_word_has_a_source_generated_public_functional_replay
    state.interpreter (sourceBody state).1 (sourceBody state).2 members task,
    Functions.Replay.every_replay_port_is_open_without_controller_consents
      state.interpreter (sourceBody state).1 (sourceBody state).2⟩

#print axioms sourceBody
#print axioms the_function_source_uses_the_actual_interpreter
#print axioms every_function_in_the_actual_source_has_a_public_functional_replacement

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Assembly
