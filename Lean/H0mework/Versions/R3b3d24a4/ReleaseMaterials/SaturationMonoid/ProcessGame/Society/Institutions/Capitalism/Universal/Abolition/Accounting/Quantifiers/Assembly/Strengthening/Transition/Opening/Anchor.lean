import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Opening.Compiler
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Opening.Ready
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Source.Current
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Source.Initial
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.RootFace

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Opening

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root
open Source.Program Innovation Quantifiers.Joint Evolution Evolution.Ingress.Joint Evolution.Ingress.Joint.Material
open Financial.Installation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))
  (enough : Planning.Enough seed claim (Material.shared seed claim))
  (reader : Registered.Macro.Raw.Reader seed.input seed.depth seed.count)

local notation "evolving" => Evolving.Epoch.Source.initial (Evolving.Source.initial seed claim enough reader)

variable (start : Nat)

def alignedOpening (_opening : Accepted seed.input seed.depth start) :
    (Epoch.Finance.process seed.input seed.depth seed.count).GeneratedState :=
  Epoch.Finance.Legacy.generated seed.input seed.depth seed.count (originalAccount seed.input seed.depth start)

variable (opening : Accepted seed.input seed.depth start)
  (atCut : seed.count = cut seed.input seed.depth start ∨ seed.count + 1 = cut seed.input seed.depth start)

include atCut

/-- The evolving root reads the account just after its original tick. The
archive can be at the tick's drained target or at an already drained cut
whose next inherited administrative item leaves the account intact. -/
theorem canonical_evolving_anchor :
    (evolving).native.frame.anchor = alignedOpening seed start opening := by
  have background : Background.account seed = originalAccount seed.input seed.depth start := by
    unfold Background.account
    rw [Background.the_actual_cursor_is_the_original_next_cursor]
    change (Cursor.next seed.input ((Runtime.frames seed.input seed.depth seed.count).cursor seed.input)).account = _
    rw [Runtime.frames_cursor]
    rcases atCut with atSource | atTarget
    · rw [atSource]
      exact the_original_next_reads_the_same_opening_GS seed.input seed.depth start
    · change (Runtime.cursorAt seed.input seed.depth (seed.count + 1)).account = _
      rw [atTarget]
      rfl
  exact congrArg (Epoch.Finance.Legacy.generated seed.input seed.depth seed.count) background

/-- The installed native-account face reads the target of a dependent Run
from the original opening. Its source, visit and account are already live. -/
theorem original_opening_runs_to_the_installed_face :
    Nonempty ((Epoch.Finance.process seed.input seed.depth seed.count).Run
      (alignedOpening seed start opening).current
      (Clearing.nativeAccountFace (evolving).native).rootRead.current) := by
  rw [← canonical_evolving_anchor seed claim enough reader start opening atCut]
  exact (evolving).native.actual.actual.native

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Opening
