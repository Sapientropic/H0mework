import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Source
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Opening.Anchor
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Opening.Archive

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff

open Source.Program Innovation Quantifiers.Joint Quantities
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro PublicFunction
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument TaskId : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Technology] [DecidableEq TaskId]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))
  (enough : Planning.Enough seed claim (Evolution.Ingress.Joint.Material.shared seed claim))
  (reader : Macro.Raw.Reader seed.input seed.depth seed.count)
  (start : Nat) (sameCut : seed.count = Opening.cut seed.input seed.depth start ∨
    seed.count + 1 = Opening.cut seed.input seed.depth start)

local notation "original" => Evolving.Epoch.Source.initial (Evolving.Source.initial seed claim enough reader)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

variable (reported : Opening.Matrix Instrument Party)
  (genesis : Opening.Support (Opening.genesisRaw seed.input) (Opening.genesisCarried seed.input))
  (archive : Opening.Support reported (Opening.carriedAtCut seed.input seed.depth start))

inductive Ingress (Candidate : Type*)
  | checked (opening : Opening.CertifiedReading seed.input seed.depth start reported)
      (nativeRun : Nonempty ((Epoch.Finance.process seed.input seed.depth seed.count).Run
        (Opening.alignedOpening seed start opening.original).current
        (Clearing.nativeAccountFace (original).native).rootRead.current))
      (choice : Candidate)
  | unproven (issue : Opening.Unresolved seed.input genesis)
  | conflicting (first : Opening.Address Instrument Party) (rest : List (Opening.Address Instrument Party))
      (exactReport : Opening.discrepancies archive = first :: rest)

/-- The old archive and genesis are checked before inspecting the migration
menu. A matched reading runs into the installed financial face at its own cut. -/
def selectAtOpening (candidates : List (Proposal Party Good Port Technology Instrument))
    (ordered : List TaskId) (task : TaskId → PublicTaskSpec Party Good)
    (reserved : ∀ word : Script, Finset (Due.Service.Ordinal (original) word))
    (held : Finset (Due.Service.Need ordered.toFinset task)) (budget : Party × Good → ℚ) (deadline : WithTop ℚ) :
    Ingress seed claim enough reader start reported genesis archive
      (Selection (original) ordered task reserved held budget deadline candidates (handoffTime (original))) :=
  match Opening.reopenAt seed.input seed.depth start reported genesis archive with
  | .unproven issue => .unproven issue
  | .conflicting first rest exactReport => .conflicting first rest exactReport
  | .certified opening =>
    .checked opening
      (Opening.original_opening_runs_to_the_installed_face seed claim enough reader start opening.original sameCut)
      (select (original) ordered task reserved held budget deadline candidates (handoffTime (original)))

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff
