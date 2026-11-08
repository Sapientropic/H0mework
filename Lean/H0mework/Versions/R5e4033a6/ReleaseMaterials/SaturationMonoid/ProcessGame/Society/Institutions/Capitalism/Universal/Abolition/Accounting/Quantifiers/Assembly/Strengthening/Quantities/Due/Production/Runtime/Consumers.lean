import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Runtime.Compiled
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Runtime.ScheduleConsumer
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Floor.Forecast.Runtime.Original
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Floor.Forecast.Runtime.Fixture
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Authority
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Stock
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Funding
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Floor.Forecast.Use
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Consumers.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Runtime.Consumers

open Source.Program Abolition.Root Abolition.Root.Registered
open Service.Floor.Runtime.Consumers (numericCut numericRows numericWord otherUse numericOpening)

private def sourceLaw : RawLaw Bool Bool Bool Unit Unit :=
  Physical.Public.interpreter Abolition.Accounting.Quantifiers.Joint.Consumers.Compact.input

private def shortLife : Request Bool Bool Bool Unit Unit :=
  ⟨false, [], false, [], .use false [(true, 1 / 2)] .necessity⟩

inductive Result
  | ready
  | stock (bearer good : Bool) (missing : ℚ)
  | authority (ordinal : Nat) (signer : Bool)
  deriving Repr

def inspect (word : RawEvent Bool Bool Bool Unit Unit) : Result :=
  match inspectRawPayment numericCut numericRows sourceLaw word numericOpening with
  | .ready _ _ => .ready
  | .stock issue => .stock issue.address.1 issue.address.2
      (Service.Floor.Runtime.chargeRows numericRows word issue.address - numericCut.stock issue.address.1 issue.address.2)
  | .refused issue => .authority issue.original.index issue.original.request.signer

private def ready : Bool :=
  match inspect numericWord with
  | .ready => true
  | _ => false

private def protectsFood : Bool :=
  match inspect [otherUse] with
  | .stock false true missing => decide (missing = 1)
  | _ => false

private def respectsWholeUse : Bool :=
  match inspect [shortLife] with
  | .authority 0 false => true
  | _ => false

/-- info: (true, true, true) -/
#guard_msgs in
#eval (ready, protectsFood, respectsWholeUse)

private def atOriginalClock (deadline : ℚ) : Nat × Nat :=
  let input := ScheduleConsumer.input deadline
  let read := Service.Floor.Runtime.Consumers.originalPaidCut
  match readAndInspect input.clock input.rows (fun row => row.remaining)
      (fun row => row.earliest) (fun row => row.deadline)
      (fun row => nativeRequest row.signed row.bearer row.good row.remaining row.purpose)
      read.current read.rows sourceLaw Service.Floor.Runtime.Consumers.paid_numeric_opening with
  | .inl _ => (1, 0)
  | .inr ⟨word, .ready _ _⟩ => (0, word.length)
  | .inr ⟨_, .stock _⟩ => (2, 0)
  | .inr ⟨_, .refused _⟩ => (3, 0)

/-- info: ((0, 1), (1, 0), 0, 0) -/
#guard_msgs in
#eval (atOriginalClock 4, atOriginalClock 3, atOriginalClock 5)

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Runtime.Consumers
