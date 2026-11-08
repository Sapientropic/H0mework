import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PaidInvocationSource
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProductiveDispatchConsumer

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DispatchWindowSource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation
abbrev previous := ProductiveDispatchSource.actual
abbrev old := ProductiveDispatchSource.model.source.code
abbrev saved := previous.current ProductiveDispatchSource.model ProductiveDispatchSource.start

-- The service provider receives the unit and accepts the installed 1→36 tariff
-- in its own actual incoming occurrence; necessity consumption is not an invoice.
def payment : ProductiveMandateSource.Action :=
 ⟨true,[],.resource true,[.resource true],.transfer true false [(true,1)]⟩
def acceptance : ProductiveMandateSource.Action :=
 ⟨false,[],.resource false,[.resource false],.present⟩
def contract : PaidInvocationSource.Contract (Party := Bool) (Good := Bool)
 (Port := ProductiveMandateSource.Port) (Technology := Bool) (Instrument := Unit) :=
 ⟨true,false,true,1,36,payment,acceptance⟩
abbrev code := PaidInvocationSource.code old contract
abbrev start := PaidInvocationSource.start old contract saved
abbrev row := PaidInvocationSource.paymentRow old contract saved true
abbrev ack := PaidInvocationSource.acceptanceRow old contract saved true true
abbrev paid := PaidInvocationSource.paid old contract saved true true
abbrev admitted := PaidInvocationSource.admitted old contract saved true true
abbrev produce := PaidInvocationSource.produce old contract saved true true
abbrev initial := PaidInvocationSource.initial old contract saved true true
abbrev model (point : Cursor code) : Native.Authority.Bound (Party := Bool) (Good := Bool)
 (Port := ProductiveMandateSource.Port) (Technology := Bool) (Instrument := Unit) :=
 ⟨ProductiveMandateSource.base,ProductiveMandateSource.scope,point.source,rfl,rfl⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DispatchWindowSource
