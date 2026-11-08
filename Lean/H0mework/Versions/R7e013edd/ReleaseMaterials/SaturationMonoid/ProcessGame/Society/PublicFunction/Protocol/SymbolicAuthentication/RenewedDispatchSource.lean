import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WorkDispatch
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DispatchWindowConsumer

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RenewedDispatchSource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation

abbrev old := DispatchWindowSource.code
variable (saved : Cursor old)
-- New packet addresses begin after the preserved, already delivered old packets.
def firstSerial := (EventStep.seed saved).frame.sent.length
def catalogue : CatalogueHandoffSource.Catalogue old :=
  ⟨[],0,[],0,(List.range (old.sites * old.sites)).map fun offset => .deliver (firstSerial saved+offset)⟩
abbrev code := CatalogueHandoffSource.code old (catalogue saved)
def start := CatalogueHandoffSource.cursor old (catalogue saved) saved
def model : Native.Authority.Bound (Party := Bool) (Good := Bool)
  (Port := ProductiveMandateSource.Port) (Technology := Bool) (Instrument := Unit) :=
  ⟨ProductiveMandateSource.base,ProductiveMandateSource.scope,(start saved).source,rfl,rfl⟩
def scope : Scope := {ProductiveDispatchSource.scope with phase := saved.cut}
def vocabulary : OwnedAttestation.Vocabulary (Party := Bool) (Good := Bool)
  (Port := ProductiveMandateSource.Port) (Technology := Bool) (Instrument := Unit) :=
  ⟨fun port => match port with | .resource _ => some (scope saved,true) | _ => none,
    fun current => current.technology.version,true⟩
def law : StageReception.Law (code saved) := ⟨fun _ _ => scope saved,1⟩
abbrev work := ProductiveMandateSource.body.take 4
abbrev State := LocalCommandRun.State (model saved) (start saved)
abbrev choose := WorkDispatch.choose (model saved) (start saved) (vocabulary saved) (law saved) work
abbrev journey := WorkDispatch.journey (model saved) (start saved) (vocabulary saved) (law saved) work
abbrev admitted := WorkDispatch.admitted (model saved) (start saved) (vocabulary saved) (law saved) work
def empty := LocalCommandRun.initial (model saved) (start saved)
def attempt := LocalCommandSource.observe (model saved) (start saved) (.command 0)
def initial := LocalCommandRun.step (model saved) (start saved) (empty saved) (.command 0)
def actual := (journey saved (initial saved) 21).1
def observed (state : State saved) (receiver : Fin (code saved).sites) :=
  HeaderReception.run (vocabulary saved) (law saved) (start saved) state.stages receiver state.stages.length
def decideAt (state : State saved) (receiver : Fin (code saved).sites) :=
  HeaderQuorum.produce (start saved) (vocabulary saved) (law saved) state.stages receiver (scope saved) 2
def zero : Fin (code saved).sites := ⟨0,by change 0 < 2;decide⟩
def one : Fin (code saved).sites := ⟨1,by change 1 < 2;decide⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RenewedDispatchSource
