import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.HeaderQuorum
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProductiveMandateConsumer
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CatalogueHandoffSource

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProductiveHeaderSource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

abbrev old := ProductiveMandateSource.code
def zero : Fin old.sites := ⟨0,by decide⟩
def one : Fin old.sites := ⟨1,by decide⟩
def catalogue : CatalogueHandoffSource.Catalogue old :=
  ⟨[],0,[],0,[.send zero zero,.send one zero,.send zero one,.send one one,
    .deliver 0,.deliver 1,.deliver 2,.deliver 3]⟩
abbrev code := CatalogueHandoffSource.code old catalogue
def saved := (LocalCommandRun.step ProductiveMandateSource.model ProductiveMandateSource.start
  ProductiveMandateSource.worked (.command 6)).current ProductiveMandateSource.model ProductiveMandateSource.start

theorem saved_is_the_actual_generated_service_endpoint :
    saved = ProductiveMandateSource.after.current ProductiveMandateSource.model ProductiveMandateSource.start := by
  obtain ⟨receipt,produced⟩ := ProductiveMandateConsumer.the_actual_productive_source_generates_a_service_receipt
  have checked := ProductiveMandateChecks.the_generated_material_funds_the_original_native_service
  simp only [ProductiveMandateChecks.serviceView,produced] at checked
  have input := of_decide_eq_true checked
  change saved = ((ProductiveMandateSource.service).after ProductiveMandateSource.model
    ProductiveMandateSource.start ProductiveMandateSource.worked).current _ _
  rw [produced]
  change saved = (LocalCommandRun.step _ _ _ (NativeCommandCompiler.input _ _ _ receipt.ready)).current _ _
  rw [input]
  rfl

def start := CatalogueHandoffSource.cursor old catalogue saved
def model : Native.Authority.Bound (Party := Bool) (Good := Bool) (Port := ProductiveMandateSource.Port)
    (Technology := Bool) (Instrument := Unit) :=
  ⟨ProductiveMandateSource.base,ProductiveMandateSource.scope,start.source,rfl,rfl⟩
def scope : Scope := ⟨3,0,0⟩
def vocabulary : OwnedAttestation.Vocabulary (Party := Bool) (Good := Bool)
    (Port := ProductiveMandateSource.Port) (Technology := Bool) (Instrument := Unit) :=
  ⟨fun port => match port with | .resource _ => some (scope,true) | _ => none,
    fun current => current.technology.version,true⟩
def law : StageReception.Law code := ⟨fun _ _ => scope,1⟩
def inputs : List LocalCommandSource.Input :=
  [.idle,.command 4,.idle,.command 5,.idle,.event 3,.event 6,.event 2,.event 7,
   .event 5,.event 8,.event 4,.event 9]
def run (attempts : List LocalCommandSource.Input) := LocalCommandRun.run model start attempts
def actual := run inputs
def observed (receiver : Fin code.sites) := HeaderReception.run vocabulary law start actual.stages receiver actual.stages.length
def decideAt (receiver : Fin code.sites) := HeaderQuorum.produce start vocabulary law actual.stages receiver scope 2

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProductiveHeaderSource
