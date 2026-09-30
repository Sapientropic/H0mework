import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaProjection.Factory
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Projection.Signature

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaProjection
open MotherArenaNetwork MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherArenaPrograms
open MotherPatchInventory
open MotherProjectionOrigin
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeLedgerSource N V}

structure Encoding (law : SourceNativeProjectionLaw source) where
  projection : law.Projection ↪ B
  active : ActiveTotal law ↪ B
  inactive : InactiveTotal law ↪ B
  payload : PayloadTotal law ↪ B

namespace Encoding
variable (old : SourceNativeProjectionLaw source) (encode : Encoding (rank := rank) old)

def activeAt (p : old.Projection) (point : Point source.source) : old.ActiveAt p point.2 ↪ B :=
  (Function.Embedding.sigmaMk point).trans ((Function.Embedding.sigmaMk p).trans encode.active)

def inactiveAt (p : old.Projection) (point : Point source.source) : old.InactiveAt p point.2 ↪ B :=
  (Function.Embedding.sigmaMk point).trans ((Function.Embedding.sigmaMk p).trans encode.inactive)

def payloadAt (p : old.Projection) (point : Point source.source) (active : old.ActiveAt p point.2) :
    old.PayloadAt p point.2 active ↪ B :=
  (Function.Embedding.sigmaMk active).trans
    ((Function.Embedding.sigmaMk point).trans ((Function.Embedding.sigmaMk p).trans encode.payload))
end Encoding

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaProjection
