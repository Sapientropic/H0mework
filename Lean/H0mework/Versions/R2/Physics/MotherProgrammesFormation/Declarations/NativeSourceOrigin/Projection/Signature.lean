import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Projection.Factory

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherProjectionOrigin
open MotherNetworkFactory MotherFullCompiler MotherSourcePrograms
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeLedgerSource N V}

abbrev ActiveTotal (law : SourceNativeProjectionLaw source) :=
  Σ projection : law.Projection, Σ point : Point source.source, law.ActiveAt projection point.2

abbrev InactiveTotal (law : SourceNativeProjectionLaw source) :=
  Σ projection : law.Projection, Σ point : Point source.source, law.InactiveAt projection point.2

abbrev PayloadTotal (law : SourceNativeProjectionLaw source) :=
  Σ projection : law.Projection, Σ point : Point source.source, Σ active : law.ActiveAt projection point.2,
    law.PayloadAt projection point.2 active

abbrev Total (law : SourceNativeProjectionLaw source) :=
  law.Projection ⊕ ActiveTotal law ⊕ InactiveTotal law ⊕ PayloadTotal law

structure Encoding (law : SourceNativeProjectionLaw source) where
  projection : law.Projection ↪ B
  active : ActiveTotal law ↪ B
  inactive : InactiveTotal law ↪ B
  payload : PayloadTotal law ↪ B

structure Presentation (old generated : SourceNativeProjectionLaw source) where
  projection : old.Projection ≃ generated.Projection
  active : ∀ p (point : Point source.source), old.ActiveAt p point.2 ≃ generated.ActiveAt (projection p) point.2
  inactive : ∀ p (point : Point source.source), old.InactiveAt p point.2 ≃ generated.InactiveAt (projection p) point.2
  payload : ∀ p (point : Point source.source) (value : old.ActiveAt p point.2),
    old.PayloadAt p point.2 value ≃ generated.PayloadAt (projection p) point.2 (active p point value)
  classify : ∀ p (point : Point source.source), generated.classify (projection p) point.2 =
    (Equiv.sumCongr (active p point) (inactive p point)) (old.classify p point.2)
  project : ∀ p (point : Point source.source) (value : old.ActiveAt p point.2),
    generated.project (projection p) point.2 (active p point value) = payload p point value (old.project p point.2 value)

namespace Encoding
variable (old : SourceNativeProjectionLaw source) (encode : Encoding old)

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
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherProjectionOrigin
