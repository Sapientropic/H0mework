import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.AuthorityCoordinates.Output
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.AuthorityRoot.Header

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAuthorityCoordinates
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section
variable {rank : Ordinal.{0}} {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {root : SourceNativeAuthoritativeRootClosure N V}
    (material : MotherArenaHigher.Material rank) (output : Output)
    (formed : MotherArenaTheory.formTheory material = some output)
    (p : MotherAuthorityRoot.Presentation root output.1.1 output.1.2 output.2)

/-- Original indices acquire coordinates by inverse restriction of the
actual generated root; no address premise is added to the source law. -/
def occurrence (current : V.Current) : root.toRoot.actual.OccurrenceAt current ↪ MotherArenaHigher.Base rank :=
  (p.represented.event current).toEmbedding.trans
    ((sourceCoordinates material output formed).represented.event (p.vocabulary.current current))

def entry (support : N.Support) : OpenResponsibilityAt N support ↪ MotherArenaHigher.Base rank :=
  (p.network.ledger support).toEmbedding.trans
    ((ledgerCoordinates material output formed).entry (p.network.support support))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAuthorityCoordinates
