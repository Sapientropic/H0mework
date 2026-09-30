import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.TheoryTransport.Presentation

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherTheoryTransport.Presentation
open ResponsibilityLifecycle LivingLawEvolution
noncomputable section

variable {N G : WorldRelationNetwork.{0}} {n : MotherNetworkOrigin.Presentation N G}
    {old : TheoryState N} {generated : TheoryState G} (p : Presentation n old generated)

def expressionTotal : MotherArenaTheory.ExpressionTotal old ≃ MotherArenaTheory.ExpressionTotal generated :=
  Equiv.sigmaCongr n.support p.expression

def realizationTotal : MotherArenaTheory.RealizationTotal old ≃ MotherArenaTheory.RealizationTotal generated :=
  Equiv.sigmaCongr n.support (fun support =>
    Equiv.sigmaCongr (n.obstructionAt support) (p.realization support))

def withoutTotal : MotherArenaTheory.WithoutTotal old ≃ MotherArenaTheory.WithoutTotal generated :=
  Equiv.sigmaCongr p.law (fun choice => Equiv.sigmaCongr n.support (fun support =>
    Equiv.sigmaCongr (n.obstructionAt support) (p.without choice support)))

def theoremTotal : MotherArenaTheory.TheoremTotal old ≃ MotherArenaTheory.TheoremTotal generated :=
  Equiv.sigmaCongr n.support (fun support =>
    Equiv.sigmaCongr (p.expression support) (p.theoremMember support))

/-- All six source-material address components are retained together. -/
def total : MotherArenaTheory.Total old ≃ MotherArenaTheory.Total generated :=
  Equiv.sumCongr p.version (Equiv.sumCongr p.law (Equiv.sumCongr p.expressionTotal
    (Equiv.sumCongr p.realizationTotal (Equiv.sumCongr p.withoutTotal p.theoremTotal))))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherTheoryTransport.Presentation
