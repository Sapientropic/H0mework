import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaTheory.Encoding

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaTheory.Encoding
open MotherArenaNetwork
open ResponsibilityLifecycle LivingLawEvolution
noncomputable section
variable {rank : Ordinal.{0}} {N : WorldRelationNetwork.{0}}
    (coordinates : Coordinates (rank := rank) N) (old : TheoryState N) (encode : Encoding (rank := rank) old)
    {material : MotherArenaHigher.Material rank}
    (hm : MotherArenaHigher.read rank material = reader coordinates old encode)

def expressionEquiv (support : N.Support) : old.ExpressionAt support ≃ Expression coordinates material support :=
  MotherArenaNetworkOrigin.imageEquiv ((Function.Embedding.sigmaMk support).trans encode.expression)
    (fun code => r2 material 2 (coordinates.support support) code) (by
      intro code
      rw [r2, reader_bit coordinates old encode hm]
      simp only [graph, MotherArenaHigher.unpair_pair]
      constructor
      · rintro ⟨other, expression, same, selected⟩
        have same := coordinates.support.injective same
        cases same
        exact ⟨expression, selected⟩
      · rintro ⟨expression, selected⟩
        exact ⟨support, expression, rfl, selected⟩)

def realizationEquiv (support : N.Support) (obstruction : N.ObstructionAt support) :
    old.inventory.RealizationAt obstruction ≃ Realization coordinates material support obstruction :=
  MotherArenaNetworkOrigin.imageEquiv
    ((Function.Embedding.sigmaMk obstruction).trans ((Function.Embedding.sigmaMk support).trans encode.realization))
    (fun code => r3 material 3 (coordinates.support support) (coordinates.obstruction support obstruction) code) (by
      intro code
      rw [r3, reader_bit coordinates old encode hm]
      simp only [graph, MotherArenaHigher.unpair_pair]
      constructor
      · rintro ⟨other, event, value, same, eventEq, selected⟩
        have same := coordinates.support.injective same
        cases same
        have same := (coordinates.obstruction support).injective eventEq
        cases same
        exact ⟨value, selected⟩
      · rintro ⟨value, selected⟩
        exact ⟨support, obstruction, value, rfl, rfl, selected⟩)

def withoutEquiv (law : old.inventory.Law) (support : N.Support) (obstruction : N.ObstructionAt support) :
    old.inventory.RealizationWithoutAt law obstruction ≃
      RealizationWithout coordinates material (lawEquiv coordinates old encode hm law) support obstruction :=
  MotherArenaNetworkOrigin.imageEquiv
    ((Function.Embedding.sigmaMk obstruction).trans ((Function.Embedding.sigmaMk support).trans
      ((Function.Embedding.sigmaMk law).trans encode.without)))
    (fun code => r4 material 4 (encode.law law) (coordinates.support support) (coordinates.obstruction support obstruction) code) (by
      intro code
      rw [r4, reader_bit coordinates old encode hm]
      simp only [graph, MotherArenaHigher.unpair_pair]
      constructor
      · rintro ⟨otherLaw, other, event, value, lawEq, same, eventEq, selected⟩
        have sameLaw := encode.law.injective lawEq
        cases sameLaw
        have same := coordinates.support.injective same
        cases same
        have same := (coordinates.obstruction support).injective eventEq
        cases same
        exact ⟨value, selected⟩
      · rintro ⟨value, selected⟩
        exact ⟨law, support, obstruction, value, rfl, rfl, rfl, selected⟩)

def theoremEquiv (support : N.Support) (expression : old.ExpressionAt support) :
    old.TheoremAt expression ≃
      TheoremMember coordinates material support (expressionEquiv coordinates old encode hm support expression) :=
  MotherArenaNetworkOrigin.imageEquiv
    ((Function.Embedding.sigmaMk expression).trans ((Function.Embedding.sigmaMk support).trans encode.theoremMember))
    (fun code => r3 material 5 (coordinates.support support) (encode.expression ⟨support, expression⟩) code) (by
      intro code
      rw [r3, reader_bit coordinates old encode hm]
      simp only [graph, MotherArenaHigher.unpair_pair]
      constructor
      · rintro ⟨other, exp, value, same, expEq, selected⟩
        have same := coordinates.support.injective same
        cases same
        have same := ((Function.Embedding.sigmaMk (β := old.ExpressionAt) support).trans encode.expression).injective expEq
        cases same
        exact ⟨value, selected⟩
      · rintro ⟨value, selected⟩
        exact ⟨support, expression, value, rfl, rfl, selected⟩)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaTheory.Encoding
