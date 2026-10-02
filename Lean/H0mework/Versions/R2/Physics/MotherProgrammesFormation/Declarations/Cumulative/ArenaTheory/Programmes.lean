import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaTheory.Presentation

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaTheory.Encoding
open MotherInventoryAdmission
open ResponsibilityLifecycle LivingLawEvolution
noncomputable section
variable {rank : Ordinal.{0}} {N : WorldRelationNetwork.{0}}
    (coordinates : Coordinates (rank := rank) N) (old : TheoryState N) (encode : Encoding (rank := rank) old)
    {material : MotherArenaHigher.Material rank}
    (hm : MotherArenaHigher.read rank material = reader coordinates old encode)

def expressionPointEquiv : ExpressionTotal old ≃ ExpressionPoint coordinates material :=
  Equiv.sigmaCongrRight (expressionEquiv coordinates old encode hm)

def pointPresentation (support : N.Support) (expression : old.ExpressionAt support) :
    ConstructivePresentation
      (TheoremMember coordinates material support (expressionEquiv coordinates old encode hm support expression))
      (N.HoldsAt support (denotes coordinates material (checked coordinates old encode hm)
        (expressionEquiv coordinates old encode hm support expression))) :=
  presentationFromEquiv ((theoremEquiv coordinates old encode hm support expression).symm.trans
    ((presentationEquiv (old.theoremPresentation expression)).trans
      (Equiv.cast (congrArg (N.HoldsAt support) (denotes_value coordinates old encode hm support expression).symm))))

def programmes : TheoremPresentations coordinates material (checked coordinates old encode hm) :=
  Equiv.piCongrLeft _ (expressionPointEquiv coordinates old encode hm)
    (fun point => pointPresentation coordinates old encode hm point.1 point.2)

theorem programmes_at (support : N.Support) (expression : old.ExpressionAt support) :
    programmes coordinates old encode hm ⟨support, expressionEquiv coordinates old encode hm support expression⟩ =
      pointPresentation coordinates old encode hm support expression :=
  Equiv.piCongrLeft_apply_apply
    (fun point : ExpressionPoint coordinates material =>
      ConstructivePresentation (TheoremMember coordinates material point.1 point.2)
        (N.HoldsAt point.1 (denotes coordinates material (checked coordinates old encode hm) point.2)))
    (expressionPointEquiv coordinates old encode hm)
    (fun point => pointPresentation coordinates old encode hm point.1 point.2)
    (⟨support, expression⟩ : ExpressionTotal old)

def presentation : Presentation old
    (theory coordinates material (checked coordinates old encode hm) (programmes coordinates old encode hm)) where
  version := versionEquiv coordinates old encode hm
  version_eq := version_value coordinates old encode hm
  law := lawEquiv coordinates old encode hm
  realization := realizationEquiv coordinates old encode hm
  without := withoutEquiv coordinates old encode hm
  expression := expressionEquiv coordinates old encode hm
  denotes := denotes_value coordinates old encode hm
  theoremMember := theoremEquiv coordinates old encode hm
  presentation := by
    intro support expression
    change presentationFromEquiv ((theoremEquiv coordinates old encode hm support expression).trans
      ((presentationEquiv (programmes coordinates old encode hm
        ⟨support, expressionEquiv coordinates old encode hm support expression⟩)).trans
          (Equiv.cast (congrArg (N.HoldsAt support) (denotes_value coordinates old encode hm support expression))))) = _
    rw [programmes_at]
    exact presentation_conjugate_recovers
      (theoremEquiv coordinates old encode hm support expression)
      (Equiv.cast (congrArg (N.HoldsAt support) (denotes_value coordinates old encode hm support expression).symm))
      (old.theoremPresentation expression)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaTheory.Encoding
