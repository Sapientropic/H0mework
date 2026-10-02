import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Obligation.Origin

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherObligationOrigin
open ResponsibilityLifecycle MotherRestructuringOrigin
noncomputable section

variable {old generated : Sorts} {left : Families old} {right : Families generated}
    (sorts : ∀ i, old i ≃ generated i) (families : FamilyMap sorts left right)
    {original : Operations old left} {output : Operations generated right}
    (p : OperationsAcross sorts families original output)

def originEquiv (source : old 0) (content : old 1) :
    ObligationOrigin (vocabulary old left original) source content ≃
      ObligationOrigin (vocabulary generated right output) (sorts 0 source) (sorts 1 content) :=
  (originBodyEquiv (vocabulary old left original) source content).trans
    ((Equiv.sumCongr
      (resultFibreEquiv (families 0 (source, PUnit.unit)) (sorts 1)
        (fun obstruction => original.demandContent obstruction)
        (fun obstruction => output.demandContent obstruction)
        (p.content_eq source) content)
      (Equiv.sumCongr (families 1 (source, content, PUnit.unit))
        (Equiv.sumCongr (families 2 (source, content, PUnit.unit))
          (Equiv.sumCongr (families 3 (source, content, PUnit.unit))
            (Equiv.sumCongr (families 4 (source, content, PUnit.unit))
              (families 5 (source, content, PUnit.unit))))))).trans
      (originBodyEquiv (vocabulary generated right output) (sorts 0 source) (sorts 1 content)).symm)

def assumptionEquiv (source : old 0) (bearer : old 3) (scope : old 5) :
    BearerAssumption (vocabulary old left original) source bearer scope ≃
      BearerAssumption (vocabulary generated right output) (sorts 0 source) (sorts 3 bearer) (sorts 5 scope) :=
  (assumptionBodyEquiv (vocabulary old left original) source bearer scope).trans
    ((Equiv.sumCongr (families 7 (bearer, source, scope, PUnit.unit))
      (families 8 (bearer, source, scope, PUnit.unit))).trans
        (assumptionBodyEquiv (vocabulary generated right output) (sorts 0 source) (sorts 3 bearer) (sorts 5 scope)).symm)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherObligationOrigin
