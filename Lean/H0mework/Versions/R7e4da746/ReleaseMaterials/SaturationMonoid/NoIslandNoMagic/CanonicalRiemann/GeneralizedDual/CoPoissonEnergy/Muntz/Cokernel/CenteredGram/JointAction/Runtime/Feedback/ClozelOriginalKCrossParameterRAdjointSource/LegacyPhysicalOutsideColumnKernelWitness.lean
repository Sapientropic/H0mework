import Lean
import Mathlib.Analysis.CStarAlgebra.Classes

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000

elab "cp399OriginalOutsideSmulType" : term =>
  return (Lean.Expr.app
  (Lean.Expr.app
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.const `IsBoundedSMul [Lean.Level.zero, Lean.Level.zero])
              (Lean.Expr.const `Complex []))
            (Lean.Expr.const `Complex []))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.const `SeminormedRing.toPseudoMetricSpace [Lean.Level.zero])
              (Lean.Expr.const `Complex []))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `SeminormedCommRing.toSeminormedRing [Lean.Level.zero])
                (Lean.Expr.const `Complex []))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `NormedCommRing.toSeminormedCommRing [Lean.Level.zero])
                  (Lean.Expr.const `Complex []))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `NormedField.toNormedCommRing [Lean.Level.zero])
                    (Lean.Expr.const `Complex []))
                  (Lean.Expr.const `Complex.instNormedField []))))))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.const `SeminormedAddCommGroup.toPseudoMetricSpace [Lean.Level.zero])
            (Lean.Expr.const `Complex []))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.const `NonUnitalSeminormedRing.toSeminormedAddCommGroup [Lean.Level.zero])
              (Lean.Expr.const `Complex []))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing [Lean.Level.zero])
                (Lean.Expr.const `Complex []))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `SeminormedCommRing.toNonUnitalSeminormedCommRing [Lean.Level.zero])
                  (Lean.Expr.const `Complex []))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `NormedCommRing.toSeminormedCommRing [Lean.Level.zero])
                    (Lean.Expr.const `Complex []))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommCStarAlgebra.toNormedCommRing [Lean.Level.zero])
                      (Lean.Expr.const `Complex []))
                    (Lean.Expr.const `instCommCStarAlgebraComplex []))))))))
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `MulZeroClass.toZero [Lean.Level.zero]) (Lean.Expr.const `Complex []))
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `instMulZeroClassOfSemiring [Lean.Level.zero]) (Lean.Expr.const `Complex []))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.const `DivisionSemiring.toSemiring [Lean.Level.zero])
              (Lean.Expr.const `Complex []))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `Semifield.toDivisionSemiring [Lean.Level.zero])
                (Lean.Expr.const `Complex []))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Field.toSemifield [Lean.Level.zero]) (Lean.Expr.const `Complex []))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `NormedField.toField [Lean.Level.zero]) (Lean.Expr.const `Complex []))
                  (Lean.Expr.const `Complex.instNormedField []))))))))
    (Lean.Expr.app
      (Lean.Expr.app (Lean.Expr.const `NegZeroClass.toZero [Lean.Level.zero]) (Lean.Expr.const `Complex []))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.const `SubNegZeroMonoid.toNegZeroClass [Lean.Level.zero])
          (Lean.Expr.const `Complex []))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.const `SubtractionMonoid.toSubNegZeroMonoid [Lean.Level.zero])
            (Lean.Expr.const `Complex []))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.const `SubtractionCommMonoid.toSubtractionMonoid [Lean.Level.zero])
              (Lean.Expr.const `Complex []))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `AddCommGroup.toDivisionAddCommMonoid [Lean.Level.zero])
                (Lean.Expr.const `Complex []))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `SeminormedAddCommGroup.toAddCommGroup [Lean.Level.zero])
                  (Lean.Expr.const `Complex []))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `NonUnitalSeminormedRing.toSeminormedAddCommGroup [Lean.Level.zero])
                    (Lean.Expr.const `Complex []))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing [Lean.Level.zero])
                      (Lean.Expr.const `Complex []))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `SeminormedCommRing.toNonUnitalSeminormedCommRing [Lean.Level.zero])
                        (Lean.Expr.const `Complex []))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `NormedCommRing.toSeminormedCommRing [Lean.Level.zero])
                          (Lean.Expr.const `Complex []))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `CommCStarAlgebra.toNormedCommRing [Lean.Level.zero])
                            (Lean.Expr.const `Complex []))
                          (Lean.Expr.const `instCommCStarAlgebraComplex [])))))))))))))
  (Lean.Expr.app
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.const `SMulZeroClass.toSMul [Lean.Level.zero, Lean.Level.zero])
          (Lean.Expr.const `Complex []))
        (Lean.Expr.const `Complex []))
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `AddZero.toZero [Lean.Level.zero]) (Lean.Expr.const `Complex []))
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `AddZeroClass.toAddZero [Lean.Level.zero]) (Lean.Expr.const `Complex []))
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `AddMonoid.toAddZeroClass [Lean.Level.zero]) (Lean.Expr.const `Complex []))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `SubNegMonoid.toAddMonoid [Lean.Level.zero])
                (Lean.Expr.const `Complex []))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `AddGroup.toSubNegMonoid [Lean.Level.zero])
                  (Lean.Expr.const `Complex []))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `AddCommGroup.toAddGroup [Lean.Level.zero])
                    (Lean.Expr.const `Complex []))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `SeminormedAddCommGroup.toAddCommGroup [Lean.Level.zero])
                      (Lean.Expr.const `Complex []))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `NonUnitalSeminormedRing.toSeminormedAddCommGroup [Lean.Level.zero])
                        (Lean.Expr.const `Complex []))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing [Lean.Level.zero])
                          (Lean.Expr.const `Complex []))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `SeminormedCommRing.toNonUnitalSeminormedCommRing [Lean.Level.zero])
                            (Lean.Expr.const `Complex []))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `NormedCommRing.toSeminormedCommRing [Lean.Level.zero])
                              (Lean.Expr.const `Complex []))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CommCStarAlgebra.toNormedCommRing [Lean.Level.zero])
                                (Lean.Expr.const `Complex []))
                              (Lean.Expr.const `instCommCStarAlgebraComplex []))))))))))))))
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.const `DistribSMul.toSMulZeroClass [Lean.Level.zero, Lean.Level.zero])
            (Lean.Expr.const `Complex []))
          (Lean.Expr.const `Complex []))
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `AddMonoid.toAddZeroClass [Lean.Level.zero]) (Lean.Expr.const `Complex []))
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `SubNegMonoid.toAddMonoid [Lean.Level.zero]) (Lean.Expr.const `Complex []))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `AddGroup.toSubNegMonoid [Lean.Level.zero]) (Lean.Expr.const `Complex []))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `AddCommGroup.toAddGroup [Lean.Level.zero])
                  (Lean.Expr.const `Complex []))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `SeminormedAddCommGroup.toAddCommGroup [Lean.Level.zero])
                    (Lean.Expr.const `Complex []))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `NonUnitalSeminormedRing.toSeminormedAddCommGroup [Lean.Level.zero])
                      (Lean.Expr.const `Complex []))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing [Lean.Level.zero])
                        (Lean.Expr.const `Complex []))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `SeminormedCommRing.toNonUnitalSeminormedCommRing [Lean.Level.zero])
                          (Lean.Expr.const `Complex []))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `NormedCommRing.toSeminormedCommRing [Lean.Level.zero])
                            (Lean.Expr.const `Complex []))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `CommCStarAlgebra.toNormedCommRing [Lean.Level.zero])
                              (Lean.Expr.const `Complex []))
                            (Lean.Expr.const `instCommCStarAlgebraComplex []))))))))))))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `DistribMulAction.toDistribSMul [Lean.Level.zero, Lean.Level.zero])
                (Lean.Expr.const `Complex []))
              (Lean.Expr.const `Complex []))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Semiring.toMonoid [Lean.Level.zero]) (Lean.Expr.const `Complex []))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `DivisionSemiring.toSemiring [Lean.Level.zero])
                  (Lean.Expr.const `Complex []))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `Semifield.toDivisionSemiring [Lean.Level.zero])
                    (Lean.Expr.const `Complex []))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Field.toSemifield [Lean.Level.zero]) (Lean.Expr.const `Complex []))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `NormedField.toField [Lean.Level.zero])
                        (Lean.Expr.const `Complex []))
                      (Lean.Expr.const `Complex.instNormedField [])))))))
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `SubNegMonoid.toAddMonoid [Lean.Level.zero]) (Lean.Expr.const `Complex []))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `AddGroup.toSubNegMonoid [Lean.Level.zero]) (Lean.Expr.const `Complex []))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `AddCommGroup.toAddGroup [Lean.Level.zero])
                  (Lean.Expr.const `Complex []))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `SeminormedAddCommGroup.toAddCommGroup [Lean.Level.zero])
                    (Lean.Expr.const `Complex []))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `NonUnitalSeminormedRing.toSeminormedAddCommGroup [Lean.Level.zero])
                      (Lean.Expr.const `Complex []))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing [Lean.Level.zero])
                        (Lean.Expr.const `Complex []))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `SeminormedCommRing.toNonUnitalSeminormedCommRing [Lean.Level.zero])
                          (Lean.Expr.const `Complex []))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `NormedCommRing.toSeminormedCommRing [Lean.Level.zero])
                            (Lean.Expr.const `Complex []))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `CommCStarAlgebra.toNormedCommRing [Lean.Level.zero])
                              (Lean.Expr.const `Complex []))
                            (Lean.Expr.const `instCommCStarAlgebraComplex [])))))))))))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Module.toDistribMulAction [Lean.Level.zero, Lean.Level.zero])
                  (Lean.Expr.const `Complex []))
                (Lean.Expr.const `Complex []))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `DivisionSemiring.toSemiring [Lean.Level.zero])
                  (Lean.Expr.const `Complex []))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `Semifield.toDivisionSemiring [Lean.Level.zero])
                    (Lean.Expr.const `Complex []))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Field.toSemifield [Lean.Level.zero]) (Lean.Expr.const `Complex []))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `NormedField.toField [Lean.Level.zero])
                        (Lean.Expr.const `Complex []))
                      (Lean.Expr.const `Complex.instNormedField []))))))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `AddCommGroup.toAddCommMonoid [Lean.Level.zero])
                (Lean.Expr.const `Complex []))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `SeminormedAddCommGroup.toAddCommGroup [Lean.Level.zero])
                  (Lean.Expr.const `Complex []))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `NonUnitalSeminormedRing.toSeminormedAddCommGroup [Lean.Level.zero])
                    (Lean.Expr.const `Complex []))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing [Lean.Level.zero])
                      (Lean.Expr.const `Complex []))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `SeminormedCommRing.toNonUnitalSeminormedCommRing [Lean.Level.zero])
                        (Lean.Expr.const `Complex []))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `NormedCommRing.toSeminormedCommRing [Lean.Level.zero])
                          (Lean.Expr.const `Complex []))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `CommCStarAlgebra.toNormedCommRing [Lean.Level.zero])
                            (Lean.Expr.const `Complex []))
                          (Lean.Expr.const `instCommCStarAlgebraComplex [])))))))))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `NormedSpace.toModule [Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.const `Complex []))
                  (Lean.Expr.const `Complex []))
                (Lean.Expr.const `Complex.instNormedField []))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `NonUnitalSeminormedRing.toSeminormedAddCommGroup [Lean.Level.zero])
                  (Lean.Expr.const `Complex []))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing [Lean.Level.zero])
                    (Lean.Expr.const `Complex []))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `SeminormedCommRing.toNonUnitalSeminormedCommRing [Lean.Level.zero])
                      (Lean.Expr.const `Complex []))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `NormedCommRing.toSeminormedCommRing [Lean.Level.zero])
                        (Lean.Expr.const `Complex []))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommCStarAlgebra.toNormedCommRing [Lean.Level.zero])
                          (Lean.Expr.const `Complex []))
                        (Lean.Expr.const `instCommCStarAlgebraComplex [])))))))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `NonUnitalCStarAlgebra.toNormedSpace [Lean.Level.zero])
                (Lean.Expr.const `Complex []))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra [Lean.Level.zero])
                  (Lean.Expr.const `Complex []))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `CommCStarAlgebra.toNonUnitalCommCStarAlgebra [Lean.Level.zero])
                    (Lean.Expr.const `Complex []))
                  (Lean.Expr.const `instCommCStarAlgebraComplex []))))))))))

elab "cp399OriginalOutsideSmulProof" : term =>
  return (Lean.Expr.app
  (Lean.Expr.app
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.const `NormedSpace.toIsBoundedSMul [Lean.Level.zero, Lean.Level.zero])
          (Lean.Expr.const `Complex []))
        (Lean.Expr.const `Complex []))
      (Lean.Expr.const `Complex.instNormedField []))
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.const `NonUnitalSeminormedRing.toSeminormedAddCommGroup [Lean.Level.zero])
        (Lean.Expr.const `Complex []))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.const `NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing [Lean.Level.zero])
          (Lean.Expr.const `Complex []))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.const `SeminormedCommRing.toNonUnitalSeminormedCommRing [Lean.Level.zero])
            (Lean.Expr.const `Complex []))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.const `NormedCommRing.toSeminormedCommRing [Lean.Level.zero])
              (Lean.Expr.const `Complex []))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `CommCStarAlgebra.toNormedCommRing [Lean.Level.zero])
                (Lean.Expr.const `Complex []))
              (Lean.Expr.const `instCommCStarAlgebraComplex [])))))))
  (Lean.Expr.app
    (Lean.Expr.app
      (Lean.Expr.const `NonUnitalCStarAlgebra.toNormedSpace [Lean.Level.zero])
      (Lean.Expr.const `Complex []))
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.const `NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra [Lean.Level.zero])
        (Lean.Expr.const `Complex []))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.const `CommCStarAlgebra.toNonUnitalCommCStarAlgebra [Lean.Level.zero])
          (Lean.Expr.const `Complex []))
        (Lean.Expr.const `instCommCStarAlgebraComplex [])))))

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource

-- This is the exact existing kernel name required by the paid source proof.
set_option linter.auxLemma false in
theorem physicalOutsideColumn._proof_1 : cp399OriginalOutsideSmulType :=
  cp399OriginalOutsideSmulProof

end OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
