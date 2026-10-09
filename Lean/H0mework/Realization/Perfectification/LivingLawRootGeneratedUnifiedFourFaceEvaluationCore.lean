import Mathlib.LinearAlgebra.Dual.Defs
import H0mework.Foundation.Source.AccountedUnfolding

/-! Evaluator-polymorphic sibling projections of one exact source occurrence. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace UnifiedFourFace.Evaluation

universe s a c t l r h v e

structure Input
    (Source : Type s) (Algebra : Type a) (Combinatorial : Type c)
    (Topological : Type t) (Logical : Type l) (Relation : Type r)
    (Cochain : Type h) (Carrier : Type v) (Target : Type e)
    [AddCommGroup Carrier] [Module ℤ Carrier]
    [AddCommGroup Target] [Module ℤ Target] where
  occurrence : RootedAccountedUnfolding Source
  algebraAt : Source → Algebra
  combinatorialAt : Source → Combinatorial
  topologicalAt : Source → Topological
  logicalAt : Source → Logical
  relationAt : Source → Relation
  cochainAt : Source → Cochain
  evaluationAt : Source → Carrier →ₗ[ℤ] Target
  faithfulAt : Source → Carrier →ₗ[ℤ] Carrier

end UnifiedFourFace.Evaluation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
