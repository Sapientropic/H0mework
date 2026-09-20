import H0mework.Realization.ScalarCofinal.Naturality

/-! Tail observation of an existing scalar quotient tower preserves its complete source. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedScalarCofinalTail

open CategoryTheory CategoryTheory.Limits
open SourceGeneratedScalarCofinalKernelCompletion

noncomputable section

universe r u

variable {R : Type r} [CommRing R]
variable {Generator : Type u} [AddCommGroup Generator] [Module R Generator]
variable {Carrier : Nat → Type u}
variable [∀ stage, AddCommGroup (Carrier stage)] [∀ stage, Module R (Carrier stage)]

@[reducible] def tail (data : Data (R := R) (Generator := Generator) (Carrier := Carrier)) :
    Data (R := R) (Generator := Generator) (Carrier := fun stage => Carrier (stage + 1)) where
  evaluator stage := data.evaluator (stage + 1)
  transition stage := data.transition (stage + 1)

theorem compatible (data : Data (R := R) (Generator := Generator) (Carrier := Carrier))
    (laws : data.Compatible) : (tail data).Compatible :=
  fun stage => laws (stage + 1)

variable (data : Data (R := R) (Generator := Generator) (Carrier := Carrier))
variable (laws : data.Compatible)

private def projectionCone : Cone ((tail data).quotientTower (compatible data laws)) :=
  Cone.mk (data.Completion laws)
    (NatTrans.ofOpSequence (fun stage => data.restriction laws (stage + 1)) (fun stage => by
      simp only [Functor.const_obj_map,
        Data.quotientTower, Functor.ofOpSequence_map_homOfLE_succ]
      change data.restriction laws (stage + 1) =
        data.restriction laws (stage + 1 + 1) ≫
          ModuleCat.ofHom (data.quotientTransition laws (stage + 1))
      symm
      have square := limit.w (data.quotientTower laws)
        (homOfLE (Nat.le_succ (stage + 1))).op
      simp only [Data.quotientTower, Functor.ofOpSequence_map_homOfLE_succ] at square
      change data.restriction laws (stage + 1 + 1) ≫
          ModuleCat.ofHom (data.quotientTransition laws (stage + 1)) =
        data.restriction laws (stage + 1) at square
      exact square))

/-- The existing limit consumes its own later projections; no new stage values enter. -/
def completionMap : data.Completion laws ⟶ (tail data).Completion (compatible data laws) :=
  limit.lift ((tail data).quotientTower (compatible data laws)) (projectionCone data laws)

@[reassoc (attr := simp)] theorem completionMap_restriction (stage : Nat) :
    completionMap data laws ≫ (tail data).restriction (compatible data laws) stage =
      data.restriction laws (stage + 1) :=
  limit.lift_π (projectionCone data laws) (Opposite.op stage)

theorem completionMap_source :
    data.completionMap laws ≫ completionMap data laws =
      (tail data).completionMap (compatible data laws) := by
  apply (limit.isLimit ((tail data).quotientTower (compatible data laws))).hom_ext
  intro stage
  change (data.completionMap laws ≫ completionMap data laws) ≫
      (tail data).restriction (compatible data laws) stage.unop =
    (tail data).completionMap (compatible data laws) ≫
      (tail data).restriction (compatible data laws) stage.unop
  rw [Category.assoc, completionMap_restriction]
  exact (data.completionMap_restriction laws (stage.unop + 1)).trans
    ((tail data).completionMap_restriction (compatible data laws) stage.unop).symm

end
end SourceGeneratedScalarCofinalTail
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
