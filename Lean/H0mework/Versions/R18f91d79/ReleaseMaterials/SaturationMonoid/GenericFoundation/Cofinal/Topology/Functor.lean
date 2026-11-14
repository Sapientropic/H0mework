import H0mework.Realization.Perfectification.Integral.Completion.LivingLawRootGeneratedPrimePowerCompletionNaturalityKernel

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedPrimePowerCompletion

open CategoryTheory CategoryTheory.Limits

variable {A B : Type u} [AddCommGroup A] [AddCommGroup B]

private theorem stage_map_add (p : Nat.Primes) (j : Nat) (f g : A →ₗ[ℤ] B) :
    stageMap p j (f + g) = stageMap p j f + stageMap p j g := by
  apply LinearMap.ext
  intro value
  obtain ⟨word, rfl⟩ := (powerRange (L := A) p j).mkQ_surjective value
  exact map_add (stageProjection (L := B) p j) (f word) (g word)

private theorem coimage_map_add (p : Nat.Primes) (f g : A →ₗ[ℤ] B) :
    coimageMap p (f + g) = coimageMap p f + coimageMap p g := by
  apply LinearMap.ext
  intro value
  obtain ⟨word, rfl⟩ := (SeparationKernel (L := A) p).mkQ_surjective value
  exact map_add (coimageProjection (L := B) p) (f word) (g word)

private theorem completion_map_add (p : Nat.Primes) (f g : A →ₗ[ℤ] B) :
    inducedCompletionMap p (f + g) = inducedCompletionMap p f + inducedCompletionMap p g := by
  apply (limit.isLimit (tower (L := B) p)).hom_ext
  rintro ⟨j⟩
  change inducedCompletionMap p (f + g) ≫ restriction (L := B) p j =
    (inducedCompletionMap p f + inducedCompletionMap p g) ≫ restriction (L := B) p j
  rw [Preadditive.add_comp, inducedCompletionMap_restriction p (f + g),
    inducedCompletionMap_restriction p f, inducedCompletionMap_restriction p g, stage_map_add,
    ModuleCat.ofHom_add, Preadditive.comp_add]

/-- The original prime-power quotient and its induced action. -/
def stageFunctor (p : Nat.Primes) (j : Nat) : AddCommGrpCat.{u} ⥤ ModuleCat.{u} ℤ where
  obj M := ModuleCat.of ℤ (StageResidual (L := M) p j)
  map f := ModuleCat.ofHom (stageMap p j f.hom.toIntLinearMap)
  map_id M := ModuleCat.hom_ext (stageMap_id (L := M) p j)
  map_comp f g := ModuleCat.hom_ext (stageMap_comp p j g.hom.toIntLinearMap f.hom.toIntLinearMap)

instance (p : Nat.Primes) (j : Nat) : (stageFunctor.{u} p j).Additive where
  map_add := by
    intro M N f g
    exact ModuleCat.hom_ext (stage_map_add p j f.hom.toIntLinearMap g.hom.toIntLinearMap)

/-- The original coherent limit and its actual induced map. -/
def completionFunctor (p : Nat.Primes) : AddCommGrpCat.{u} ⥤ ModuleCat.{u} ℤ where
  obj M := Completion (L := M) p
  map f := inducedCompletionMap p f.hom.toIntLinearMap
  map_id M := inducedCompletionMap_id (L := M) p
  map_comp f g := inducedCompletionMap_comp p g.hom.toIntLinearMap f.hom.toIntLinearMap

instance (p : Nat.Primes) : (completionFunctor.{u} p).Additive where
  map_add := by
    intro M N f g
    exact completion_map_add p f.hom.toIntLinearMap g.hom.toIntLinearMap

/-- The original separation quotient and its induced action. -/
def coimageFunctor (p : Nat.Primes) : AddCommGrpCat.{u} ⥤ ModuleCat.{u} ℤ where
  obj M := ModuleCat.of ℤ (FaithfulCoimage (L := M) p)
  map f := ModuleCat.ofHom (coimageMap p f.hom.toIntLinearMap)
  map_id M := ModuleCat.hom_ext (coimageMap_id (L := M) p)
  map_comp f g := ModuleCat.hom_ext (coimageMap_comp p g.hom.toIntLinearMap f.hom.toIntLinearMap)

instance (p : Nat.Primes) : (coimageFunctor.{u} p).Additive where
  map_add := by
    intro M N f g
    exact ModuleCat.hom_ext (coimage_map_add p f.hom.toIntLinearMap g.hom.toIntLinearMap)

def stageFunctorTransition (p : Nat.Primes) (j : Nat) : stageFunctor.{u} p (j+1) ⟶ stageFunctor p j where
  app M := ModuleCat.ofHom (transition (L := M) p j)
  naturality _ _ f := ModuleCat.hom_ext (stageMap_transition p j f.hom.toIntLinearMap).symm

def completionFunctorRestriction (p : Nat.Primes) (j : Nat) : completionFunctor.{u} p ⟶ stageFunctor p j where
  app M := restriction (L := M) p j
  naturality _ _ f := inducedCompletionMap_restriction p f.hom.toIntLinearMap j

def coimageFunctorRealization (p : Nat.Primes) : coimageFunctor.{u} p ⟶ completionFunctor p where
  app M := ModuleCat.ofHom (coimageRealization (L := M) p)
  naturality _ _ f := ModuleCat.hom_ext (coimageRealization_naturality p f.hom.toIntLinearMap)

theorem completion_functor_restriction_step (p : Nat.Primes) (j : Nat) :
    completionFunctorRestriction.{u} p (j+1) ≫ stageFunctorTransition p j = completionFunctorRestriction p j := by
  apply NatTrans.ext
  funext M
  change restriction (L := M) p (j+1) ≫ ModuleCat.ofHom (transition (L := M) p j) = restriction (L := M) p j
  have compatible := limit.w (tower (L := M) p) (homOfLE (Nat.le_add_right j 1)).op
  rw [Functor.ofOpSequence_map_homOfLE_succ] at compatible
  exact compatible

end SourceGeneratedPrimePowerCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
