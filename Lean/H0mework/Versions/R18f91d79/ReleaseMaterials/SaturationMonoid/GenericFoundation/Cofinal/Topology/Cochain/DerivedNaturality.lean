import H0mework.Versions.R18f91d79.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.Cochain.DerivedLimit
import H0mework.Versions.R18f91d79.ReleaseMaterials.SaturationMonoid.LivingLawRootGeneratedSequentialHomotopyLimitNaturalityKernel

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u v
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedPrimePowerCompletion

open CategoryTheory CategoryTheory.Limits SequentialHomotopyLimit SequentialHomotopyLimitNaturality
open CochainMappingCoconeShortExact CochainMappingCoconeFunctoriality
open CochainComplex.HomComplex

private theorem cocone_projection_ext {K A B : IntegralCochainComplex} (g : A ⟶ B)
    {left right : K ⟶ CochainComplex.mappingCocone g}
    (first : left ≫ CochainComplex.mappingCocone.fst g = right ≫ CochainComplex.mappingCocone.fst g)
    (second : ∀ i, left.f i ≫ (CochainComplex.mappingCocone.snd g).v i (i + -1) rfl =
      right.f i ≫ (CochainComplex.mappingCocone.snd g).v i (i + -1) rfl) : left = right := by
  apply HomologicalComplex.hom_ext
  intro i
  have read := congrArg (fun (map : K ⟶ A) => map.f i) first
  change left.f i ≫ (CochainComplex.mappingCocone.fst g).f i =
    right.f i ≫ (CochainComplex.mappingCocone.fst g).f i at read
  calc
    _ = left.f i ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = right.f i ≫ 𝟙 _ := by
      rw [← CochainComplex.mappingCocone.id_X g i (i + -1) rfl]
      simp only [Preadditive.comp_add, ← Category.assoc, read, second i]
    _ = _ := Category.comp_id _

private theorem lift_short_complex_naturality (S T : ShortComplex IntegralCochainComplex)
    (completed : S.X₁ ⟶ T.X₁) (products : S.X₂ ⟶ T.X₂) (difference : S.X₃ ⟶ T.X₃)
    (kernelSquare : S.f ≫ products = completed ≫ T.f)
    (differenceSquare : products ≫ T.g = S.g ≫ difference) :
    liftShortComplex S ≫ mappingCoconeMap S.g T.g products difference differenceSquare =
      completed ≫ liftShortComplex T := by
  let map := mappingCoconeMap S.g T.g products difference differenceSquare
  apply cocone_projection_ext T.g
  · calc
      _ = liftShortComplex S ≫ (map ≫ CochainComplex.mappingCocone.fst T.g) := Category.assoc _ _ _
      _ = (liftShortComplex S ≫ CochainComplex.mappingCocone.fst S.g) ≫ products :=
        (congrArg (fun leg => liftShortComplex S ≫ leg)
          (mappingCoconeMap_fst S.g T.g products difference differenceSquare)).trans (Category.assoc _ _ _).symm
      _ = completed ≫ T.f := (congrArg (fun leg => leg ≫ products) (liftShortComplex_fst S)).trans kernelSquare
      _ = _ := (congrArg (fun leg => completed ≫ leg) (liftShortComplex_fst T)).symm.trans (Category.assoc _ _ _).symm
  · intro i
    have read := congrArg (fun (leg : Cochain (CochainComplex.mappingCocone S.g) T.X₃ (-1)) => leg.v i (i + -1) rfl)
      (mappingCoconeMap_snd S.g T.g products difference differenceSquare)
    rw [Cochain.comp_v _ _ _ i i (i + -1) (add_zero i) rfl,
      Cochain.comp_v _ _ _ i (i + -1) (i + -1) rfl (add_zero _)] at read
    simp only [Cochain.ofHom_v] at read
    simp only [HomologicalComplex.comp_f, Category.assoc, read]
    rw [← Category.assoc ((liftShortComplex S).f i)]
    simp only [liftShortComplex, CochainComplex.mappingCocone.lift_f_snd_v, Cochain.zero_v, zero_comp, comp_zero]

private theorem limit_product_naturality {Root : Type u} {NextRoot : Type v}
    {sourceOccurrence : RootedAccountedUnfolding (Root × (ℕᵒᵖ ⥤ IntegralCochainComplex))}
    {targetOccurrence : RootedAccountedUnfolding (NextRoot × (ℕᵒᵖ ⥤ IntegralCochainComplex))}
    (source : RootGeneratedSequentialHomotopyLimitAt sourceOccurrence)
    (target : RootGeneratedSequentialHomotopyLimitAt targetOccurrence)
    (prior : Cone source.actualTower) (later : Cone target.actualTower)
    (written : source.actualTower ⟶ target.actualTower) (completed : prior.pt ⟶ later.pt)
    (restrictions : ∀ stage : Nat, completed ≫ later.π.app (Opposite.op stage) =
      prior.π.app (Opposite.op stage) ≫ written.app (Opposite.op stage)) :
    limitProductMap source prior ≫ productMap source target written =
      completed ≫ limitProductMap target later := by
  apply Pi.hom_ext
  intro stage
  let first := limitProductMap source prior
  let next := limitProductMap target later
  let product := productMap source target written
  let left := source.productProjection stage
  let right := target.productProjection stage
  let read := written.app (Opposite.op stage)
  have sourceRead : (first ≫ product) ≫ right = prior.π.app (Opposite.op stage) ≫ read :=
    (Category.assoc first product right).trans
      ((congrArg (fun leg => first ≫ leg) (productMap_projection source target written stage)).trans
        ((Category.assoc first left read).symm.trans
          (congrArg (fun leg => leg ≫ read) (limit_product_projection source prior stage))))
  have targetRead : (completed ≫ next) ≫ right = completed ≫ later.π.app (Opposite.op stage) :=
    (Category.assoc completed next right).trans
      (congrArg (fun leg => completed ≫ leg) (limit_product_projection target later stage))
  exact sourceRead.trans ((restrictions stage).symm.trans targetRead.symm)

variable {Root : Type u} {NextRoot : Type v}
variable (root : RootedAccountedUnfolding Root) (next : RootedAccountedUnfolding NextRoot)
variable (p : Nat.Primes) {source target : CochainComplex AddCommGrpCat ℤ}

local notation "shape" => ComplexShape.up ℤ
local notation "before" => cochainDerivedLimitFace root p source
local notation "after" => cochainDerivedLimitFace next p target

/-- The actual cochain map acts on the generated homotopy limit through its whole stage transformation. -/
def cochainDerivedAction (action : source ⟶ target) : (before).homotopyLimit ⟶ (after).homotopyLimit :=
  homotopyLimitMap before after (cochainStageTowerMap shape p action)

/-- The canonical comparison commutes with the actual stage action, including the cocone residual coordinate. -/
theorem cochain_derived_limit_naturality (action : source ⟶ target) :
    cochainDerivedLimitMap root p source ≫ cochainDerivedAction root next p action =
      ((completionFunctor p).mapHomologicalComplex shape).map action ≫ cochainDerivedLimitMap next p target := by
  let sourceCone := cochainCompletionCone shape p source
  let targetCone := cochainCompletionCone shape p target
  let written := cochainStageTowerMap shape p action
  let products := productMap before after written
  let completed := ((completionFunctor p).mapHomologicalComplex shape).map action
  have kernelSquare := limit_product_naturality before after sourceCone targetCone written completed
    (cochain_completion_map_restriction shape p action)
  exact lift_short_complex_naturality (limitDifferenceSequence before sourceCone)
    (limitDifferenceSequence after targetCone) completed products products kernelSquare
    (SequentialHomotopyLimitNaturality.differenceSquare before after written)

/-- A paid cochain homotopy equivalence acts invertibly in the derived limit. -/
theorem cochain_derived_action_quasiIso (action : HomotopyEquiv source target) :
    QuasiIso (cochainDerivedAction root next p action.hom) := by
  let first := cochainDerivedLimitMap root p source
  let last := cochainDerivedLimitMap next p target
  let moved := cochainDerivedAction root next p action.hom
  let completed := (completionFunctor p).mapHomotopyEquiv action
  have compared : first ≫ moved = completed.hom ≫ last :=
    cochain_derived_limit_naturality root next p action.hom
  have firstIso := cochain_derived_limit_quasiIso root p source
  have lastIso := cochain_derived_limit_quasiIso next p target
  have crossed := quasiIso_comp completed.hom last (hφ := completed.quasiIso_hom) (hφ' := lastIso)
  exact quasiIso_of_comp_left first moved (hφ := firstIso)
    (hφφ' := (congrArg (fun map => QuasiIso map) compared).mpr crossed)

end SourceGeneratedPrimePowerCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
