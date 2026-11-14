import SaturationMonoid.GenericFoundation.Cofinal.Topology.Operations.Closure.Continuation.Retraction

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationCompletion

open CategoryTheory CategoryTheory.Limits CofinalHistorySettlement CofinalHistoryTransition CofinalRelationGeneratedComplex
open SourceOperationEffects SourceOperationExecution SourceOperationPaidRelations

section ComplexMap

variable {A B G : Type u} {first : RootedAccountedUnfolding A} {later : RootedAccountedUnfolding B}
variable {firstSeed laterSeed : RootedAccountedUnfolding (PresentedRelationEventAt G)}
variable {firstContinue laterContinue : RootedAccountedUnfolding
  (PresentedRelationEventAt G → RootedAccountedUnfolding (PresentedRelationEventAt G))}

private theorem later_differential_zero
    (face : RootGeneratedCofinalHistoryAt first firstSeed firstContinue) (degree : Nat) :
    (natComplex face).d (degree+1) (degree+1+1) = 0 :=
  CochainComplex.of_d _ _ (degree+1)

private def relationComplexMap (source : RootGeneratedCofinalHistoryAt first firstSeed firstContinue)
    (target : RootGeneratedCofinalHistoryAt later laterSeed laterContinue)
    (relation : source.relationClosure →ₗ[ℤ] target.relationClosure)
    (generator : source.generatorClosure →ₗ[ℤ] target.generatorClosure)
    (square : ∀ word, generator (relationInclusion source word) = relationInclusion target (relation word)) :
    natComplex source ⟶ natComplex target := by
  let component : ∀ degree, (natComplex source).X degree ⟶ (natComplex target).X degree
    | 0 => ModuleCat.ofHom relation
    | 1 => ModuleCat.ofHom generator
    | _+2 => 𝟙 _
  refine CochainComplex.ofHom component ?_
  rintro (_ | degree)
  · change ModuleCat.ofHom relation ≫ (natComplex target).d 0 1 =
      (natComplex source).d 0 1 ≫ ModuleCat.ofHom generator
    rw [natComplex_d_zero_one target, natComplex_d_zero_one source]
    exact ModuleCat.hom_ext (LinearMap.ext fun word => (square word).symm)
  · rw [later_differential_zero source degree, later_differential_zero target degree, comp_zero, zero_comp]

end ComplexMap

variable {S Root NextRoot : Type u} {V X : S → Type u} [∀ s, AddCommGroup (V s)]
variable {s : S} {old : Env V X} {before middle after : Expr V X s}
variable (root : RootedAccountedUnfolding Root) (prior : Trace old before middle)
variable (nextRoot : RootedAccountedUnfolding NextRoot) (next : Trace old before after)
variable (paid : words prior <+: words next)

local notation "sourceHistory" => prefixHistory root (exposure prior)
local notation "targetHistory" => prefixHistory nextRoot (exposure next)
local notation "relationForward" => continuationRelation root nextRoot paid
local notation "generatorForward" =>
  GeneratedTransition.generatorMap sourceHistory targetHistory (continuationTransition root nextRoot paid)
local notation "relationBack" => continuationRelationBack root prior nextRoot next
local notation "generatorBack" => continuationGeneratorBack root prior nextRoot next
local notation "contraction" => continuationHomotopyMap root prior nextRoot next

/-- The original inclusion on both terms gives the actual map of paid complexes. -/
def continuationCochainMap : natComplex sourceHistory ⟶ natComplex targetHistory :=
  relationComplexMap sourceHistory targetHistory relationForward generatorForward
    (continuation_forward_differential root prior nextRoot next paid)

private def retractCochainMap : natComplex targetHistory ⟶ natComplex sourceHistory :=
  relationComplexMap targetHistory sourceHistory relationBack generatorBack
    (continuation_backward_differential root prior nextRoot next)

private def homotopyComponent : ∀ i j, (natComplex targetHistory).X i ⟶ (natComplex targetHistory).X j
  | 1, 0 => ModuleCat.ofHom contraction
  | _, _ => 0

private def continuationContraction : Homotopy (𝟙 (natComplex targetHistory))
    (retractCochainMap root prior nextRoot next ≫ continuationCochainMap root prior nextRoot next paid) where
  hom := homotopyComponent root prior nextRoot next
  zero i j unrelated := by
    rcases i with (_ | _ | i) <;> cases j <;> first | rfl | exact False.elim (unrelated rfl)
  comm i := by
    rcases i with (_ | _ | degree)
    · rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_zero_cochainComplex, add_zero, natComplex_d_zero_one]
      exact ModuleCat.hom_ext (LinearMap.ext fun word =>
        ((congrArg (fun r : (targetHistory).relationClosure => r + relationForward (relationBack word))
          (continuation_homotopy_relation root prior nextRoot next paid word)).trans
          (sub_add_cancel word (relationForward (relationBack word)))).symm)
    · rw [Homotopy.dNext_cochainComplex, later_differential_zero targetHistory, zero_comp,
        Homotopy.prevD_succ_cochainComplex, zero_add, natComplex_d_zero_one]
      exact ModuleCat.hom_ext (LinearMap.ext fun word =>
        ((congrArg (fun g : (targetHistory).generatorClosure => g + generatorForward (generatorBack word))
          (continuation_homotopy_generator root prior nextRoot next paid word)).trans
          (sub_add_cancel word (generatorForward (generatorBack word)))).symm)
    · rw [Homotopy.dNext_cochainComplex, later_differential_zero targetHistory, zero_comp,
        Homotopy.prevD_succ_cochainComplex, later_differential_zero targetHistory, comp_zero, zero_add, zero_add]
      change 𝟙 _ = 𝟙 _ ≫ 𝟙 _
      rw [Category.id_comp]

/-- The actual paid continuation is a deformation retract of the original two-term complexes. -/
def continuationCochainHomotopyEquiv : HomotopyEquiv (natComplex sourceHistory) (natComplex targetHistory) where
  hom := continuationCochainMap root prior nextRoot next paid
  inv := retractCochainMap root prior nextRoot next
  homotopyHomInvId := Homotopy.ofEq (by
    apply HomologicalComplex.hom_ext
    rintro (_ | _ | degree)
    · exact ModuleCat.hom_ext (LinearMap.ext (continuation_relation_retract root prior nextRoot next paid))
    · exact ModuleCat.hom_ext (LinearMap.ext (continuation_generator_retract root prior nextRoot next paid))
    · exact Category.id_comp _)
  homotopyInvHomId := (continuationContraction root prior nextRoot next paid).symm

end SourceOperationCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
