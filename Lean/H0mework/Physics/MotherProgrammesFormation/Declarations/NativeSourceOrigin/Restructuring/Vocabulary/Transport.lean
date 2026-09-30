import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Vocabulary.OperationRecovery

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringOrigin
noncomputable section

abbrev FamilyMap {old generated : Sorts} (sorts : ∀ i, old i ≃ generated i)
    (left : Families old) (right : Families generated) :=
  (index : Fin 31) → (args : Args old (signature index)) → left index args ≃ right index (argsEquiv sorts (signature index) args)

def obstructionEquiv {old generated : Sorts} (sorts : ∀ i, old i ≃ generated i)
    {left : Families old} {right : Families generated} (families : FamilyMap sorts left right) :
    (Σ source : old 0, left 0 (source, PUnit.unit)) ≃ (Σ source : generated 0, right 0 (source, PUnit.unit)) :=
  Equiv.sigmaCongr (sorts 0) (fun source => families 0 (source, PUnit.unit))

structure OperationsAcross {old generated : Sorts} (sorts : ∀ i, old i ≃ generated i)
    {left : Families old} {right : Families generated} (families : FamilyMap sorts left right)
    (original : Operations old left) (output : Operations generated right) : Prop where
  null_eq : output.null = sorts 8 original.null
  complement_eq : ∀ x, output.complement (sorts 8 x) = sorts 8 (original.complement x)
  identity_eq : ∀ source, output.anchorIdentity (sorts 0 source) = sorts 8 (original.anchorIdentity source)
  scope_eq : ∀ source, output.anchorScope (sorts 0 source) = sorts 5 (original.anchorScope source)
  lineage_eq : ∀ source, output.anchorLineage (sorts 0 source) = sorts 6 (original.anchorLineage source)
  incidence_eq : ∀ source, output.incidence (sorts 0 source) = sorts 7 (original.incidence source)
  content_eq : ∀ source (obstruction : left 0 (source, PUnit.unit)),
    output.demandContent (families 0 (source, PUnit.unit) obstruction) = sorts 1 (original.demandContent obstruction)
  residual_eq : ∀ source (obstruction : left 0 (source, PUnit.unit)),
    output.demandResidual (families 0 (source, PUnit.unit) obstruction) = sorts 2 (original.demandResidual obstruction)

variable {old generated : Sorts} (sorts : ∀ i, old i ≃ generated i)
    {left : Families old} {right : Families generated} (families : FamilyMap sorts left right)
    (original : Operations old left)

def transportOperations : Operations generated right where
  null := sorts 8 original.null
  complement := fun x => sorts 8 (original.complement ((sorts 8).symm x))
  involutive := by
    intro x
    simp only [Equiv.symm_apply_apply]
    exact (congrArg (sorts 8) (original.involutive ((sorts 8).symm x))).trans ((sorts 8).apply_symm_apply x)
  nontrivial := by
    intro same
    have originalEq := (sorts 8).injective same
    exact original.nontrivial (originalEq.trans (congrArg original.complement ((sorts 8).symm_apply_apply original.null)))
  anchorIdentity := fun source => sorts 8 (original.anchorIdentity ((sorts 0).symm source))
  anchorScope := fun source => sorts 5 (original.anchorScope ((sorts 0).symm source))
  anchorLineage := fun source => sorts 6 (original.anchorLineage ((sorts 0).symm source))
  anchorRegistered := by
    intro source same
    have originalEq := (sorts 8).injective same
    exact original.anchorRegistered ((sorts 0).symm source)
      (originalEq.trans (congrArg original.complement ((sorts 8).symm_apply_apply _)))
  incidence := fun source => sorts 7 (original.incidence ((sorts 0).symm source))
  demandContent := fun {source} obstruction =>
    sorts 1 (original.demandContent ((obstructionEquiv sorts families).symm ⟨source, obstruction⟩).2)
  demandResidual := fun {source} obstruction =>
    sorts 2 (original.demandResidual ((obstructionEquiv sorts families).symm ⟨source, obstruction⟩).2)

theorem transported_operations : OperationsAcross sorts families original (transportOperations sorts families original) where
  null_eq := rfl
  complement_eq := fun x => congrArg (fun value => sorts 8 (original.complement value)) ((sorts 8).symm_apply_apply x)
  identity_eq := fun source => congrArg (fun value => sorts 8 (original.anchorIdentity value)) ((sorts 0).symm_apply_apply source)
  scope_eq := fun source => congrArg (fun value => sorts 5 (original.anchorScope value)) ((sorts 0).symm_apply_apply source)
  lineage_eq := fun source => congrArg (fun value => sorts 6 (original.anchorLineage value)) ((sorts 0).symm_apply_apply source)
  incidence_eq := fun source => congrArg (fun value => sorts 7 (original.incidence value)) ((sorts 0).symm_apply_apply source)
  content_eq := fun source obstruction => congrArg
    (fun value : Σ source : old 0, left 0 (source, PUnit.unit) => sorts 1 (original.demandContent value.2))
    ((obstructionEquiv sorts families).symm_apply_apply ⟨source, obstruction⟩)
  residual_eq := fun source obstruction => congrArg
    (fun value : Σ source : old 0, left 0 (source, PUnit.unit) => sorts 2 (original.demandResidual value.2))
    ((obstructionEquiv sorts families).symm_apply_apply ⟨source, obstruction⟩)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringOrigin
