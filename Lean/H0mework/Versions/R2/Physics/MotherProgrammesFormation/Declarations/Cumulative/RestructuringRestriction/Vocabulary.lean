import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Receipts.SectionsAcross
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.AdmissionAlignment.VocabularyRestriction

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringRestriction
open MotherRestructuringOrigin
open ResponsibilityLifecycle
noncomputable section

variable {original generated : Sorts} (sorts : ∀ index, original index ≃ generated index)
    {left : Families original} {right : Families generated} (families : FamilyMap sorts left right)
    (output : Operations generated right)

/-- All value operations are inverse readings of the actual generated
operations. The original twelve carriers and thirty-one families are the
explicit target schemas of the paid inverse correspondences. -/
def restrictOperations : Operations original left where
  null := (sorts 8).symm output.null
  complement := fun value => (sorts 8).symm (output.complement (sorts 8 value))
  involutive := by
    intro value
    simp only [Equiv.apply_symm_apply]
    exact (congrArg (sorts 8).symm (output.involutive (sorts 8 value))).trans
      ((sorts 8).symm_apply_apply value)
  nontrivial := by
    intro same
    apply output.nontrivial
    simpa only [Equiv.apply_symm_apply] using congrArg (sorts 8) same
  anchorIdentity := fun source => (sorts 8).symm (output.anchorIdentity (sorts 0 source))
  anchorScope := fun source => (sorts 5).symm (output.anchorScope (sorts 0 source))
  anchorLineage := fun source => (sorts 6).symm (output.anchorLineage (sorts 0 source))
  anchorRegistered := by
    intro source same
    apply output.anchorRegistered (sorts 0 source)
    simpa only [Equiv.apply_symm_apply] using congrArg (sorts 8) same
  incidence := fun source => (sorts 7).symm (output.incidence (sorts 0 source))
  demandContent := fun {source} obstruction =>
    (sorts 1).symm (output.demandContent (families 0 (source, PUnit.unit) obstruction))
  demandResidual := fun {source} obstruction =>
    (sorts 2).symm (output.demandResidual (families 0 (source, PUnit.unit) obstruction))

theorem restrictOperations_eq (old : Operations original left)
    (across : OperationsAcross sorts families old output) :
    restrictOperations sorts families output = old := by
  apply operations_ext
  · exact (congrArg (sorts 8).symm across.null_eq).trans ((sorts 8).symm_apply_apply _)
  · funext value
    exact (congrArg (sorts 8).symm (across.complement_eq value)).trans ((sorts 8).symm_apply_apply _)
  · funext source
    exact (congrArg (sorts 8).symm (across.identity_eq source)).trans ((sorts 8).symm_apply_apply _)
  · funext source
    exact (congrArg (sorts 5).symm (across.scope_eq source)).trans ((sorts 5).symm_apply_apply _)
  · funext source
    exact (congrArg (sorts 6).symm (across.lineage_eq source)).trans ((sorts 6).symm_apply_apply _)
  · funext source
    exact (congrArg (sorts 7).symm (across.incidence_eq source)).trans ((sorts 7).symm_apply_apply _)
  · funext source obstruction
    exact (congrArg (sorts 1).symm (across.content_eq source obstruction)).trans ((sorts 1).symm_apply_apply _)
  · funext source obstruction
    exact (congrArg (sorts 2).symm (across.residual_eq source obstruction)).trans ((sorts 2).symm_apply_apply _)

def restrictVocabulary (old : RestructuringVocabulary.{0})
    {sortsOut : Sorts} {familiesOut : Families sortsOut} (ops : Operations sortsOut familiesOut)
    (sorts : ∀ index, sortsOf old.base index ≃ sortsOut index)
    (families : FamilyMap sorts (familiesOf old) familiesOut) : RestructuringVocabulary :=
  restructuring (sortsOf old.base) (familiesOf old) (restrictOperations sorts families ops)

theorem restrictVocabulary_eq (old : RestructuringVocabulary.{0})
    {sortsOut : Sorts} {familiesOut : Families sortsOut} (ops : Operations sortsOut familiesOut)
    (sorts : ∀ index, sortsOf old.base index ≃ sortsOut index)
    (families : FamilyMap sorts (familiesOf old) familiesOut)
    (across : OperationsAcross sorts families (operationsOf old) ops) :
    restrictVocabulary old ops sorts families = old := by
  unfold restrictVocabulary
  rw [restrictOperations_eq sorts families ops (operationsOf old) across]
  exact restructuring_original old

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringRestriction
