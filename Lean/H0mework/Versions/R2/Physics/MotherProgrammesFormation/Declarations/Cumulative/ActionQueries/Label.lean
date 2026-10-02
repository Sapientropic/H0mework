import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.Query

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActionQueries
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
noncomputable section
universe u v
private theorem cast_family {A : Type u} {F : A → Type v} (f : (a : A) → F a)
    {first last : A} (same : first = last) : Equiv.cast (congrArg F same) (f first) = f last := by
  cases same
  rfl

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    {U7 : U7ProducerCalculus N} (calculus : U7ObstructionEvolutionCalculus N U7)
    {Query Index FormedIndex : Type} (label : Index → Query) (indices : Index ≃ FormedIndex)

def indexClauseEquiv :
    ((index : Index) → MotherNativeClause.Clause root visit U7 calculus (label index)) ≃
      ((index : FormedIndex) → MotherNativeClause.Clause root visit U7 calculus (label (indices.symm index))) :=
  Equiv.piCongr indices (fun index =>
    Equiv.cast (congrArg (fun value : Index => MotherNativeClause.Clause root visit U7 calculus (label value))
      (indices.symm_apply_apply index).symm))

theorem indexClause_at
    (original : (index : Index) → MotherNativeClause.Clause root visit U7 calculus (label index))
    (index : FormedIndex) : indexClauseEquiv calculus label indices original index = original (indices.symm index) := by
  obtain ⟨originalIndex, rfl⟩ := indices.surjective index
  rw [indexClauseEquiv, Equiv.piCongr_apply_apply]
  exact cast_family original (indices.symm_apply_apply originalIndex).symm

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActionQueries
