import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Projection.Across

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherProjectionRestriction
open MotherFullCompiler MotherSourcePrograms MotherProjectionOrigin
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

variable {N G : WorldRelationNetwork.{0}} {V W : ConstructiveRoot.Vocabulary.{0}}
    {left : SourceNativeLedgerSource N V} {right : SourceNativeLedgerSource G W}
    {n : MotherNetworkOrigin.Presentation N G} {v : MotherVocabularyOrigin.Presentation V W}
    {sourceMap : MotherNativeSourceOrigin.Presentation n v left.source right.source}
    {old : SourceNativeProjectionLaw left} {generated : SourceNativeProjectionLaw right}
    (across : Across sourceMap old generated)

def restrictClassify (projection : old.Projection) (point : Point left.source) :
    old.ActiveAt projection point.2 ⊕ old.InactiveAt projection point.2 :=
  (Equiv.sumCongr (across.active projection point) (across.inactive projection point)).symm
    (generated.classify (across.projection projection) (pointEquiv sourceMap point).2)

theorem restrictClassify_eq (projection : old.Projection) (point : Point left.source) :
    restrictClassify across projection point = old.classify projection point.2 := by
  unfold restrictClassify
  rw [across.classify, Equiv.symm_apply_apply]

def restrictProject (projection : old.Projection) (point : Point left.source) (active : old.ActiveAt projection point.2) :
    old.PayloadAt projection point.2 active :=
  (across.payload projection point active).symm
    (generated.project (across.projection projection) (pointEquiv sourceMap point).2 (across.active projection point active))

theorem restrictProject_eq (projection : old.Projection) (point : Point left.source) (active : old.ActiveAt projection point.2) :
    restrictProject across projection point active = old.project projection point.2 active := by
  unfold restrictProject
  rw [across.project, Equiv.symm_apply_apply]

/-- Original types are the paid inverse indices. Both actual operations
read the generated projection law, including every unselected active member. -/
def restrictProjection : SourceNativeProjectionLaw left where
  Projection := old.Projection
  ActiveAt := old.ActiveAt
  InactiveAt := old.InactiveAt
  PayloadAt := old.PayloadAt
  classify := fun projection {current} event => restrictClassify across projection ⟨current, event⟩
  project := fun projection {current} event active => restrictProject across projection ⟨current, event⟩ active

theorem restrictProjection_eq : restrictProjection across = old := by
  have classifyEq : (fun projection {current} event => restrictClassify across projection ⟨current, event⟩) = old.classify := by
    funext projection current event
    exact restrictClassify_eq across projection ⟨current, event⟩
  have projectEq : (fun projection {current} event active => restrictProject across projection ⟨current, event⟩ active) = old.project := by
    funext projection current event active
    exact restrictProject_eq across projection ⟨current, event⟩ active
  exact congrArg₂ (fun classify project =>
    ({ Projection := old.Projection, ActiveAt := old.ActiveAt, InactiveAt := old.InactiveAt,
       PayloadAt := old.PayloadAt, classify, project } : SourceNativeProjectionLaw left)) classifyEq projectEq

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherProjectionRestriction
