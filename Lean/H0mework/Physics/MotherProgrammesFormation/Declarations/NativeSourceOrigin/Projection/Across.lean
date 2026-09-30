import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Projection.Formation

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherProjectionOrigin
open MotherFullCompiler MotherSourcePrograms
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

variable {N G : WorldRelationNetwork.{0}} {V W : Vocabulary.{0}}
    {left : SourceNativeLedgerSource N V} {right : SourceNativeLedgerSource G W}
    {n : MotherNetworkOrigin.Presentation N G} {v : MotherVocabularyOrigin.Presentation V W}
    (sourceMap : MotherNativeSourceOrigin.Presentation n v left.source right.source)

structure Across (old : SourceNativeProjectionLaw left) (generated : SourceNativeProjectionLaw right) where
  projection : old.Projection ≃ generated.Projection
  active : ∀ p (point : Point left.source), old.ActiveAt p point.2 ≃ generated.ActiveAt (projection p) (pointEquiv sourceMap point).2
  inactive : ∀ p (point : Point left.source), old.InactiveAt p point.2 ≃ generated.InactiveAt (projection p) (pointEquiv sourceMap point).2
  payload : ∀ p (point : Point left.source) (value : old.ActiveAt p point.2),
    old.PayloadAt p point.2 value ≃ generated.PayloadAt (projection p) (pointEquiv sourceMap point).2 (active p point value)
  classify : ∀ p (point : Point left.source), generated.classify (projection p) (pointEquiv sourceMap point).2 =
    (Equiv.sumCongr (active p point) (inactive p point)) (old.classify p point.2)
  project : ∀ p (point : Point left.source) (value : old.ActiveAt p point.2),
    generated.project (projection p) (pointEquiv sourceMap point).2 (active p point value) =
      payload p point value (old.project p point.2 value)

namespace Across
variable {sourceMap} {old : SourceNativeProjectionLaw left} {middle generated : SourceNativeProjectionLaw right}
    (a : Across sourceMap old middle) (b : Presentation middle generated)

def comp : Across sourceMap old generated where
  projection := a.projection.trans b.projection
  active := fun p point => (a.active p point).trans (b.active (a.projection p) (pointEquiv sourceMap point))
  inactive := fun p point => (a.inactive p point).trans (b.inactive (a.projection p) (pointEquiv sourceMap point))
  payload := fun p point value => (a.payload p point value).trans
    (b.payload (a.projection p) (pointEquiv sourceMap point) (a.active p point value))
  classify := by
    intro p point
    refine (b.classify (a.projection p) (pointEquiv sourceMap point)).trans ?_
    refine (congrArg (Equiv.sumCongr (b.active (a.projection p) (pointEquiv sourceMap point))
      (b.inactive (a.projection p) (pointEquiv sourceMap point))) (a.classify p point)).trans ?_
    cases old.classify p point.2 <;> rfl
  project := fun p point value => (b.project (a.projection p) (pointEquiv sourceMap point) (a.active p point value)).trans
    (congrArg (b.payload (a.projection p) (pointEquiv sourceMap point) (a.active p point value)) (a.project p point value))

def totalEquiv : Total old ≃ Total middle :=
  Equiv.sumCongr a.projection
    (Equiv.sumCongr (Equiv.sigmaCongr a.projection (fun p => Equiv.sigmaCongr (pointEquiv sourceMap) (a.active p)))
      (Equiv.sumCongr (Equiv.sigmaCongr a.projection (fun p => Equiv.sigmaCongr (pointEquiv sourceMap) (a.inactive p)))
        (Equiv.sigmaCongr a.projection (fun p => Equiv.sigmaCongr (pointEquiv sourceMap)
          (fun point => Equiv.sigmaCongr (a.active p point) (a.payload p point))))))

def outcomeEquiv (projection : old.Projection) (point : Point left.source) :
    SourceNativeProjectionFiberAt old projection point.2 ≃
      SourceNativeProjectionFiberAt middle (a.projection projection) (pointEquiv sourceMap point).2 :=
  Equiv.sumCongr (Equiv.sigmaCongr (a.active projection point) (a.payload projection point)) (a.inactive projection point)

theorem outcome_eq (projection : old.Projection) (point : Point left.source) :
    middle.outcomeAt (a.projection projection) (pointEquiv sourceMap point).2 =
      outcomeEquiv a projection point (old.outcomeAt projection point.2) := by
  unfold SourceNativeProjectionLaw.outcomeAt
  rw [a.classify]
  cases selected : old.classify projection point.2 with
  | inl active =>
      exact congrArg Sum.inl (congrArg
        (fun value => (⟨a.active projection point active, value⟩ :
          Sigma (middle.PayloadAt (a.projection projection) (pointEquiv sourceMap point).2)))
        (a.project projection point active))
  | inr inactive => rfl
end Across

private def payloadCast {I : Type} (A : I → Type) (C : (i : I) → A i → Type)
    {i j : I} (same : i = j) (value : A i) : C i value ≃ C j ((Equiv.cast (congrArg A same)) value) := by
  cases same
  exact Equiv.refl _

private theorem classifier_cast {I : Type} (A B : I → Type) (classify : (i : I) → A i ⊕ B i)
    {i j : I} (same : i = j) : classify j =
    (Equiv.sumCongr (Equiv.cast (congrArg A same)) (Equiv.cast (congrArg B same))) (classify i) := by
  cases same
  cases classify i <;> rfl

private theorem projector_cast {I : Type} (A : I → Type) (C : (i : I) → A i → Type)
    (project : (i : I) → (value : A i) → C i value) {i j : I} (same : i = j) (value : A i) :
    project j ((Equiv.cast (congrArg A same)) value) = payloadCast A C same value (project i value) := by
  cases same
  rfl

def pullbackLaw (old : SourceNativeProjectionLaw left) : SourceNativeProjectionLaw right where
  Projection := old.Projection
  ActiveAt := fun p {current} event => old.ActiveAt p ((pointEquiv sourceMap).symm ⟨current, event⟩).2
  InactiveAt := fun p {current} event => old.InactiveAt p ((pointEquiv sourceMap).symm ⟨current, event⟩).2
  PayloadAt := fun p {current} event value => old.PayloadAt p ((pointEquiv sourceMap).symm ⟨current, event⟩).2 value
  classify := fun p {current} event => old.classify p ((pointEquiv sourceMap).symm ⟨current, event⟩).2
  project := fun p {current} event value => old.project p ((pointEquiv sourceMap).symm ⟨current, event⟩).2 value

def pullbackAcross (old : SourceNativeProjectionLaw left) : Across sourceMap old (pullbackLaw sourceMap old) where
  projection := Equiv.refl _
  active := fun p point => Equiv.cast (congrArg (fun point : Point left.source => old.ActiveAt p point.2)
    ((pointEquiv sourceMap).symm_apply_apply point).symm)
  inactive := fun p point => Equiv.cast (congrArg (fun point : Point left.source => old.InactiveAt p point.2)
    ((pointEquiv sourceMap).symm_apply_apply point).symm)
  payload := fun p point value => payloadCast (fun point : Point left.source => old.ActiveAt p point.2)
    (fun point value => old.PayloadAt p point.2 value) ((pointEquiv sourceMap).symm_apply_apply point).symm value
  classify := fun p point => classifier_cast (fun point : Point left.source => old.ActiveAt p point.2)
    (fun point => old.InactiveAt p point.2) (fun point => old.classify p point.2)
      ((pointEquiv sourceMap).symm_apply_apply point).symm
  project := fun p point value => projector_cast (fun point : Point left.source => old.ActiveAt p point.2)
    (fun point value => old.PayloadAt p point.2 value) (fun point value => old.project p point.2 value)
      ((pointEquiv sourceMap).symm_apply_apply point).symm value

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherProjectionOrigin
