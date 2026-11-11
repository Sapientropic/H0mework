import H0mework.Realization.Topology.EquivariantDual

/-!
# Naturality of test--Hilbert generalized-dual residuals

A commuting square of source and Hilbert features pulls continuous duals and
test duals contravariantly and induces the canonical map on extension
residuals. If the Hilbert actions commute, the same construction preserves
the equivariant bounded-extension subspaces.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedTestHilbertGeneralizedDual

noncomputable section

universe c c' h h'

variable {C : Type c} [AddCommGroup C] [Module ℂ C]
variable {C' : Type c'} [AddCommGroup C'] [Module ℂ C']
variable {H : Type h} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {H' : Type h'} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']

def testDualPullback (map : C →ₗ[ℂ] C') :
    TestDual C' →ₗ[ℂ] TestDual C where
  toFun functional := functional.comp map
  map_add' left right := by
    ext value
    rfl
  map_smul' scalar functional := by
    ext value
    rfl

def hilbertDualPullback (map : H →L[ℂ] H') :
    HilbertDual H' →ₗ[ℂ] HilbertDual H where
  toFun functional := functional.comp map
  map_add' left right := by
    ext value
    rfl
  map_smul' scalar functional := by
    ext value
    rfl

structure SourceMorphism
    (feature : C →ₗ[ℂ] H) (feature' : C' →ₗ[ℂ] H') where
  sourceMap : C →ₗ[ℂ] C'
  hilbertMap : H →L[ℂ] H'
  feature_commutes :
    hilbertMap.toLinearMap.comp feature = feature'.comp sourceMap

namespace SourceMorphism

theorem dualRestriction_naturality
    {feature : C →ₗ[ℂ] H} {feature' : C' →ₗ[ℂ] H'}
    (morphism : SourceMorphism feature feature') :
    (testDualPullback morphism.sourceMap).comp
        (hilbertDualRestriction feature') =
      (hilbertDualRestriction feature).comp
        (hilbertDualPullback morphism.hilbertMap) := by
  apply LinearMap.ext
  intro functional
  apply LinearMap.ext
  intro value
  have commute := LinearMap.congr_fun morphism.feature_commutes value
  exact congrArg functional commute.symm

theorem maps_extensionRange
    {feature : C →ₗ[ℂ] H} {feature' : C' →ₗ[ℂ] H'}
    (morphism : SourceMorphism feature feature') :
    LinearMap.range (hilbertDualRestriction feature') ≤
      (LinearMap.range (hilbertDualRestriction feature)).comap
        (testDualPullback morphism.sourceMap) := by
  rintro functional ⟨extension, rfl⟩
  refine ⟨hilbertDualPullback morphism.hilbertMap extension, ?_⟩
  exact (LinearMap.congr_fun
    (dualRestriction_naturality morphism) extension).symm

/-- Contravariant transport of the explicit extension residual. -/
def inducedResidualMap
    {feature : C →ₗ[ℂ] H} {feature' : C' →ₗ[ℂ] H'}
    (morphism : SourceMorphism feature feature') :
    ExtensionResidual feature' →ₗ[ℂ] ExtensionResidual feature :=
  (LinearMap.range (hilbertDualRestriction feature')).mapQ
    (LinearMap.range (hilbertDualRestriction feature))
    (testDualPullback morphism.sourceMap)
    morphism.maps_extensionRange

@[simp] theorem inducedResidualMap_canonical
    {feature : C →ₗ[ℂ] H} {feature' : C' →ₗ[ℂ] H'}
    (morphism : SourceMorphism feature feature')
    (functional : TestDual C') :
    inducedResidualMap morphism
        (canonicalExtensionResidual feature' functional) =
      canonicalExtensionResidual feature
        (testDualPullback morphism.sourceMap functional) :=
  rfl

def identity (feature : C →ₗ[ℂ] H) :
    SourceMorphism feature feature where
  sourceMap := LinearMap.id
  hilbertMap := ContinuousLinearMap.id ℂ H
  feature_commutes := by simp

@[simp] theorem inducedResidualMap_identity
    (feature : C →ₗ[ℂ] H) :
    inducedResidualMap (identity feature) = LinearMap.id := by
  apply LinearMap.ext
  intro residual
  obtain ⟨functional, rfl⟩ :=
    Submodule.mkQ_surjective
      (LinearMap.range (hilbertDualRestriction feature)) residual
  rfl

def comp
    {C'' H'' : Type*}
    [AddCommGroup C''] [Module ℂ C'']
    [NormedAddCommGroup H''] [InnerProductSpace ℂ H'']
    {feature : C →ₗ[ℂ] H} {feature' : C' →ₗ[ℂ] H'}
    {feature'' : C'' →ₗ[ℂ] H''}
    (first : SourceMorphism feature feature')
    (second : SourceMorphism feature' feature'') :
    SourceMorphism feature feature'' where
  sourceMap := second.sourceMap.comp first.sourceMap
  hilbertMap := second.hilbertMap.comp first.hilbertMap
  feature_commutes := by
    apply LinearMap.ext
    intro value
    change second.hilbertMap (first.hilbertMap (feature value)) =
      feature'' (second.sourceMap (first.sourceMap value))
    have firstCommute := congrArg
      (fun map : C →ₗ[ℂ] H' => map value) first.feature_commutes
    change first.hilbertMap (feature value) =
      feature' (first.sourceMap value) at firstCommute
    have secondCommute := congrArg
      (fun map : C' →ₗ[ℂ] H'' => map (first.sourceMap value))
      second.feature_commutes
    change second.hilbertMap (feature' (first.sourceMap value)) =
      feature'' (second.sourceMap (first.sourceMap value)) at secondCommute
    rw [firstCommute, secondCommute]

theorem inducedResidualMap_comp
    {C'' H'' : Type*}
    [AddCommGroup C''] [Module ℂ C'']
    [NormedAddCommGroup H''] [InnerProductSpace ℂ H'']
    {feature : C →ₗ[ℂ] H} {feature' : C' →ₗ[ℂ] H'}
    {feature'' : C'' →ₗ[ℂ] H''}
    (first : SourceMorphism feature feature')
    (second : SourceMorphism feature' feature'') :
    inducedResidualMap (comp first second) =
      (inducedResidualMap first).comp (inducedResidualMap second) := by
  apply LinearMap.ext
  intro residual
  obtain ⟨functional, rfl⟩ :=
    Submodule.mkQ_surjective
      (LinearMap.range (hilbertDualRestriction feature'')) residual
  rfl

/-! ## Equivariant naturality -/

structure EquivariantSourceMorphism
    (feature : C →ₗ[ℂ] H) (feature' : C' →ₗ[ℂ] H')
    (action : H →L[ℂ] H) (action' : H' →L[ℂ] H')
    extends SourceMorphism feature feature' where
  action_commutes : hilbertMap.comp action = action'.comp hilbertMap

namespace EquivariantSourceMorphism

def eigenDualPullback
    {feature : C →ₗ[ℂ] H} {feature' : C' →ₗ[ℂ] H'}
    {action : H →L[ℂ] H} {action' : H' →L[ℂ] H'}
    (character : ℂ)
    (morphism : EquivariantSourceMorphism
      feature feature' action action') :
    HilbertEigenDual action' character →ₗ[ℂ]
      HilbertEigenDual action character where
  toFun extension := ⟨hilbertDualPullback morphism.hilbertMap extension.1,
    (mem_hilbertEigenDual_iff action character _).mpr fun value => by
      have targetLaw :=
        (mem_hilbertEigenDual_iff action' character extension.1).mp
          extension.2 (morphism.hilbertMap value)
      have commute := congrArg
        (fun map : H →L[ℂ] H' => map value)
        morphism.action_commutes
      change morphism.hilbertMap (action value) =
        action' (morphism.hilbertMap value) at commute
      change extension.1 (morphism.hilbertMap (action value)) =
        character * extension.1 (morphism.hilbertMap value)
      rw [commute]
      exact targetLaw⟩
  map_add' left right := rfl
  map_smul' scalar functional := rfl

theorem eigenRestriction_naturality
    {feature : C →ₗ[ℂ] H} {feature' : C' →ₗ[ℂ] H'}
    {action : H →L[ℂ] H} {action' : H' →L[ℂ] H'}
    (character : ℂ)
    (morphism : EquivariantSourceMorphism
      feature feature' action action') :
    (testDualPullback morphism.sourceMap).comp
        (hilbertEigenDualRestriction feature' action' character) =
      (hilbertEigenDualRestriction feature action character).comp
        (eigenDualPullback character morphism) := by
  apply LinearMap.ext
  intro extension
  exact LinearMap.congr_fun
    (SourceMorphism.dualRestriction_naturality morphism.toSourceMorphism)
    extension.1

theorem maps_equivariantExtensionRange
    {feature : C →ₗ[ℂ] H} {feature' : C' →ₗ[ℂ] H'}
    {action : H →L[ℂ] H} {action' : H' →L[ℂ] H'}
    (character : ℂ)
    (morphism : EquivariantSourceMorphism
      feature feature' action action') :
    LinearMap.range
        (hilbertEigenDualRestriction feature' action' character) ≤
      (LinearMap.range
        (hilbertEigenDualRestriction feature action character)).comap
          (testDualPullback morphism.sourceMap) := by
  rintro functional ⟨extension, rfl⟩
  refine ⟨eigenDualPullback character morphism extension, ?_⟩
  exact (LinearMap.congr_fun
    (eigenRestriction_naturality character morphism) extension).symm

def inducedEquivariantResidualMap
    {feature : C →ₗ[ℂ] H} {feature' : C' →ₗ[ℂ] H'}
    {action : H →L[ℂ] H} {action' : H' →L[ℂ] H'}
    (character : ℂ)
    (morphism : EquivariantSourceMorphism
      feature feature' action action') :
    EquivariantExtensionResidual feature' action' character →ₗ[ℂ]
      EquivariantExtensionResidual feature action character :=
  (LinearMap.range
      (hilbertEigenDualRestriction feature' action' character)).mapQ
    (LinearMap.range
      (hilbertEigenDualRestriction feature action character))
    (testDualPullback morphism.sourceMap)
    (maps_equivariantExtensionRange character morphism)

@[simp] theorem inducedEquivariantResidualMap_canonical
    {feature : C →ₗ[ℂ] H} {feature' : C' →ₗ[ℂ] H'}
    {action : H →L[ℂ] H} {action' : H' →L[ℂ] H'}
    (character : ℂ)
    (morphism : EquivariantSourceMorphism
      feature feature' action action')
    (functional : TestDual C') :
    inducedEquivariantResidualMap character morphism
        (canonicalEquivariantExtensionResidual
          feature' action' character functional) =
      canonicalEquivariantExtensionResidual feature action character
        (testDualPullback morphism.sourceMap functional) :=
  rfl

end EquivariantSourceMorphism
end SourceMorphism

end

end SourceGeneratedTestHilbertGeneralizedDual
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
