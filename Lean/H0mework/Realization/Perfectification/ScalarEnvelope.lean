import H0mework.Realization.Perfectification.ScalarCoimage

/-!
# Scalar-polymorphic exact perfect envelope

For every commutative coefficient ring `R`, the coimage of an actual
`R`-linear dual evaluation is canonically equivalent to its generated dual
image.  The inverse supplies coevaluation and both zig-zag identities.  The
result is initial among source-compatible exact targets whose dual object
embeds faithfully into the same ambient dual.

This is the coefficient-neutral form of the exact `P∞` mechanism.  It does
not identify the generated image with the whole algebraic dual and does not
add topology, boundedness, finite generation, or a determinant premise.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedScalarExactEnvelope

open SourceGeneratedScalarPerfectification

noncomputable section

universe r c d a b

variable {R : Type r} [CommRing R]
variable {C : Type c} {D : Type d}
variable [AddCommGroup C] [Module R C]
variable [AddCommGroup D] [Module R D]
variable (evaluation : C →ₗ[R] Module.Dual R D)

abbrev Carrier := PerfectificationCarrier evaluation

abbrev GeneratedDual := LinearMap.range (dualEmbedding evaluation)

def dualInclusion : GeneratedDual evaluation →ₗ[R] Module.Dual R D :=
  (GeneratedDual evaluation).subtype

def generatedDualMap : Carrier evaluation →ₗ[R] GeneratedDual evaluation :=
  (dualEmbedding evaluation).codRestrict (GeneratedDual evaluation) (by
    intro value
    exact ⟨value, rfl⟩)

theorem generatedDualMap_injective :
    Function.Injective (generatedDualMap evaluation) := by
  intro left right equality
  apply dualEmbedding_injective evaluation
  exact congrArg Subtype.val equality

theorem generatedDualMap_surjective :
    Function.Surjective (generatedDualMap evaluation) := by
  intro target
  rcases target.property with ⟨value, equality⟩
  refine ⟨value, ?_⟩
  apply Subtype.ext
  exact equality

theorem generatedDualMap_bijective :
    Function.Bijective (generatedDualMap evaluation) :=
  ⟨generatedDualMap_injective evaluation, generatedDualMap_surjective evaluation⟩

noncomputable def perfectEquiv :
    Carrier evaluation ≃ₗ[R] GeneratedDual evaluation :=
  LinearEquiv.ofBijective (generatedDualMap evaluation)
    (generatedDualMap_bijective evaluation)

def coevaluation : GeneratedDual evaluation →ₗ[R] Carrier evaluation :=
  (perfectEquiv evaluation).symm.toLinearMap

theorem dualInclusion_comp_generatedDualMap :
    (dualInclusion evaluation).comp (generatedDualMap evaluation) =
      dualEmbedding evaluation := by
  rfl

@[simp] theorem coevaluation_comp_generatedDualMap :
    (coevaluation evaluation).comp (generatedDualMap evaluation) =
      LinearMap.id := by
  apply LinearMap.ext
  intro value
  exact (perfectEquiv evaluation).symm_apply_apply value

@[simp] theorem generatedDualMap_comp_coevaluation :
    (generatedDualMap evaluation).comp (coevaluation evaluation) =
      LinearMap.id := by
  apply LinearMap.ext
  intro value
  exact (perfectEquiv evaluation).apply_symm_apply value

theorem source_evaluation_readback :
    ((dualInclusion evaluation).comp (generatedDualMap evaluation)).comp
        (canonicalMap evaluation) = evaluation := by
  apply LinearMap.ext
  intro value
  rfl

structure UniversalPerfectEnvelope : Type (max r c d + 2) where
  private mk ::
  map : Carrier evaluation →ₗ[R] GeneratedDual evaluation
  inclusion : GeneratedDual evaluation →ₗ[R] Module.Dual R D
  equivalence : Carrier evaluation ≃ₗ[R] GeneratedDual evaluation
  coevaluation : GeneratedDual evaluation →ₗ[R] Carrier evaluation
  map_bijective : Function.Bijective map
  inclusion_map : inclusion.comp map = dualEmbedding evaluation
  left_zigzag : coevaluation.comp map = LinearMap.id
  right_zigzag : map.comp coevaluation = LinearMap.id

def sourceGeneratedPerfectification : UniversalPerfectEnvelope evaluation where
  map := generatedDualMap evaluation
  inclusion := dualInclusion evaluation
  equivalence := perfectEquiv evaluation
  coevaluation := coevaluation evaluation
  map_bijective := generatedDualMap_bijective evaluation
  inclusion_map := dualInclusion_comp_generatedDualMap evaluation
  left_zigzag := coevaluation_comp_generatedDualMap evaluation
  right_zigzag := generatedDualMap_comp_coevaluation evaluation

theorem universalPerfectEnvelope_total :
    Nonempty (UniversalPerfectEnvelope evaluation) :=
  ⟨sourceGeneratedPerfectification evaluation⟩

/-! ## Universal exact target -/

structure CompatiblePerfectTarget
    (TargetCarrier : Type a) (TargetDual : Type b)
    [AddCommGroup TargetCarrier] [Module R TargetCarrier]
    [AddCommGroup TargetDual] [Module R TargetDual] :
    Type (max r c d a b + 1) where
  sourceMap : C →ₗ[R] TargetCarrier
  duality : TargetCarrier ≃ₗ[R] TargetDual
  dualInclusion : TargetDual →ₗ[R] Module.Dual R D
  dualInclusion_injective : Function.Injective dualInclusion
  readback : (dualInclusion.comp duality.toLinearMap).comp sourceMap = evaluation

namespace CompatiblePerfectTarget

variable {TargetCarrier : Type a} {TargetDual : Type b}
variable [AddCommGroup TargetCarrier] [Module R TargetCarrier]
variable [AddCommGroup TargetDual] [Module R TargetDual]

theorem kernel_compatibility
    (target : CompatiblePerfectTarget evaluation TargetCarrier TargetDual) :
    LinearMap.ker evaluation ≤ LinearMap.ker target.sourceMap := by
  intro value value_mem
  rw [LinearMap.mem_ker] at value_mem ⊢
  have readbackAt := LinearMap.congr_fun target.readback value
  have inclusionZero :
      target.dualInclusion (target.duality (target.sourceMap value)) = 0 := by
    simpa [LinearMap.comp_apply, value_mem] using readbackAt
  have dualZero : target.duality (target.sourceMap value) = 0 :=
    target.dualInclusion_injective (by simpa using inclusionZero)
  exact target.duality.injective (by simpa using dualZero)

def carrierFactor
    (target : CompatiblePerfectTarget evaluation TargetCarrier TargetDual) :
    Carrier evaluation →ₗ[R] TargetCarrier :=
  canonicalFactor evaluation target.sourceMap
    (target.kernel_compatibility evaluation)

@[simp] theorem carrierFactor_comp_canonicalMap
    (target : CompatiblePerfectTarget evaluation TargetCarrier TargetDual) :
    (target.carrierFactor evaluation).comp (canonicalMap evaluation) =
      target.sourceMap :=
  canonicalFactor_comp evaluation target.sourceMap
    (target.kernel_compatibility evaluation)

def dualFactor
    (target : CompatiblePerfectTarget evaluation TargetCarrier TargetDual) :
    GeneratedDual evaluation →ₗ[R] TargetDual :=
  (target.duality.toLinearMap.comp (target.carrierFactor evaluation)).comp
    (coevaluation evaluation)

@[simp] theorem dualFactor_comp_generatedDualMap
    (target : CompatiblePerfectTarget evaluation TargetCarrier TargetDual) :
    (target.dualFactor evaluation).comp (generatedDualMap evaluation) =
      target.duality.toLinearMap.comp (target.carrierFactor evaluation) := by
  apply LinearMap.ext
  intro value
  exact congrArg (fun carrierValue =>
      target.duality (target.carrierFactor evaluation carrierValue))
    ((perfectEquiv evaluation).symm_apply_apply value)

theorem dualInclusion_comp_dualFactor
    (target : CompatiblePerfectTarget evaluation TargetCarrier TargetDual) :
    target.dualInclusion.comp (target.dualFactor evaluation) =
      SourceGeneratedScalarExactEnvelope.dualInclusion evaluation := by
  apply LinearMap.ext
  intro dualValue
  obtain ⟨carrierValue, rfl⟩ :=
    (generatedDualMap_surjective evaluation) dualValue
  obtain ⟨sourceValue, rfl⟩ :=
    Submodule.mkQ_surjective (LinearMap.ker evaluation) carrierValue
  have targetAt := LinearMap.congr_fun target.readback sourceValue
  have sourceAt := LinearMap.congr_fun
    (dualEmbedding_comp_canonicalMap evaluation) sourceValue
  have zigAt := LinearMap.congr_fun
    (coevaluation_comp_generatedDualMap evaluation)
    (canonicalMap evaluation sourceValue)
  have factorAt := LinearMap.congr_fun
    (target.carrierFactor_comp_canonicalMap evaluation) sourceValue
  rw [LinearMap.comp_apply] at zigAt factorAt
  have zigAt' :
      coevaluation evaluation
          (generatedDualMap evaluation (canonicalMap evaluation sourceValue)) =
        canonicalMap evaluation sourceValue := by
    simpa using zigAt
  change target.dualInclusion
      (target.duality
        (target.carrierFactor evaluation
          (coevaluation evaluation
            (generatedDualMap evaluation (canonicalMap evaluation sourceValue))))) =
    dualEmbedding evaluation (canonicalMap evaluation sourceValue)
  rw [zigAt', factorAt]
  exact targetAt.trans sourceAt.symm

end CompatiblePerfectTarget

structure EnvelopeMorphism
    {TargetCarrier : Type a} {TargetDual : Type b}
    [AddCommGroup TargetCarrier] [Module R TargetCarrier]
    [AddCommGroup TargetDual] [Module R TargetDual]
    (target : CompatiblePerfectTarget evaluation TargetCarrier TargetDual) :
    Type (max r c d a b + 1) where
  carrierMap : Carrier evaluation →ₗ[R] TargetCarrier
  dualMap : GeneratedDual evaluation →ₗ[R] TargetDual
  source_commutes : carrierMap.comp (canonicalMap evaluation) = target.sourceMap
  duality_commutes : dualMap.comp (generatedDualMap evaluation) =
    target.duality.toLinearMap.comp carrierMap
  inclusion_commutes : target.dualInclusion.comp dualMap = dualInclusion evaluation

def universalMorphism
    {TargetCarrier : Type a} {TargetDual : Type b}
    [AddCommGroup TargetCarrier] [Module R TargetCarrier]
    [AddCommGroup TargetDual] [Module R TargetDual]
    (target : CompatiblePerfectTarget evaluation TargetCarrier TargetDual) :
    EnvelopeMorphism evaluation target where
  carrierMap := target.carrierFactor evaluation
  dualMap := target.dualFactor evaluation
  source_commutes := target.carrierFactor_comp_canonicalMap evaluation
  duality_commutes := target.dualFactor_comp_generatedDualMap evaluation
  inclusion_commutes := target.dualInclusion_comp_dualFactor evaluation

theorem universalMorphism_unique
    {TargetCarrier : Type a} {TargetDual : Type b}
    [AddCommGroup TargetCarrier] [Module R TargetCarrier]
    [AddCommGroup TargetDual] [Module R TargetDual]
    (target : CompatiblePerfectTarget evaluation TargetCarrier TargetDual)
    (other : EnvelopeMorphism evaluation target) :
    other = universalMorphism evaluation target := by
  have carrierEquality : other.carrierMap = target.carrierFactor evaluation :=
    canonicalFactor_unique evaluation target.sourceMap
      (target.kernel_compatibility evaluation) other.carrierMap
      other.source_commutes
  cases other with
  | mk otherCarrier otherDual sourceCommutes dualityCommutes inclusionCommutes =>
      simp only at carrierEquality
      subst otherCarrier
      have dualEquality : otherDual = target.dualFactor evaluation := by
        apply LinearMap.ext
        intro dualValue
        obtain ⟨carrierValue, rfl⟩ :=
          (generatedDualMap_surjective evaluation) dualValue
        have otherAt := LinearMap.congr_fun dualityCommutes carrierValue
        have canonicalAt := LinearMap.congr_fun
          (CompatiblePerfectTarget.dualFactor_comp_generatedDualMap
            evaluation target) carrierValue
        exact otherAt.trans canonicalAt.symm
      subst otherDual
      rfl

theorem universal_property
    {TargetCarrier : Type a} {TargetDual : Type b}
    [AddCommGroup TargetCarrier] [Module R TargetCarrier]
    [AddCommGroup TargetDual] [Module R TargetDual]
    (target : CompatiblePerfectTarget evaluation TargetCarrier TargetDual) :
    ∃! morphism : EnvelopeMorphism evaluation target,
      morphism.carrierMap.comp (canonicalMap evaluation) = target.sourceMap := by
  refine ⟨universalMorphism evaluation target,
    (universalMorphism evaluation target).source_commutes, ?_⟩
  intro other _
  exact universalMorphism_unique evaluation target other

/-! ## Source-morphism naturality -/

variable {C' : Type c} {D' : Type d}
variable [AddCommGroup C'] [Module R C']
variable [AddCommGroup D'] [Module R D']
variable (evaluation' : C' →ₗ[R] Module.Dual R D')

def inducedCarrierMap
    (carrierMap : C →ₗ[R] C')
    (dualMap : D' →ₗ[R] D)
    (naturality : (inducedDualTarget dualMap).comp evaluation =
      evaluation'.comp carrierMap) :
    Carrier evaluation →ₗ[R] Carrier evaluation' :=
  inducedPerfectificationMap evaluation evaluation' carrierMap dualMap naturality

def inducedDualImageMap
    (carrierMap : C →ₗ[R] C')
    (dualMap : D' →ₗ[R] D)
    (naturality : (inducedDualTarget dualMap).comp evaluation =
      evaluation'.comp carrierMap) :
    GeneratedDual evaluation →ₗ[R] GeneratedDual evaluation' :=
  ((inducedDualTarget dualMap).comp (dualInclusion evaluation)).codRestrict
    (GeneratedDual evaluation') (by
      intro value
      rcases value.property with ⟨sourceValue, sourceEquality⟩
      refine ⟨inducedCarrierMap evaluation evaluation' carrierMap dualMap naturality
        sourceValue, ?_⟩
      have commute := congrArg (fun f => f sourceValue)
        (dualEmbedding_naturality evaluation evaluation' carrierMap dualMap naturality)
      calc
        dualEmbedding evaluation'
            (inducedCarrierMap evaluation evaluation' carrierMap dualMap naturality
              sourceValue) =
            inducedDualTarget dualMap (dualEmbedding evaluation sourceValue) := commute
        _ = inducedDualTarget dualMap value.1 := by rw [sourceEquality])

theorem generatedDualMap_naturality
    (carrierMap : C →ₗ[R] C')
    (dualMap : D' →ₗ[R] D)
    (naturality : (inducedDualTarget dualMap).comp evaluation =
      evaluation'.comp carrierMap) :
    (inducedDualImageMap evaluation evaluation' carrierMap dualMap naturality).comp
        (generatedDualMap evaluation) =
      (generatedDualMap evaluation').comp
        (inducedCarrierMap evaluation evaluation' carrierMap dualMap naturality) := by
  apply LinearMap.ext
  intro value
  apply Subtype.ext
  have commute := congrArg (fun f => f value)
    (dualEmbedding_naturality evaluation evaluation' carrierMap dualMap naturality)
  exact commute.symm

theorem dualInclusion_naturality
    (carrierMap : C →ₗ[R] C')
    (dualMap : D' →ₗ[R] D)
    (naturality : (inducedDualTarget dualMap).comp evaluation =
      evaluation'.comp carrierMap) :
    (dualInclusion evaluation').comp
        (inducedDualImageMap evaluation evaluation' carrierMap dualMap naturality) =
      (inducedDualTarget dualMap).comp (dualInclusion evaluation) := by
  apply LinearMap.ext
  intro value
  rfl

theorem coevaluation_naturality
    (carrierMap : C →ₗ[R] C')
    (dualMap : D' →ₗ[R] D)
    (naturality : (inducedDualTarget dualMap).comp evaluation =
      evaluation'.comp carrierMap) :
    (inducedCarrierMap evaluation evaluation' carrierMap dualMap naturality).comp
        (coevaluation evaluation) =
      (coevaluation evaluation').comp
        (inducedDualImageMap evaluation evaluation' carrierMap dualMap naturality) := by
  apply LinearMap.ext
  intro dualValue
  obtain ⟨carrierValue, rfl⟩ :=
    (generatedDualMap_surjective evaluation) dualValue
  have sourceZigzag := LinearMap.congr_fun
    (coevaluation_comp_generatedDualMap evaluation) carrierValue
  have targetZigzag := LinearMap.congr_fun
    (coevaluation_comp_generatedDualMap evaluation')
    (inducedCarrierMap evaluation evaluation' carrierMap dualMap naturality carrierValue)
  have forwardNaturality := LinearMap.congr_fun
    (generatedDualMap_naturality evaluation evaluation' carrierMap dualMap naturality)
    carrierValue
  rw [LinearMap.comp_apply] at sourceZigzag targetZigzag forwardNaturality
  simpa [sourceZigzag, forwardNaturality] using targetZigzag.symm

theorem inducedDualImageMap_id
    (identityNaturality :
      (inducedDualTarget (LinearMap.id : D →ₗ[R] D)).comp evaluation =
        evaluation.comp (LinearMap.id : C →ₗ[R] C)) :
    inducedDualImageMap evaluation evaluation LinearMap.id LinearMap.id
      identityNaturality = LinearMap.id := by
  apply LinearMap.ext
  intro value
  apply Subtype.ext
  rfl

variable {C'' : Type c} {D'' : Type d}
variable [AddCommGroup C''] [Module R C'']
variable [AddCommGroup D''] [Module R D'']

theorem inducedDualImageMap_comp
    (evaluation'' : C'' →ₗ[R] Module.Dual R D'')
    (carrierMap₁ : C →ₗ[R] C') (carrierMap₂ : C' →ₗ[R] C'')
    (dualMap₁ : D' →ₗ[R] D) (dualMap₂ : D'' →ₗ[R] D')
    (naturality₁ : (inducedDualTarget dualMap₁).comp evaluation =
      evaluation'.comp carrierMap₁)
    (naturality₂ : (inducedDualTarget dualMap₂).comp evaluation' =
      evaluation''.comp carrierMap₂)
    (compositeNaturality :
      (inducedDualTarget (dualMap₁.comp dualMap₂)).comp evaluation =
        evaluation''.comp (carrierMap₂.comp carrierMap₁)) :
    inducedDualImageMap evaluation evaluation''
        (carrierMap₂.comp carrierMap₁) (dualMap₁.comp dualMap₂)
        compositeNaturality =
      (inducedDualImageMap evaluation' evaluation'' carrierMap₂ dualMap₂
        naturality₂).comp
        (inducedDualImageMap evaluation evaluation' carrierMap₁ dualMap₁
          naturality₁) := by
  apply LinearMap.ext
  intro value
  apply Subtype.ext
  rfl

end
end SourceGeneratedScalarExactEnvelope
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
