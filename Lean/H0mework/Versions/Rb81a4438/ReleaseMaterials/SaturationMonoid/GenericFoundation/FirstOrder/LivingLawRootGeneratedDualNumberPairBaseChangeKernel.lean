import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.DualNumber
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Canonical pair chart for dual-number scalar extension

For a ring map `R → K` and an `R`-module `M`, restriction along
`K → K[ε]` canonically identifies `K[ε] ⊗[R] M` with two copies of
`K ⊗[R] M`.  The construction explicitly crosses Mathlib's bundled
`restrictScalars` module structures, proves the pure-tensor coordinate law,
and requires no basis, finiteness, or domain-specific comparison.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedScalarSquareZeroFirstOrder

open scoped ChangeOfRings

noncomputable section

universe u m

variable {R : Type u} {K : Type u} [CommRing R] [CommRing K]

def baseToDual (f : R →+* K) : R →+* DualNumber K :=
  (TrivSqZeroExt.inlHom K K).comp f

abbrev ordinaryExtension (f : R →+* K) (M : ModuleCat.{max u m} R) :=
  (ModuleCat.extendScalars f).obj M

abbrev dualExtension (f : R →+* K) (M : ModuleCat.{max u m} R) :=
  (ModuleCat.extendScalars (baseToDual f)).obj M

abbrev restrictedDualExtension (f : R →+* K)
    (M : ModuleCat.{max u m} R) :=
  (ModuleCat.restrictScalars (TrivSqZeroExt.inlHom K K)).obj
    (dualExtension f M)

abbrev rawDualTensor (f : R →+* K) (M : ModuleCat.{max u m} R) :=
  TensorProduct R
    ((ModuleCat.restrictScalars (baseToDual f)).obj
      (ModuleCat.of (DualNumber K) (DualNumber K))) M

/-- The bundled restricted module and the raw tensor have the same additive
carrier.  Naming this bridge prevents instance identity from being mistaken
for a mathematical obstruction. -/
def restrictedDualUnderlyingAddEquiv
    (f : R →+* K) (M : ModuleCat.{max u m} R) :
    restrictedDualExtension f M ≃+ rawDualTensor f M where
  toFun value := value
  invFun value := value
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

def restrictedDualPureTensor
    (f : R →+* K) (M : ModuleCat.{max u m} R)
    (coefficient : DualNumber K) (value : M) :
    restrictedDualExtension f M :=
  coefficient ⊗ₜ[R, baseToDual f] value

def dualPureTensor
    (f : R →+* K) (M : ModuleCat.{max u m} R)
    (coefficient : DualNumber K) (value : M) : dualExtension f M :=
  coefficient ⊗ₜ[R, baseToDual f] value

noncomputable def dualUnderlyingEquiv
    (f : R →+* K) (M : ModuleCat.{max u m} R) :
    letI : Algebra R (DualNumber K) := (baseToDual f).toAlgebra
    dualExtension f M ≃ₗ[DualNumber K]
      TensorProduct R (DualNumber K) M := by
  letI : Algebra R (DualNumber K) := (baseToDual f).toAlgebra
  exact
    { toFun := fun value => value
      invFun := fun value => value
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

@[simp] theorem smul_dualPureTensor
    (f : R →+* K) (M : ModuleCat.{max u m} R)
    (scalar coefficient : DualNumber K) (value : M) :
    scalar • dualPureTensor f M coefficient value =
      dualPureTensor f M (scalar * coefficient) value := by
  letI : Algebra R (DualNumber K) := (baseToDual f).toAlgebra
  apply (dualUnderlyingEquiv f M).injective
  rfl

@[simp] theorem restrictedDualUnderlyingAddEquiv_symm_tmul
    (f : R →+* K) (M : ModuleCat.{max u m} R)
    (coefficient : DualNumber K) (value : M) :
    (restrictedDualUnderlyingAddEquiv f M).symm
        (coefficient ⊗ₜ[R, baseToDual f] value) =
      restrictedDualPureTensor f M coefficient value := by
  rfl

abbrev iteratedDualExtension
    (f : R →+* K) (M : ModuleCat.{max u m} R) :=
  (ModuleCat.extendScalars (TrivSqZeroExt.inlHom K K)).obj
    (ordinaryExtension f M)

def ordinaryPureTensor
    (f : R →+* K) (M : ModuleCat.{max u m} R)
    (coefficient : K) (value : M) : ordinaryExtension f M :=
  coefficient ⊗ₜ[R, f] value

def ordinaryUnitTensor
    (f : R →+* K) (M : ModuleCat.{max u m} R) (value : M) :
    ordinaryExtension f M :=
  ordinaryPureTensor f M 1 value

noncomputable def ordinaryUnderlyingEquiv
    (f : R →+* K) (M : ModuleCat.{max u m} R) :
    letI : Algebra R K := f.toAlgebra
    ordinaryExtension f M ≃ₗ[K] TensorProduct R K M := by
  letI : Algebra R K := f.toAlgebra
  exact
    { toFun := fun value => value
      invFun := fun value => value
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

@[simp] theorem ordinaryPureTensor_add
    (f : R →+* K) (M : ModuleCat.{max u m} R)
    (left right : K) (value : M) :
    ordinaryPureTensor f M (left + right) value =
      ordinaryPureTensor f M left value +
        ordinaryPureTensor f M right value := by
  letI : Algebra R K := f.toAlgebra
  apply (ordinaryUnderlyingEquiv f M).injective
  change (left + right) ⊗ₜ[R] value =
    left ⊗ₜ[R] value + right ⊗ₜ[R] value
  exact TensorProduct.add_tmul left right value

@[simp] theorem smul_ordinaryPureTensor
    (f : R →+* K) (M : ModuleCat.{max u m} R)
    (scalar coefficient : K) (value : M) :
    scalar • ordinaryPureTensor f M coefficient value =
      ordinaryPureTensor f M (scalar * coefficient) value := by
  letI : Algebra R K := f.toAlgebra
  apply (ordinaryUnderlyingEquiv f M).injective
  rfl

@[simp] theorem smul_ordinaryUnitTensor
    (f : R →+* K) (M : ModuleCat.{max u m} R)
    (scalar : K) (value : M) :
    scalar • ordinaryUnitTensor f M value =
      ordinaryPureTensor f M scalar value := by
  rw [ordinaryUnitTensor, smul_ordinaryPureTensor, mul_one]

abbrev iteratedDualAsBase (X : ModuleCat.{max u m} K) :=
  (ModuleCat.restrictScalars (TrivSqZeroExt.inlHom K K)).obj
    ((ModuleCat.extendScalars (TrivSqZeroExt.inlHom K K)).obj X)

abbrev dualNumberAsBase :=
  (ModuleCat.restrictScalars (TrivSqZeroExt.inlHom K K)).obj
    (ModuleCat.of (DualNumber K) (DualNumber K))

noncomputable def dualNumberEquivProd :
    dualNumberAsBase (K := K) ≃ₗ[K] K × K where
  toFun value := (value.fst, value.snd)
  invFun value := (value.1, value.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' scalar value := by
    apply Prod.ext
    · change ((TrivSqZeroExt.inl scalar : DualNumber K) *
          (show DualNumber K from value)).fst = scalar * value.fst
      rfl
    · change ((TrivSqZeroExt.inl scalar : DualNumber K) *
          (show DualNumber K from value)).snd = scalar * value.snd
      change scalar * value.snd + 0 * value.fst = scalar * value.snd
      simp

noncomputable def iteratedUnderlyingEquiv (X : ModuleCat.{max u m} K) :
    iteratedDualAsBase X ≃ₗ[K]
      TensorProduct K (dualNumberAsBase (K := K)) X where
  toFun value := value
  invFun value := value
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def iteratedPairEquiv (X : ModuleCat.{max u m} K) :
    iteratedDualAsBase X ≃ₗ[K] X × X := by
  exact (iteratedUnderlyingEquiv X).trans
    (((dualNumberEquivProd (K := K)).rTensor X).trans
      ((TensorProduct.prodLeft K K K K X).trans
        ((TensorProduct.lid K X).prodCongr (TensorProduct.lid K X))))

def iteratedPureTensor
    (X : ModuleCat.{max u m} K)
    (coefficient : DualNumber K) (value : X) :
    iteratedDualAsBase X :=
  coefficient ⊗ₜ[K, TrivSqZeroExt.inlHom K K] value

@[simp] theorem iteratedPairEquiv_tmul
    (X : ModuleCat.{max u m} K) (coefficient : DualNumber K) (value : X) :
    iteratedPairEquiv X (iteratedPureTensor X coefficient value) =
      (coefficient.fst • value, coefficient.snd • value) := by
  rfl

/-- Canonical change-of-rings equivalence through the actual
`extendScalars` and `restrictScalars` objects. -/
noncomputable def scalarExtensionPairEquiv
    (f : R →+* K) (M : ModuleCat.{max u m} R) :
    restrictedDualExtension f M ≃ₗ[K]
      ordinaryExtension f M × ordinaryExtension f M := by
  let compositionIso := ModuleCat.extendScalarsComp.{u, m} f
    (TrivSqZeroExt.inlHom K K)
  let restrictedCompositionIso :=
    (ModuleCat.restrictScalars
      (TrivSqZeroExt.inlHom K K)).mapIso (compositionIso.app M)
  exact restrictedCompositionIso.toLinearEquiv.trans
    (iteratedPairEquiv (ordinaryExtension f M))

theorem extendScalarsComp_tmul
    (f : R →+* K) (M : ModuleCat.{max u m} R)
    (coefficient : DualNumber K) (value : M) :
    (ModuleCat.extendScalarsComp.{u, m} f
        (TrivSqZeroExt.inlHom K K)).hom.app M
          (coefficient ⊗ₜ[R, baseToDual f] value) =
      iteratedPureTensor (ordinaryExtension f M) coefficient
        (ordinaryUnitTensor f M value) := by
  have sourceScale := ModuleCat.ExtendScalars.smul_tmul
    (baseToDual f) coefficient 1 value
  simp only [mul_one] at sourceScale
  have mappedSourceScale := congrArg
    (fun input =>
      (ModuleCat.extendScalarsComp.{u, m} f
        (TrivSqZeroExt.inlHom K K)).hom.app M input)
    sourceScale
  have mapScale :=
    ((ModuleCat.extendScalarsComp.{u, m} f
      (TrivSqZeroExt.inlHom K K)).hom.app M).hom.map_smul
        coefficient
        ((1 : DualNumber K) ⊗ₜ[R, baseToDual f] value)
  have mapOne := ModuleCat.extendScalarsComp_hom_app_one_tmul
    f (TrivSqZeroExt.inlHom K K) M value
  have scaledMapOne := congrArg
    (fun output : iteratedDualExtension f M => coefficient • output) mapOne
  have targetScale := ModuleCat.ExtendScalars.smul_tmul
    (TrivSqZeroExt.inlHom K K) coefficient 1
      (ordinaryUnitTensor f M value)
  simp only [mul_one] at targetScale
  exact mappedSourceScale.symm.trans
    (mapScale.trans (scaledMapOne.trans targetScale))

@[simp] theorem scalarExtensionPairEquiv_tmul
    (f : R →+* K) (M : ModuleCat.{max u m} R)
    (coefficient : DualNumber K) (value : M) :
    scalarExtensionPairEquiv f M
        (restrictedDualPureTensor f M coefficient value) =
      (ordinaryPureTensor f M coefficient.fst value,
        ordinaryPureTensor f M coefficient.snd value) := by
  unfold scalarExtensionPairEquiv
  change iteratedPairEquiv (ordinaryExtension f M)
      ((ModuleCat.extendScalarsComp.{u, m} f
        (TrivSqZeroExt.inlHom K K)).hom.app M
          (coefficient ⊗ₜ[R, baseToDual f] value)) = _
  rw [extendScalarsComp_tmul, iteratedPairEquiv_tmul]
  apply Prod.ext
  · exact smul_ordinaryUnitTensor f M coefficient.fst value
  · exact smul_ordinaryUnitTensor f M coefficient.snd value

end


end SourceGeneratedScalarSquareZeroFirstOrder
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
