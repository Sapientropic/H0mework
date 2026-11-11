import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.FirstOrder.LivingLawRootGeneratedDualNumberPairBaseChangeKernel
import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.FirstOrder.LivingLawRootGeneratedScalarSquareZeroConnectingKernel

/-!
# Naturality and operator conjugacy for the dual-number pair chart

The canonical pair chart is natural for every source-module map.  More
strongly, it conjugates the actual scalar-extended operator
`1 - (1 + aε)F` to the generic constant/infinitesimal `pairOperator`.
Thus the pair matrix is a faithful coordinate of the actual change-of-rings
carrier, not an independently postulated comparison.
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

def ordinaryExtensionMap
    (f : R →+* K) {M N : ModuleCat.{max u m} R}
    (map : M ⟶ N) :
    ordinaryExtension f M →ₗ[K] ordinaryExtension f N :=
  ((ModuleCat.extendScalars f).map map).hom

def dualExtensionMap
    (f : R →+* K) {M N : ModuleCat.{max u m} R}
    (map : M ⟶ N) :
    dualExtension f M →ₗ[DualNumber K] dualExtension f N :=
  ((ModuleCat.extendScalars (baseToDual f)).map map).hom

@[simp] theorem dualExtensionMap_tmul
    (f : R →+* K) {M N : ModuleCat.{max u m} R}
    (map : M ⟶ N) (coefficient : DualNumber K) (value : M) :
    dualExtensionMap f map (dualPureTensor f M coefficient value) =
      dualPureTensor f N coefficient (map value) := by
  rfl

def restrictedDualExtensionMap
    (f : R →+* K) {M N : ModuleCat.{max u m} R}
    (map : M ⟶ N) :
    restrictedDualExtension f M →ₗ[K] restrictedDualExtension f N :=
  ((ModuleCat.restrictScalars (TrivSqZeroExt.inlHom K K)).map
    ((ModuleCat.extendScalars (baseToDual f)).map map)).hom

def scalarPairMap {X Y : Type*} [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y] (map : X →ₗ[K] Y) :
    (X × X) →ₗ[K] (Y × Y) :=
  (map.comp (LinearMap.fst K X X)).prod
    (map.comp (LinearMap.snd K X X))

@[simp] theorem scalarPairMap_apply
    {X Y : Type*} [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y] (map : X →ₗ[K] Y)
    (value : X × X) :
    scalarPairMap map value = (map value.1, map value.2) := by
  rfl

@[simp] theorem ordinaryExtensionMap_tmul
    (f : R →+* K) {M N : ModuleCat.{max u m} R}
    (map : M ⟶ N) (coefficient : K) (value : M) :
    ordinaryExtensionMap f map
        (ordinaryPureTensor f M coefficient value) =
      ordinaryPureTensor f N coefficient (map value) := by
  rfl

@[simp] theorem restrictedDualExtensionMap_tmul
    (f : R →+* K) {M N : ModuleCat.{max u m} R}
    (map : M ⟶ N) (coefficient : DualNumber K) (value : M) :
    restrictedDualExtensionMap f map
        (restrictedDualPureTensor f M coefficient value) =
      restrictedDualPureTensor f N coefficient (map value) := by
  rfl

/-- Source maps commute with the canonical pair coordinate. -/
theorem scalarExtensionPairEquiv_naturality
    (f : R →+* K) {M N : ModuleCat.{max u m} R}
    (map : M ⟶ N) :
    (scalarPairMap (ordinaryExtensionMap f map)).comp
        (scalarExtensionPairEquiv f M).toLinearMap =
      (scalarExtensionPairEquiv f N).toLinearMap.comp
        (restrictedDualExtensionMap f map) := by
  apply LinearMap.ext
  intro input
  change scalarPairMap (ordinaryExtensionMap f map)
      (scalarExtensionPairEquiv f M input) =
    scalarExtensionPairEquiv f N
      (restrictedDualExtensionMap f map input)
  obtain ⟨rawInput, rfl⟩ :=
    (restrictedDualUnderlyingAddEquiv f M).symm.surjective input
  induction rawInput using TensorProduct.induction_on with
  | zero =>
      rw [map_zero, map_zero, map_zero]
      exact (scalarExtensionPairEquiv f N).map_zero.symm
  | tmul coefficient value =>
      let coefficient' : DualNumber K :=
        (coefficient.fst, coefficient.snd)
      change scalarPairMap (ordinaryExtensionMap f map)
          (scalarExtensionPairEquiv f M
            (restrictedDualPureTensor f M coefficient' value)) =
        scalarExtensionPairEquiv f N
          (restrictedDualExtensionMap f map
            (restrictedDualPureTensor f M coefficient' value))
      rw [scalarExtensionPairEquiv_tmul]
      change
        (ordinaryExtensionMap f map
            (ordinaryPureTensor f M coefficient'.fst value),
          ordinaryExtensionMap f map
            (ordinaryPureTensor f M coefficient'.snd value)) = _
      rw [ordinaryExtensionMap_tmul, ordinaryExtensionMap_tmul,
        restrictedDualExtensionMap_tmul, scalarExtensionPairEquiv_tmul]
  | add left right leftLaw rightLaw =>
      rw [map_add, map_add, map_add, map_add, leftLaw, rightLaw]
      exact (scalarExtensionPairEquiv f N).map_add _ _ |>.symm

def dualWeight (derivative : K) : DualNumber K :=
  1 + TrivSqZeroExt.inr derivative

@[simp] theorem dualWeight_fst (derivative : K) :
    (dualWeight derivative).fst = 1 := by
  change 1 + 0 = (1 : K)
  simp

@[simp] theorem dualWeight_snd (derivative : K) :
    (dualWeight derivative).snd = derivative := by
  change 0 + derivative = derivative
  simp

/-- The actual dual-number-linear operator before forgetting to the
constant scalar ring. -/
def dualFirstOrderOperator
    (f : R →+* K) (M : ModuleCat.{max u m} R)
    (action : M ⟶ M) (derivative : K) :
    dualExtension f M →ₗ[DualNumber K] dualExtension f M :=
  LinearMap.id - dualWeight derivative • dualExtensionMap f action

def restrictedDualFirstOrderOperator
    (f : R →+* K) (M : ModuleCat.{max u m} R)
    (action : M ⟶ M) (derivative : K) :
    restrictedDualExtension f M →ₗ[K] restrictedDualExtension f M :=
  ((ModuleCat.restrictScalars (TrivSqZeroExt.inlHom K K)).map
    (ModuleCat.ofHom
      (dualFirstOrderOperator f M action derivative))).hom

@[simp] theorem dualFirstOrderOperator_tmul
    (f : R →+* K) (M : ModuleCat.{max u m} R)
    (action : M ⟶ M) (derivative : K)
    (coefficient : DualNumber K) (value : M) :
    dualFirstOrderOperator f M action derivative
        (dualPureTensor f M coefficient value) =
      dualPureTensor f M coefficient value -
        dualPureTensor f M (dualWeight derivative * coefficient)
          (action value) := by
  unfold dualFirstOrderOperator
  rw [LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.smul_apply, dualExtensionMap_tmul,
    smul_dualPureTensor]

@[simp] theorem restrictedDualFirstOrderOperator_tmul
    (f : R →+* K) (M : ModuleCat.{max u m} R)
    (action : M ⟶ M) (derivative : K)
    (coefficient : DualNumber K) (value : M) :
    restrictedDualFirstOrderOperator f M action derivative
        (restrictedDualPureTensor f M coefficient value) =
      restrictedDualPureTensor f M coefficient value -
        restrictedDualPureTensor f M
          (dualWeight derivative * coefficient) (action value) := by
  exact dualFirstOrderOperator_tmul f M action derivative coefficient value

/-- The actual dual-number operator is precisely the generic pair matrix in
the canonical constant/infinitesimal chart. -/
theorem scalarExtensionPairEquiv_operator_conjugacy
    (f : R →+* K) (M : ModuleCat.{max u m} R)
    (action : M ⟶ M) (derivative : K) :
    (scalarExtensionPairEquiv f M).toLinearMap.comp
        (restrictedDualFirstOrderOperator f M action derivative) =
      (pairOperator (ordinaryExtensionMap f action) derivative).comp
        (scalarExtensionPairEquiv f M).toLinearMap := by
  apply LinearMap.ext
  intro input
  change scalarExtensionPairEquiv f M
      (restrictedDualFirstOrderOperator f M action derivative input) =
    pairOperator (ordinaryExtensionMap f action) derivative
      (scalarExtensionPairEquiv f M input)
  obtain ⟨rawInput, rfl⟩ :=
    (restrictedDualUnderlyingAddEquiv f M).symm.surjective input
  induction rawInput using TensorProduct.induction_on with
  | zero =>
      rw [map_zero, map_zero, map_zero, map_zero]
  | tmul coefficient value =>
      let coefficient' : DualNumber K :=
        (coefficient.fst, coefficient.snd)
      change scalarExtensionPairEquiv f M
          (restrictedDualFirstOrderOperator f M action derivative
            (restrictedDualPureTensor f M coefficient' value)) =
        pairOperator (ordinaryExtensionMap f action) derivative
          (scalarExtensionPairEquiv f M
            (restrictedDualPureTensor f M coefficient' value))
      rw [restrictedDualFirstOrderOperator_tmul, map_sub,
        scalarExtensionPairEquiv_tmul, scalarExtensionPairEquiv_tmul,
        pairOperator_apply,
        ordinaryExtensionMap_tmul, ordinaryExtensionMap_tmul]
      apply Prod.ext
      · change
          ordinaryPureTensor f M coefficient'.fst value -
              ordinaryPureTensor f M
                ((dualWeight derivative * coefficient').fst) (action value) =
            ordinaryPureTensor f M coefficient'.fst value -
              ordinaryPureTensor f M coefficient'.fst (action value)
        rw [show (dualWeight derivative * coefficient').fst =
            coefficient'.fst by
              change (1 + 0) * coefficient'.fst = coefficient'.fst
              simp]
      · change
          ordinaryPureTensor f M coefficient'.snd value -
              ordinaryPureTensor f M
                ((dualWeight derivative * coefficient').snd) (action value) =
            ordinaryPureTensor f M coefficient'.snd value -
              ordinaryPureTensor f M coefficient'.snd (action value) -
                derivative •
                  ordinaryPureTensor f M coefficient'.fst (action value)
        rw [show (dualWeight derivative * coefficient').snd =
            coefficient'.snd + derivative * coefficient'.fst by
              change (1 + 0) * coefficient'.snd +
                  (0 + derivative) * coefficient'.fst = _
              simp]
        rw [ordinaryPureTensor_add,
          ← smul_ordinaryPureTensor]
        module
  | add left right leftLaw rightLaw =>
      rw [map_add, map_add, map_add, map_add, leftLaw, rightLaw]
      exact (pairOperator
        (ordinaryExtensionMap f action) derivative).map_add _ _ |>.symm

end


end SourceGeneratedScalarSquareZeroFirstOrder
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
