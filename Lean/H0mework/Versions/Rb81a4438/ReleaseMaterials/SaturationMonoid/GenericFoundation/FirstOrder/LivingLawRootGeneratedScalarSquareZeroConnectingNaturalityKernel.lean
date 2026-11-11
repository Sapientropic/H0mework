import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.FirstOrder.LivingLawRootGeneratedScalarSquareZeroConnectingKernel

/-!
# Naturality of the scalar square-zero connecting kernel

An equivariant source map transports the pair matrix, fixed kernel, fixed
cokernel, and connecting map.  Identity and composition are strict.  No
injectivity, surjectivity, finite presentation, or domain result is assumed.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedScalarSquareZeroFirstOrder

noncomputable section

universe r m n p

variable {R : Type r} [CommRing R]
variable {M : Type m} [AddCommGroup M] [Module R M]
variable {N : Type n} [AddCommGroup N] [Module R N]

structure EquivariantMap
    (sourceAction : M →ₗ[R] M) (targetAction : N →ₗ[R] N) where
  sourceMap : M →ₗ[R] N
  commutes : sourceMap.comp sourceAction =
    targetAction.comp sourceMap

namespace EquivariantMap

def pairMap {sourceAction : M →ₗ[R] M}
    {targetAction : N →ₗ[R] N}
    (morphism : EquivariantMap sourceAction targetAction) :
    (M × M) →ₗ[R] (N × N) :=
  (morphism.sourceMap.comp (LinearMap.fst R M M)).prod
    (morphism.sourceMap.comp (LinearMap.snd R M M))

@[simp] theorem pairMap_apply
    {sourceAction : M →ₗ[R] M}
    {targetAction : N →ₗ[R] N}
    (morphism : EquivariantMap sourceAction targetAction)
    (value : M × M) :
    morphism.pairMap value =
      (morphism.sourceMap value.1, morphism.sourceMap value.2) := by
  rfl

theorem pairOperator_naturality
    {sourceAction : M →ₗ[R] M}
    {targetAction : N →ₗ[R] N}
    (morphism : EquivariantMap sourceAction targetAction)
    (derivative : R) :
    morphism.pairMap.comp (pairOperator sourceAction derivative) =
      (pairOperator targetAction derivative).comp morphism.pairMap := by
  apply LinearMap.ext
  intro value
  have commute := LinearMap.congr_fun morphism.commutes value.1
  have commute' := LinearMap.congr_fun morphism.commutes value.2
  simp only [LinearMap.comp_apply, pairMap_apply, pairOperator_apply,
    map_sub, map_smul]
  simp only [LinearMap.comp_apply] at commute commute'
  rw [commute, commute']

def fixedKernelMap
    {sourceAction : M →ₗ[R] M}
    {targetAction : N →ₗ[R] N}
    (morphism : EquivariantMap sourceAction targetAction) :
    FixedKernel sourceAction →ₗ[R] FixedKernel targetAction where
  toFun value := ⟨morphism.sourceMap value.1, by
    rw [LinearMap.mem_ker]
    change morphism.sourceMap value.1 -
      targetAction (morphism.sourceMap value.1) = 0
    have commute := LinearMap.congr_fun morphism.commutes value.1
    simp only [LinearMap.comp_apply] at commute
    rw [← commute, ← map_sub]
    have fixed := LinearMap.mem_ker.mp value.2
    change value.1 - sourceAction value.1 = 0 at fixed
    rw [fixed, map_zero]⟩
  map_add' left right := by
    apply Subtype.ext
    exact map_add morphism.sourceMap left.1 right.1
  map_smul' scalar value := by
    apply Subtype.ext
    exact map_smul morphism.sourceMap scalar value.1

def fixedCokernelMap
    {sourceAction : M →ₗ[R] M}
    {targetAction : N →ₗ[R] N}
    (morphism : EquivariantMap sourceAction targetAction) :
    FixedCokernel sourceAction →ₗ[R] FixedCokernel targetAction :=
  Submodule.liftQ _
    ((Submodule.mkQ (LinearMap.range (fixedDifference targetAction))).comp
      morphism.sourceMap) (by
        intro value membership
        rw [LinearMap.mem_ker, LinearMap.comp_apply,
          Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        rcases membership with ⟨preimage, rfl⟩
        refine ⟨morphism.sourceMap preimage, ?_⟩
        have commute := LinearMap.congr_fun morphism.commutes preimage
        simp only [fixedDifference, LinearMap.comp_apply,
          LinearMap.sub_apply, LinearMap.id_apply, map_sub] at commute ⊢
        rw [commute])

theorem pairConnecting_naturality
    {sourceAction : M →ₗ[R] M}
    {targetAction : N →ₗ[R] N}
    (morphism : EquivariantMap sourceAction targetAction)
    (derivative : R) :
    (morphism.fixedCokernelMap).comp
        (pairConnecting sourceAction derivative) =
      (pairConnecting targetAction derivative).comp
        morphism.fixedKernelMap := by
  apply LinearMap.ext
  intro value
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    pairConnecting_apply, pairConnecting_apply]
  unfold fixedCokernelMap fixedKernelMap
  rw [Submodule.liftQ_apply, LinearMap.comp_apply,
    Submodule.mkQ_apply]
  change Submodule.Quotient.mk
      (morphism.sourceMap ((-derivative) • value.1)) =
    Submodule.Quotient.mk
      ((-derivative) • morphism.sourceMap value.1)
  rw [map_smul]

def identity (action : M →ₗ[R] M) :
    EquivariantMap action action where
  sourceMap := LinearMap.id
  commutes := by rfl

def comp
    {P : Type p} [AddCommGroup P] [Module R P]
    {sourceAction : M →ₗ[R] M}
    {middleAction : N →ₗ[R] N}
    {targetAction : P →ₗ[R] P}
    (second : EquivariantMap middleAction targetAction)
    (first : EquivariantMap sourceAction middleAction) :
    EquivariantMap sourceAction targetAction where
  sourceMap := second.sourceMap.comp first.sourceMap
  commutes := by
    apply LinearMap.ext
    intro value
    have firstCommutes := LinearMap.congr_fun first.commutes value
    have secondCommutes := LinearMap.congr_fun second.commutes
      (first.sourceMap value)
    simp only [LinearMap.comp_apply] at firstCommutes secondCommutes ⊢
    rw [firstCommutes, secondCommutes]

@[simp] theorem pairMap_identity (action : M →ₗ[R] M) :
    (identity action).pairMap = LinearMap.id := by
  apply LinearMap.ext
  intro value
  exact Prod.ext rfl rfl

@[simp] theorem fixedKernelMap_identity (action : M →ₗ[R] M) :
    (identity action).fixedKernelMap = LinearMap.id := by
  apply LinearMap.ext
  intro value
  apply Subtype.ext
  rfl

@[simp] theorem fixedCokernelMap_identity (action : M →ₗ[R] M) :
    (identity action).fixedCokernelMap = LinearMap.id := by
  apply LinearMap.ext
  intro value
  refine Submodule.Quotient.induction_on _ value ?_
  intro representative
  rfl

theorem pairMap_comp
    {P : Type p} [AddCommGroup P] [Module R P]
    {sourceAction : M →ₗ[R] M}
    {middleAction : N →ₗ[R] N}
    {targetAction : P →ₗ[R] P}
    (second : EquivariantMap middleAction targetAction)
    (first : EquivariantMap sourceAction middleAction) :
    (comp second first).pairMap =
      second.pairMap.comp first.pairMap := by
  apply LinearMap.ext
  intro value
  exact Prod.ext rfl rfl

theorem fixedKernelMap_comp
    {P : Type p} [AddCommGroup P] [Module R P]
    {sourceAction : M →ₗ[R] M}
    {middleAction : N →ₗ[R] N}
    {targetAction : P →ₗ[R] P}
    (second : EquivariantMap middleAction targetAction)
    (first : EquivariantMap sourceAction middleAction) :
    (comp second first).fixedKernelMap =
      second.fixedKernelMap.comp first.fixedKernelMap := by
  apply LinearMap.ext
  intro value
  apply Subtype.ext
  rfl

theorem fixedCokernelMap_comp
    {P : Type p} [AddCommGroup P] [Module R P]
    {sourceAction : M →ₗ[R] M}
    {middleAction : N →ₗ[R] N}
    {targetAction : P →ₗ[R] P}
    (second : EquivariantMap middleAction targetAction)
    (first : EquivariantMap sourceAction middleAction) :
    (comp second first).fixedCokernelMap =
      second.fixedCokernelMap.comp first.fixedCokernelMap := by
  apply LinearMap.ext
  intro value
  refine Submodule.Quotient.induction_on _ value ?_
  intro representative
  rfl

end EquivariantMap

end


end SourceGeneratedScalarSquareZeroFirstOrder
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
