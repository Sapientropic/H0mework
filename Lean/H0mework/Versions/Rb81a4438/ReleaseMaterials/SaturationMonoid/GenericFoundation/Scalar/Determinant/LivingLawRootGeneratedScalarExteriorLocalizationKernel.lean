import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree

/-!
# Scalar exterior powers commute with localization

For a free source module, the localization of every exterior power is
canonically equivalent to the exterior power of the localized module.  The
equivalence is characterized on pure wedges and is natural for endomorphisms.
No determinant, rank or chosen output frame is an input.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedScalarExteriorLocalization

open Module Set

noncomputable section

universe r f

variable {R : Type r} [CommRing R]
variable {F : Type f} [AddCommGroup F] [Module R F]
variable [Module.Free R F]

theorem localizedMap_comp
    {A B C : Type*}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    (S : Submonoid R) (first : A →ₗ[R] B) (second : B →ₗ[R] C) :
    LocalizedModule.map S (second ∘ₗ first) =
      LocalizedModule.map S second ∘ₗ LocalizedModule.map S first := by
  apply LinearMap.restrictScalars_injective R
  apply IsLocalizedModule.linearMap_ext S
    (LocalizedModule.mkLinearMap S A) (LocalizedModule.mkLinearMap S C)
  ext value
  change LocalizedModule.map S (second ∘ₗ first)
      (LocalizedModule.mk value 1) =
    LocalizedModule.map S second
      (LocalizedModule.map S first (LocalizedModule.mk value 1))
  rw [LocalizedModule.map_mk, LocalizedModule.map_mk,
    LocalizedModule.map_mk]
  rfl

theorem localizedMap_id
    {A : Type*} [AddCommGroup A] [Module R A]
    (S : Submonoid R) :
    LocalizedModule.map S (LinearMap.id : A →ₗ[R] A) = LinearMap.id :=
  LocalizedModule.map_id S

/-- Basis-defined comparison for a free module.  Its public characterization
below is basis-free. -/
noncomputable def freeExteriorLocalizationEquiv
    (S : Submonoid R) (degree : ℕ) :
    LocalizedModule S (⋀[R]^degree F) ≃ₗ[Localization S]
      ⋀[Localization S]^degree (LocalizedModule S F) := by
  let basis := Module.Free.chooseBasis R F
  letI : LinearOrder (Module.Free.ChooseBasisIndex R F) :=
    WellOrderingRel.isWellOrder.linearOrder
  let sourceBasis :=
    IsBaseChange.basis (basis.exteriorPower degree)
      (LocalizedModule.isBaseChange S (⋀[R]^degree F))
  let targetBasis :=
    (IsBaseChange.basis basis (LocalizedModule.isBaseChange S F)).exteriorPower degree
  exact sourceBasis.equiv targetBasis (Equiv.refl _)

noncomputable def localizedIMulti
    (S : Submonoid R) (degree : ℕ) :
    F [⋀^Fin degree]→ₗ[R]
      (⋀[Localization S]^degree (LocalizedModule S F)) where
  toFun vectors :=
    exteriorPower.ιMulti (Localization S) degree
      (LocalizedModule.mkLinearMap S F ∘ vectors)
  map_update_add' vectors index x y := by
    simpa only [Function.comp_update, LinearMap.map_add] using
      (exteriorPower.ιMulti (Localization S) degree).map_update_add
        (LocalizedModule.mkLinearMap S F ∘ vectors) index
        (LocalizedModule.mkLinearMap S F x)
        (LocalizedModule.mkLinearMap S F y)
  map_update_smul' vectors index scalar x := by
    simpa only [Function.comp_update, LinearMap.map_smul,
      IsScalarTower.algebraMap_smul (Localization S)] using
      (exteriorPower.ιMulti (Localization S) degree).map_update_smul
        (LocalizedModule.mkLinearMap S F ∘ vectors) index
        (algebraMap R (Localization S) scalar)
        (LocalizedModule.mkLinearMap S F x)
  map_eq_zero_of_eq' vectors _ _ equality ne := by
    apply (exteriorPower.ιMulti (Localization S) degree).map_eq_zero_of_eq
      (LocalizedModule.mkLinearMap S F ∘ vectors)
    · exact congrArg (LocalizedModule.mkLinearMap S F) equality
    · exact ne

theorem freeExteriorLocalizationEquiv_comp_source
    (S : Submonoid R) (degree : ℕ) :
    (freeExteriorLocalizationEquiv (F := F) S degree).toLinearMap.restrictScalars R ∘ₗ
        LocalizedModule.mkLinearMap S (⋀[R]^degree F) =
      exteriorPower.alternatingMapLinearEquiv
        (localizedIMulti (F := F) S degree) := by
  let basis := Module.Free.chooseBasis R F
  letI : LinearOrder (Module.Free.ChooseBasisIndex R F) :=
    WellOrderingRel.isWellOrder.linearOrder
  let sourceBasis :=
    IsBaseChange.basis (basis.exteriorPower degree)
      (LocalizedModule.isBaseChange S (⋀[R]^degree F))
  let targetBasis :=
    (IsBaseChange.basis basis (LocalizedModule.isBaseChange S F)).exteriorPower degree
  apply (basis.exteriorPower degree).ext
  intro subset
  simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars,
    exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    LocalizedModule.mkLinearMap_apply, localizedIMulti,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  have equivalenceEq :
      freeExteriorLocalizationEquiv (F := F) S degree =
        sourceBasis.equiv targetBasis (Equiv.refl _) := rfl
  rw [equivalenceEq]
  have sourceValue :
      sourceBasis subset = LocalizedModule.mk
        (exteriorPower.ιMulti_family R degree basis subset) 1 := by
    calc
      sourceBasis subset = LocalizedModule.mk
          ((basis.exteriorPower degree) subset) 1 := by
        simpa only [LocalizedModule.mkLinearMap_apply] using
          IsBaseChange.basis_apply (basis.exteriorPower degree)
            (LocalizedModule.isBaseChange S (⋀[R]^degree F)) subset
      _ = LocalizedModule.mk
          (exteriorPower.ιMulti_family R degree basis subset) 1 := by
        rw [exteriorPower.basis_apply]
  change (sourceBasis.equiv targetBasis (Equiv.refl _))
      (LocalizedModule.mk
        (exteriorPower.ιMulti_family R degree basis subset) 1) = _
  rw [← sourceValue, Basis.equiv_apply]
  simp only [Equiv.refl_apply]
  have targetValue :
      targetBasis subset = exteriorPower.ιMulti_family (Localization S) degree
        (IsBaseChange.basis basis (LocalizedModule.isBaseChange S F)) subset := by
    change ((IsBaseChange.basis basis
      (LocalizedModule.isBaseChange S F)).exteriorPower degree) subset = _
    rw [exteriorPower.basis_apply]
  rw [targetValue]
  change exteriorPower.ιMulti_family (Localization S) degree
      (IsBaseChange.basis basis (LocalizedModule.isBaseChange S F)) subset =
    exteriorPower.ιMulti (Localization S) degree
      (LocalizedModule.mkLinearMap S F ∘ basis ∘
        powersetCard.ofFinEmbEquiv.symm subset)
  rw [exteriorPower.ιMulti_family]
  apply congrArg (exteriorPower.ιMulti (Localization S) degree)
  funext index
  simp only [Function.comp_apply, IsBaseChange.basis_apply]

/-- Pure wedges commute literally with the localization comparison. -/
theorem freeExteriorLocalizationEquiv_ιMulti
    (S : Submonoid R) (degree : ℕ)
    (vectors : Fin degree → F) :
    freeExteriorLocalizationEquiv (F := F) S degree
        (LocalizedModule.mkLinearMap S (⋀[R]^degree F)
          (exteriorPower.ιMulti R degree vectors)) =
      exteriorPower.ιMulti (Localization S) degree
        (LocalizedModule.mkLinearMap S F ∘ vectors) := by
  have equality := LinearMap.congr_fun
    (freeExteriorLocalizationEquiv_comp_source (F := F) S degree)
    (exteriorPower.ιMulti R degree vectors)
  simpa [localizedIMulti] using equality

/-- The comparison is natural for every source endomorphism. -/
theorem freeExteriorLocalizationEquiv_naturality
    (S : Submonoid R) (degree : ℕ) (linear : F →ₗ[R] F) :
    (freeExteriorLocalizationEquiv (F := F) S degree).toLinearMap ∘ₗ
        LocalizedModule.map S (exteriorPower.map degree linear) =
      exteriorPower.map degree (LocalizedModule.map S linear) ∘ₗ
        (freeExteriorLocalizationEquiv (F := F) S degree).toLinearMap := by
  let basis := Module.Free.chooseBasis R F
  letI : LinearOrder (Module.Free.ChooseBasisIndex R F) :=
    WellOrderingRel.isWellOrder.linearOrder
  let sourceBasis :=
    IsBaseChange.basis (basis.exteriorPower degree)
      (LocalizedModule.isBaseChange S (⋀[R]^degree F))
  apply sourceBasis.ext
  intro subset
  have sourceValue :
      sourceBasis subset = LocalizedModule.mk
        (exteriorPower.ιMulti_family R degree basis subset) 1 := by
    calc
      sourceBasis subset = LocalizedModule.mk
          ((basis.exteriorPower degree) subset) 1 := by
        simpa only [LocalizedModule.mkLinearMap_apply] using
          IsBaseChange.basis_apply (basis.exteriorPower degree)
            (LocalizedModule.isBaseChange S (⋀[R]^degree F)) subset
      _ = LocalizedModule.mk
          (exteriorPower.ιMulti_family R degree basis subset) 1 := by
        rw [exteriorPower.basis_apply]
  rw [sourceValue]
  simp only [LinearMap.comp_apply, LocalizedModule.map_mk,
    exteriorPower.map_apply_ιMulti, exteriorPower.ιMulti_family]
  change freeExteriorLocalizationEquiv (F := F) S degree
      (LocalizedModule.mkLinearMap S (⋀[R]^degree F)
        (exteriorPower.ιMulti R degree
          (linear ∘ basis ∘ powersetCard.ofFinEmbEquiv.symm subset))) =
    exteriorPower.map degree (LocalizedModule.map S linear)
      (freeExteriorLocalizationEquiv (F := F) S degree
        (LocalizedModule.mkLinearMap S (⋀[R]^degree F)
          (exteriorPower.ιMulti R degree
            (basis ∘ powersetCard.ofFinEmbEquiv.symm subset))))
  rw [freeExteriorLocalizationEquiv_ιMulti,
    freeExteriorLocalizationEquiv_ιMulti,
    exteriorPower.map_apply_ιMulti]
  apply congrArg (exteriorPower.ιMulti (Localization S) degree)
  funext index
  simp only [Function.comp_apply]
  change LocalizedModule.mk
      (linear (basis (powersetCard.ofFinEmbEquiv.symm subset index))) 1 =
    LocalizedModule.map S linear
      (LocalizedModule.mk
        (basis (powersetCard.ofFinEmbEquiv.symm subset index)) 1)
  rw [LocalizedModule.map_mk]

end
end SourceGeneratedScalarExteriorLocalization
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
