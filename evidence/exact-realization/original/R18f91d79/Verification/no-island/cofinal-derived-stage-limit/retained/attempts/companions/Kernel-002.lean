import SaturationMonoid.GenericFoundation.Cofinal.Topology.Cochain.SequentialDifference
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe w
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SequentialHomotopyLimit

open CategoryTheory CategoryTheory.Limits
open RootGeneratedSequentialHomotopyLimitAt

variable {Root : Type w}
variable {occurrence : RootedAccountedUnfolding (Root × (ℕᵒᵖ ⥤ IntegralCochainComplex))}
variable (face : RootGeneratedSequentialHomotopyLimitAt occurrence)
variable (cone : Cone face.actualTower)

def limitProductMap : cone.pt ⟶ face.productComplex :=
  Pi.lift (fun stage : Nat => cone.π.app (Opposite.op stage))

theorem limit_product_projection (stage : Nat) :
    limitProductMap face cone ≫ face.productProjection stage = cone.π.app (Opposite.op stage) :=
  Pi.lift_π _ stage

private theorem limit_product_zero : limitProductMap face cone ≫ face.difference = 0 := by
  apply Pi.hom_ext
  intro stage
  let inclusion := limitProductMap face cone
  let transition := face.transitionAt stage
  have shifts : inclusion ≫ face.shiftComponent stage = cone.π.app (Opposite.op stage) :=
    (Category.assoc inclusion (face.productProjection (stage+1)) transition).symm.trans
      ((congrArg (fun projected => projected ≫ transition) (limit_product_projection face cone (stage+1))).trans
        (cone.w (homOfLE (Nat.le_add_right stage 1)).op))
  rw [Category.assoc, face.difference_projection, Preadditive.comp_sub, limit_product_projection face cone, zero_comp]
  exact sub_eq_zero.mpr shifts.symm

private def compatibleProductCone {K : IntegralCochainComplex} (map : K ⟶ face.productComplex)
    (zero : map ≫ face.difference = 0) : Cone face.actualTower :=
  Cone.mk K (NatTrans.ofOpSequence (fun stage => map ≫ face.productProjection stage) (by
    intro stage
    have compatible := congrArg (fun action => action ≫ face.productProjection stage) zero
    rw [Category.assoc, face.difference_projection, Preadditive.comp_sub, zero_comp] at compatible
    change 𝟙 K ≫ (map ≫ face.productProjection stage) =
      (map ≫ face.productProjection (stage+1)) ≫ face.transitionAt stage
    exact (Category.id_comp _).trans ((sub_eq_zero.mp compatible).trans
      (Category.assoc map (face.productProjection (stage+1)) (face.transitionAt stage)).symm)))

/-- The actual compatibility kernel is the strict limit of the original cochain tower. -/
def limitProductKernel (lim : IsLimit cone) :
    IsLimit (KernelFork.ofι (limitProductMap face cone) (limit_product_zero face cone)) := by
  refine KernelFork.IsLimit.ofι _ _ (fun map zero => lim.lift (compatibleProductCone face map zero)) ?_ ?_
  · intro K map zero
    apply Pi.hom_ext
    intro stage
    rw [Category.assoc, limit_product_projection]
    exact lim.fac (compatibleProductCone face map zero) (Opposite.op stage)
  · intro K map zero candidate equation
    apply lim.hom_ext
    rintro ⟨stage⟩
    have read := congrArg (fun action => action ≫ face.productProjection stage) equation
    rw [Category.assoc, limit_product_projection] at read
    exact read.trans (lim.fac (compatibleProductCone face map zero) (Opposite.op stage)).symm

def limitDifferenceSequence : ShortComplex IntegralCochainComplex :=
  ShortComplex.mk (limitProductMap face cone) face.difference (limit_product_zero face cone)

/-- The existing product difference and strict limit generate the short exact sequence. -/
theorem limit_difference_short_exact (lim : IsLimit cone)
    (onto : ∀ (degree : ℤ) (stage : Nat), Function.Surjective ((face.transitionAt stage).f degree)) :
    (limitDifferenceSequence face cone).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _ (limitProductKernel face cone lim)
  mono_f := Fork.IsLimit.mono (limitProductKernel face cone lim)
  epi_g := difference_epi_of_surjective face onto

end SequentialHomotopyLimit
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
