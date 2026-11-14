import H0mework.Versions.R21a4a7ce.ReleaseMaterials.SaturationMonoid.CochainH1KernelConditionProducer

/-!
# H1 kernel-condition containment

This module turns cyclewise containment between two degree-one cohomology
kernel conditions into the canonical morphism between their kernel objects,
together with its defining inclusion square.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace CochainH1KernelConditionContainment

open CategoryTheory
open CategoryTheory.Limits
open CochainH1KernelConditionProducer

noncomputable section

set_option maxHeartbeats 3000000

/-- A vanishing degree-one homology class exposes an actual degree-zero
boundary in any `ModuleCat ℤ` cochain complex. -/
theorem exists_degreeOne_boundary_of_homologyπ_eq_zero
    (C : CochainComplex (ModuleCat ℤ) ℕ)
    (z : C.cycles 1)
    (hzero : (C.homologyπ 1).hom z = 0) :
    ∃ q₀ : C.X 0, (C.d 0 1).hom q₀ = (C.iCycles 1).hom z := by
  let B : ShortComplex (ModuleCat ℤ) :=
    ShortComplex.mk (C.toCycles 0 1) (C.homologyπ 1)
      (C.toCycles_comp_homologyπ 0 1)
  have hB : B.Exact :=
    B.exact_of_g_is_cokernel (C.homologyIsCokernel 0 1 (by simp))
  obtain ⟨q₀, hq₀⟩ :=
    (CategoryTheory.ShortComplex.moduleCat_exact_iff B).mp hB z hzero
  refine ⟨q₀, ?_⟩
  have hto := ConcreteCategory.congr_hom (C.toCycles_i 0 1) q₀
  simp only [ConcreteCategory.comp_apply] at hto
  exact hto.symm.trans (congrArg (fun x ↦ (C.iCycles 1).hom x) hq₀)

/-- Cyclewise containment of two degree-one kernel conditions forces the
corresponding composite from the first kernel object to vanish. -/
theorem conditionH1_comp_h1Map_eq_zero_of_cycle_containment
    {C D E : CochainComplex (ModuleCat ℤ) ℕ}
    (phi : C ⟶ D) (psi : C ⟶ E)
    (hcontain : ∀ z : C.cycles 1,
      (h1Map phi).hom ((C.homologyπ 1).hom z) = 0 →
        (h1Map psi).hom ((C.homologyπ 1).hom z) = 0) :
    kernel.ι (h1Map phi) ≫ h1Map psi = 0 := by
  let conditionProjection := projection phi
  letI : Epi conditionProjection := inferInstance
  apply (cancel_epi conditionProjection).1
  ext x
  simp only [Category.assoc, ConcreteCategory.comp_apply,
    ModuleCat.hom_zero, LinearMap.zero_apply]
  have hpullback := ConcreteCategory.congr_hom
    (show
      projection phi ≫ kernel.ι (h1Map phi) =
        pullback.snd (kernel.ι (h1Map phi)) (C.homologyπ 1) ≫ C.homologyπ 1
      from pullback.condition) x
  simp only [ConcreteCategory.comp_apply] at hpullback
  let z : C.cycles 1 :=
    (pullback.snd (kernel.ι (h1Map phi)) (C.homologyπ 1)).hom x
  have hphi := ConcreteCategory.congr_hom (kernel.condition (h1Map phi))
    ((projection phi).hom x)
  simp only [ConcreteCategory.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] at hphi
  have hphiZ : (h1Map phi).hom ((C.homologyπ 1).hom z) = 0 := by
    rw [← hpullback]
    exact hphi
  rw [hpullback]
  exact hcontain z hphiZ

/-- Canonical morphism between two source-native H1-kernel conditions once
cyclewise containment has been generated. -/
noncomputable def conditionH1MapOfCycleContainment
    {C D E : CochainComplex (ModuleCat ℤ) ℕ}
    (phi : C ⟶ D) (psi : C ⟶ E)
    (hcontain : ∀ z : C.cycles 1,
      (h1Map phi).hom ((C.homologyπ 1).hom z) = 0 →
        (h1Map psi).hom ((C.homologyπ 1).hom z) = 0) :
    ConditionH1 phi ⟶ ConditionH1 psi :=
  kernel.lift (h1Map psi) (kernel.ι (h1Map phi))
    (conditionH1_comp_h1Map_eq_zero_of_cycle_containment phi psi hcontain)

@[reassoc]
theorem conditionH1MapOfCycleContainment_inclusion
    {C D E : CochainComplex (ModuleCat ℤ) ℕ}
    (phi : C ⟶ D) (psi : C ⟶ E)
    (hcontain : ∀ z : C.cycles 1,
      (h1Map phi).hom ((C.homologyπ 1).hom z) = 0 →
        (h1Map psi).hom ((C.homologyπ 1).hom z) = 0) :
    conditionH1MapOfCycleContainment phi psi hcontain ≫
        kernel.ι (h1Map psi) =
      kernel.ι (h1Map phi) := by
  apply kernel.lift_ι


end

end CochainH1KernelConditionContainment
end SaturationMonoid

