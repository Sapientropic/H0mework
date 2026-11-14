import H0mework.Versions.R21a4a7ce.ReleaseMaterials.SaturationMonoid.CochainH1SubobjectConditionProducer

/-!
# Generic H1-kernel condition producer

This compatibility facade specializes the generic degree-one subobject
producer to `ker H¹(φ) ↪ H¹(C)`.  All complexes, maps, exactness proofs and
homology readouts are inherited definitionally from that single positive
construction.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace CochainH1KernelConditionProducer

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

noncomputable section

variable {C D : CochainComplex (ModuleCat ℤ) ℕ} (φ : C ⟶ D)

noncomputable abbrev h1Map : C.homology 1 ⟶ D.homology 1 :=
  HomologicalComplex.homologyMap φ 1

noncomputable abbrev ConditionH1 : ModuleCat ℤ := kernel (h1Map φ)

private noncomputable abbrev conditionInclusion :
    ConditionH1 φ ⟶ C.homology 1 := kernel.ι (h1Map φ)

noncomputable abbrev ConditionCycles : ModuleCat ℤ :=
  CochainH1SubobjectConditionProducer.ConditionCycles (conditionInclusion φ)

theorem boundary_condition :
    (0 : C.X 0 ⟶ ConditionH1 φ) ≫ conditionInclusion φ =
      C.toCycles 0 1 ≫ C.homologyπ 1 :=
  CochainH1SubobjectConditionProducer.boundary_condition
    (conditionInclusion φ)

noncomputable abbrev boundary : C.X 0 ⟶ ConditionCycles φ :=
  CochainH1SubobjectConditionProducer.boundary (conditionInclusion φ)

noncomputable abbrev projection : ConditionCycles φ ⟶ ConditionH1 φ :=
  CochainH1SubobjectConditionProducer.projection (conditionInclusion φ)

@[reassoc]
theorem boundary_projection : boundary φ ≫ projection φ = 0 :=
  CochainH1SubobjectConditionProducer.boundary_projection
    (conditionInclusion φ)

noncomputable abbrev conditionShortComplex : ShortComplex (ModuleCat ℤ) :=
  CochainH1SubobjectConditionProducer.conditionShortComplex
    (conditionInclusion φ)

theorem boundary_exact : (conditionShortComplex φ).Exact :=
  CochainH1SubobjectConditionProducer.boundary_exact (conditionInclusion φ)

noncomputable abbrev projectionIsCokernel :=
  CochainH1SubobjectConditionProducer.projectionIsCokernel
    (conditionInclusion φ)

noncomputable abbrev ConditionComplex : CochainComplex (ModuleCat ℤ) ℕ :=
  CochainH1SubobjectConditionProducer.ConditionComplex (conditionInclusion φ)

@[simp]
theorem conditionComplex_X_zero :
    (ConditionComplex φ).X 0 = C.X 0 :=
  CochainH1SubobjectConditionProducer.conditionComplex_X_zero
    (conditionInclusion φ)

@[simp]
theorem conditionComplex_X_one :
    (ConditionComplex φ).X 1 = ConditionCycles φ :=
  CochainH1SubobjectConditionProducer.conditionComplex_X_one
    (conditionInclusion φ)

@[simp]
theorem conditionComplex_d_zero_one :
    (ConditionComplex φ).d 0 1 = boundary φ :=
  CochainH1SubobjectConditionProducer.conditionComplex_d_zero_one
    (conditionInclusion φ)

@[simp]
theorem conditionComplex_d_one_two :
    (ConditionComplex φ).d 1 2 = 0 :=
  CochainH1SubobjectConditionProducer.conditionComplex_d_one_two
    (conditionInclusion φ)

@[reassoc]
theorem boundary_snd :
    boundary φ ≫ pullback.snd (conditionInclusion φ) (C.homologyπ 1) =
      C.toCycles 0 1 :=
  CochainH1SubobjectConditionProducer.boundary_snd (conditionInclusion φ)

noncomputable def conditionToSourceDegree :
    ∀ i : ℕ, (ConditionComplex φ).X i ⟶ C.X i
  | 0 => 𝟙 _
  | 1 =>
      pullback.snd (conditionInclusion φ) (C.homologyπ 1) ≫ C.iCycles 1
  | _ + 2 => 0

theorem conditionToSourceDegree_comm (i : ℕ) :
    conditionToSourceDegree φ i ≫ C.d i (i + 1) =
      (ConditionComplex φ).d i (i + 1) ≫
        conditionToSourceDegree φ (i + 1) :=
  CochainH1SubobjectConditionProducer.conditionToSourceDegree_comm
    (conditionInclusion φ) i

noncomputable def conditionToSource : ConditionComplex φ ⟶ C where
  f := conditionToSourceDegree φ
  comm' i j hij := by
    subst j
    exact conditionToSourceDegree_comm φ i

@[simp] theorem conditionToSource_f_zero :
    (conditionToSource φ).f 0 = 𝟙 _ := by
  rfl

noncomputable abbrev conditionCyclesIsoXOne :
    (ConditionComplex φ).cycles 1 ≅ ConditionCycles φ :=
  CochainH1SubobjectConditionProducer.conditionCyclesIsoXOne
    (conditionInclusion φ)

theorem boundary_comp_cyclesIso_inv :
    boundary φ ≫ (conditionCyclesIsoXOne φ).inv =
      (ConditionComplex φ).toCycles 0 1 :=
  CochainH1SubobjectConditionProducer.boundary_comp_cyclesIso_inv
    (conditionInclusion φ)

theorem conditionToHomologyReadout_condition :
    (ConditionComplex φ).toCycles 0 1 ≫
        ((conditionCyclesIsoXOne φ).hom ≫ projection φ) = 0 :=
  CochainH1SubobjectConditionProducer.conditionToHomologyReadout_condition
    (conditionInclusion φ)

noncomputable abbrev conditionHomologyCofork :=
  CochainH1SubobjectConditionProducer.conditionHomologyCofork
    (conditionInclusion φ)

noncomputable abbrev conditionHomologyCoforkIsCokernel :=
  CochainH1SubobjectConditionProducer.conditionHomologyCoforkIsCokernel
    (conditionInclusion φ)

noncomputable abbrev conditionH1Iso :
    (ConditionComplex φ).homology 1 ≅ ConditionH1 φ :=
  CochainH1SubobjectConditionProducer.conditionH1Iso (conditionInclusion φ)

@[reassoc]
theorem conditionHomologyπ_H1Iso_hom :
    (ConditionComplex φ).homologyπ 1 ≫ (conditionH1Iso φ).hom =
      (conditionCyclesIsoXOne φ).hom ≫ projection φ :=
  CochainH1SubobjectConditionProducer.conditionHomologyπ_H1Iso_hom
    (conditionInclusion φ)

theorem conditionCyclesMap :
    HomologicalComplex.cyclesMap (conditionToSource φ) 1 =
      (conditionCyclesIsoXOne φ).hom ≫
        pullback.snd (conditionInclusion φ) (C.homologyπ 1) :=
  CochainH1SubobjectConditionProducer.conditionCyclesMap
    (conditionInclusion φ)

theorem conditionH1Map_eq :
    HomologicalComplex.homologyMap (conditionToSource φ) 1 =
      (conditionH1Iso φ).hom ≫ kernel.ι (h1Map φ) :=
  CochainH1SubobjectConditionProducer.conditionH1Map_eq
    (conditionInclusion φ)

noncomputable def kernelH1SubobjectAt :
    CochainH1SubobjectConditionProducer.H1SubobjectAt C where
  carrier := ConditionH1 φ
  inclusion := conditionInclusion φ
  isMono := inferInstance

theorem subobjectConditionComplex_eq :
    CochainH1SubobjectConditionProducer.H1SubobjectAt.ConditionComplex
        (kernelH1SubobjectAt φ) =
      ConditionComplex φ := rfl

theorem subobjectConditionToSource_eq :
    CochainH1SubobjectConditionProducer.H1SubobjectAt.conditionToSource
        (kernelH1SubobjectAt φ) =
      conditionToSource φ := rfl

end


end CochainH1KernelConditionProducer
end SaturationMonoid
