import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Generic H1-subobject condition producer

Given a monomorphism `ι : L ⟶ H¹(C)`, this module pulls `L` back to the
actual degree-one cycles of `C`, constructs the two-term complex
`U = [C⁰ → L ×_{H¹(C)} Z¹(C)]`, and proves

`H¹(U) ≅ L`

with induced map to `H¹(C)` equal to `ι`.  The condition need not first be
presented as the kernel of a cochain map.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace CochainH1SubobjectConditionProducer

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

noncomputable section

set_option maxHeartbeats 1200000

variable {C : CochainComplex (ModuleCat ℤ) ℕ}
variable {L : ModuleCat ℤ} (ι : L ⟶ C.homology 1)

/-- Degree-one cycles whose homology class lies in the supplied subobject. -/
noncomputable abbrev ConditionCycles : ModuleCat ℤ :=
  pullback ι (C.homologyπ 1)

/-- Every actual degree-zero boundary has zero class and hence satisfies the
subobject pullback condition. -/
theorem boundary_condition :
    (0 : C.X 0 ⟶ L) ≫ ι = C.toCycles 0 1 ≫ C.homologyπ 1 := by
  rw [zero_comp, C.toCycles_comp_homologyπ]

/-- Lift of the actual degree-zero boundary into the condition cycles. -/
noncomputable def boundary : C.X 0 ⟶ ConditionCycles ι :=
  pullback.lift 0 (C.toCycles 0 1) (boundary_condition ι)

/-- Projection from condition cycles to the supplied degree-one subobject. -/
noncomputable abbrev projection : ConditionCycles ι ⟶ L :=
  pullback.fst ι (C.homologyπ 1)

@[reassoc]
theorem boundary_projection : boundary ι ≫ projection ι = 0 := by
  rw [boundary]
  apply pullback.lift_fst

/-- Short complex presenting the supplied condition by actual boundaries. -/
noncomputable abbrev conditionShortComplex : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk (boundary ι) (projection ι) (boundary_projection ι)

private theorem pullbackElement_ext
    {X Y Z : ModuleCat.{0} ℤ} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasPullback f g]
    (x y : (pullback f g : ModuleCat ℤ))
    (hfst : pullback.fst f g x = pullback.fst f g y)
    (hsnd : pullback.snd f g x = pullback.snd f g y) :
    x = y := by
  obtain ⟨x₁, x₂, hx, rfl⟩ := Concrete.pullbackMk_surjective f g x
  obtain ⟨y₁, y₂, hy, rfl⟩ := Concrete.pullbackMk_surjective f g y
  simp only [Concrete.pullbackMk_fst] at hfst
  simp only [Concrete.pullbackMk_snd] at hsnd
  subst y₁
  subst y₂
  rfl

/-- The actual-boundary presentation of the pulled-back condition cycles is
exact. -/
theorem boundary_exact : (conditionShortComplex ι).Exact := by
  let B : ShortComplex (ModuleCat ℤ) :=
    ShortComplex.mk (C.toCycles 0 1) (C.homologyπ 1)
      (C.toCycles_comp_homologyπ 0 1)
  have hB : B.Exact :=
    B.exact_of_g_is_cokernel (C.homologyIsCokernel 0 1 (by simp))
  rw [CategoryTheory.ShortComplex.moduleCat_exact_iff]
  change ∀ x : ConditionCycles ι,
    pullback.fst ι (C.homologyπ 1) x = 0 →
      ∃ y : C.X 0, boundary ι y = x
  intro x hx
  have hcondition := ConcreteCategory.congr_hom
    (show
      pullback.fst ι (C.homologyπ 1) ≫ ι =
        pullback.snd ι (C.homologyπ 1) ≫ C.homologyπ 1
      from pullback.condition) x
  have hcondition' :
      ι (pullback.fst ι (C.homologyπ 1) x) =
        C.homologyπ 1 (pullback.snd ι (C.homologyπ 1) x) := by
    simpa only [ConcreteCategory.comp_apply] using hcondition
  have hz :
      C.homologyπ 1 (pullback.snd ι (C.homologyπ 1) x) = 0 := by
    rw [← hcondition', hx, map_zero]
  obtain ⟨y, hy⟩ :=
    (CategoryTheory.ShortComplex.moduleCat_exact_iff B).mp hB
      (pullback.snd ι (C.homologyπ 1) x) hz
  refine ⟨y, ?_⟩
  apply pullbackElement_ext ι (C.homologyπ 1)
  · have hfstlift := ConcreteCategory.congr_hom
      (pullback.lift_fst (0 : C.X 0 ⟶ L) (C.toCycles 0 1)
        (boundary_condition ι)) y
    change pullback.fst ι (C.homologyπ 1) (boundary ι y) = 0 at hfstlift
    exact hfstlift.trans hx.symm
  · have hsndlift := ConcreteCategory.congr_hom
      (pullback.lift_snd (0 : C.X 0 ⟶ L) (C.toCycles 0 1)
        (boundary_condition ι)) y
    change pullback.snd ι (C.homologyπ 1) (boundary ι y) =
      C.toCycles 0 1 y at hsndlift
    exact hsndlift.trans hy

/-- The condition projection is the cokernel of the lifted boundary. -/
noncomputable def projectionIsCokernel :
    IsColimit (CokernelCofork.ofπ
      (f := boundary ι) (projection ι) (boundary_projection ι)) := by
  letI : Epi (C.homologyπ 1) := inferInstance
  letI : Epi (pullback.fst ι (C.homologyπ 1)) := inferInstance
  letI : Epi (conditionShortComplex ι).g := by
    change Epi (pullback.fst ι (C.homologyπ 1))
    infer_instance
  convert (boundary_exact ι).gIsCokernel using 1

private noncomputable abbrev conditionObject : ℕ → ModuleCat ℤ
  | 0 => C.X 0
  | 1 => ConditionCycles ι
  | _ + 2 => 0

private noncomputable abbrev conditionDifferential :
    ∀ i : ℕ, conditionObject ι i ⟶ conditionObject ι (i + 1)
  | 0 => boundary ι
  | _ + 1 => 0

private theorem conditionDifferential_sq (i : ℕ) :
    conditionDifferential ι i ≫ conditionDifferential ι (i + 1) = 0 := by
  match i with
  | 0 => simp [conditionDifferential]
  | _ + 1 => simp [conditionDifferential]

/-- The canonical two-term condition complex. -/
noncomputable abbrev ConditionComplex : CochainComplex (ModuleCat ℤ) ℕ :=
  CochainComplex.of (conditionObject ι) (conditionDifferential ι)
    (conditionDifferential_sq ι)

@[simp]
theorem conditionComplex_X_zero : (ConditionComplex ι).X 0 = C.X 0 := rfl

@[simp]
theorem conditionComplex_X_one :
    (ConditionComplex ι).X 1 = ConditionCycles ι := rfl

@[simp]
theorem conditionComplex_d_zero_one :
    (ConditionComplex ι).d 0 1 = boundary ι := by
  change CochainComplex.of.d
    (conditionObject ι) (conditionDifferential ι) 0 1 = _
  simpa using CochainComplex.of_d
    (conditionObject ι) (conditionDifferential ι) 0

@[simp]
theorem conditionComplex_d_one_two :
    (ConditionComplex ι).d 1 2 = 0 := by
  change CochainComplex.of.d
    (conditionObject ι) (conditionDifferential ι) 1 2 = _
  simpa using CochainComplex.of_d
    (conditionObject ι) (conditionDifferential ι) 1

@[reassoc]
theorem boundary_snd :
    boundary ι ≫ pullback.snd ι (C.homologyπ 1) = C.toCycles 0 1 := by
  rw [boundary]
  apply pullback.lift_snd

/-- Degreewise map from the condition complex into its source complex. -/
noncomputable def conditionToSourceDegree :
    ∀ i : ℕ, (ConditionComplex ι).X i ⟶ C.X i
  | 0 => 𝟙 _
  | 1 => pullback.snd ι (C.homologyπ 1) ≫ C.iCycles 1
  | _ + 2 => 0

theorem conditionToSourceDegree_comm (i : ℕ) :
    conditionToSourceDegree ι i ≫ C.d i (i + 1) =
      (ConditionComplex ι).d i (i + 1) ≫
        conditionToSourceDegree ι (i + 1) := by
  match i with
  | 0 =>
      change (𝟙 (C.X 0)) ≫ C.d 0 1 =
        boundary ι ≫ (pullback.snd ι (C.homologyπ 1) ≫ C.iCycles 1)
      rw [Category.id_comp, ← Category.assoc, boundary_snd, C.toCycles_i]
  | 1 =>
      change (pullback.snd ι (C.homologyπ 1) ≫ C.iCycles 1) ≫
        C.d 1 2 = 0
      rw [Category.assoc, C.iCycles_d, comp_zero]
  | i + 2 =>
      change (0 : (ConditionComplex ι).X (i + 2) ⟶ C.X (i + 2)) ≫
        C.d (i + 2) (i + 2 + 1) = 0
      rw [zero_comp]

/-- Canonical chain map from the condition complex into `C`. -/
noncomputable def conditionToSource : ConditionComplex ι ⟶ C where
  f := conditionToSourceDegree ι
  comm' i j hij := by
    subst j
    exact conditionToSourceDegree_comm ι i

/-- Degree-one cycles of the condition complex are its pullback term. -/
noncomputable def conditionCyclesIsoXOne :
    (ConditionComplex ι).cycles 1 ≅ ConditionCycles ι :=
  (ConditionComplex ι).iCyclesIso 1 2 (by simp)
    (conditionComplex_d_one_two ι)

theorem boundary_comp_cyclesIso_inv :
    boundary ι ≫ (conditionCyclesIsoXOne ι).inv =
      (ConditionComplex ι).toCycles 0 1 := by
  let U := ConditionComplex ι
  let e := conditionCyclesIsoXOne ι
  apply (cancel_mono e.hom).1
  rw [Category.assoc, e.inv_hom_id, Category.comp_id]
  change boundary ι = U.toCycles 0 1 ≫ U.iCycles 1
  rw [U.toCycles_i, conditionComplex_d_zero_one]

theorem conditionToHomologyReadout_condition :
    (ConditionComplex ι).toCycles 0 1 ≫
      ((conditionCyclesIsoXOne ι).hom ≫ projection ι) = 0 := by
  rw [← Category.assoc, ← boundary_comp_cyclesIso_inv ι]
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id_assoc]
  exact boundary_projection ι

/-- Cokernel presentation of the condition object by the generated complex. -/
noncomputable def conditionHomologyCofork :
    CokernelCofork ((ConditionComplex ι).toCycles 0 1) :=
  CokernelCofork.ofπ
    ((conditionCyclesIsoXOne ι).hom ≫ projection ι)
    (conditionToHomologyReadout_condition ι)

noncomputable def conditionHomologyCoforkIsCokernel :
    IsColimit (conditionHomologyCofork ι) := by
  let e := conditionCyclesIsoXOne ι
  let hproj := projectionIsCokernel ι
  letI : Epi (C.homologyπ 1) := inferInstance
  letI : Epi (projection ι) := inferInstance
  letI : Epi e.hom := inferInstance
  letI : Epi (e.hom ≫ projection ι) := inferInstance
  letI : Epi (conditionHomologyCofork ι).π := by
    change Epi (e.hom ≫ projection ι)
    infer_instance
  apply CokernelCofork.IsColimit.ofπ'
    (conditionHomologyCofork ι).π
    (conditionHomologyCofork ι).condition
  intro A k hk
  let k' : ConditionCycles ι ⟶ A := e.inv ≫ k
  have hk' : boundary ι ≫ k' = 0 := by
    rw [← Category.assoc, boundary_comp_cyclesIso_inv ι, hk]
  let l : L ⟶ A :=
    hproj.desc (CokernelCofork.ofπ k' hk')
  refine ⟨l, ?_⟩
  have hl : projection ι ≫ l = k' := by
    dsimp only [l]
    change (CokernelCofork.ofπ
        (projection ι) (boundary_projection ι)).π ≫
      hproj.desc (CokernelCofork.ofπ k' hk') =
        (CokernelCofork.ofπ k' hk').π
    exact Cofork.IsColimit.π_desc hproj
  calc
    (e.hom ≫ projection ι) ≫ l =
        e.hom ≫ (projection ι ≫ l) := Category.assoc _ _ _
    _ = e.hom ≫ k' := by rw [hl]
    _ = e.hom ≫ (e.inv ≫ k) := rfl
    _ = k := by rw [← Category.assoc, e.hom_inv_id, Category.id_comp]

/-- Canonical identification `H¹(U) ≅ L`. -/
noncomputable def conditionH1Iso : (ConditionComplex ι).homology 1 ≅ L :=
  IsColimit.coconePointUniqueUpToIso
    ((ConditionComplex ι).homologyIsCokernel 0 1 (by simp))
    (conditionHomologyCoforkIsCokernel ι)

@[reassoc]
theorem conditionHomologyπ_H1Iso_hom :
    (ConditionComplex ι).homologyπ 1 ≫ (conditionH1Iso ι).hom =
      (conditionCyclesIsoXOne ι).hom ≫ projection ι := by
  simpa [conditionH1Iso, conditionHomologyCofork] using
    IsColimit.comp_coconePointUniqueUpToIso_hom
      ((ConditionComplex ι).homologyIsCokernel 0 1 (by simp))
      (conditionHomologyCoforkIsCokernel ι)
      WalkingParallelPair.one

theorem conditionCyclesMap :
    HomologicalComplex.cyclesMap (conditionToSource ι) 1 =
      (conditionCyclesIsoXOne ι).hom ≫
        pullback.snd ι (C.homologyπ 1) := by
  let U := ConditionComplex ι
  let e := conditionCyclesIsoXOne ι
  rw [← cancel_mono (C.iCycles 1)]
  rw [HomologicalComplex.cyclesMap_i]
  change U.iCycles 1 ≫
      (pullback.snd ι (C.homologyπ 1) ≫ C.iCycles 1) =
    (e.hom ≫ pullback.snd ι (C.homologyπ 1)) ≫ C.iCycles 1
  rw [Category.assoc]
  rfl

/-- Under the canonical `H¹(U)` identification, the map back into `H¹(C)`
is exactly the supplied subobject inclusion. -/
theorem conditionH1Map_eq :
    HomologicalComplex.homologyMap (conditionToSource ι) 1 =
      (conditionH1Iso ι).hom ≫ ι := by
  let U := ConditionComplex ι
  rw [← cancel_epi (U.homologyπ 1)]
  rw [HomologicalComplex.homologyπ_naturality]
  rw [conditionHomologyπ_H1Iso_hom_assoc]
  rw [conditionCyclesMap]
  simp only [Category.assoc]
  rw [pullback.condition]

/-! ## Canonical subobject-indexed public mouth -/

/-- A degree-one condition as an actual subobject of `H¹(C)`.  The raw map
construction above is slightly more general; this carrier is the authority-
free mathematical mouth used by arithmetic domains. -/
structure H1SubobjectAt (C : CochainComplex (ModuleCat ℤ) ℕ) where
  carrier : ModuleCat ℤ
  inclusion : carrier ⟶ C.homology 1
  isMono : Mono inclusion

instance (condition : H1SubobjectAt C) : Mono condition.inclusion :=
  condition.isMono

namespace H1SubobjectAt

variable (condition : H1SubobjectAt C)

/-- The condition cycles generated by this exact subobject. -/
noncomputable abbrev ConditionCycles : ModuleCat ℤ :=
  CochainH1SubobjectConditionProducer.ConditionCycles condition.inclusion

/-- The canonical two-term complex generated by this exact subobject. -/
noncomputable abbrev ConditionComplex : CochainComplex (ModuleCat ℤ) ℕ :=
  CochainH1SubobjectConditionProducer.ConditionComplex condition.inclusion

/-- The canonical chain map from the condition complex into `C`. -/
noncomputable abbrev conditionToSource : ConditionComplex condition ⟶ C :=
  CochainH1SubobjectConditionProducer.conditionToSource condition.inclusion

/-- Canonical identification of generated degree-one homology with the
subobject carrier. -/
noncomputable def conditionH1Iso :
    (ConditionComplex condition).homology 1 ≅ condition.carrier :=
  CochainH1SubobjectConditionProducer.conditionH1Iso condition.inclusion

/-- The generated map back to `H¹(C)` is exactly the installed subobject
inclusion. -/
theorem conditionH1Map_eq :
    HomologicalComplex.homologyMap (conditionToSource condition) 1 =
      (condition.conditionH1Iso).hom ≫ condition.inclusion :=
  CochainH1SubobjectConditionProducer.conditionH1Map_eq condition.inclusion

end H1SubobjectAt

end

end CochainH1SubobjectConditionProducer
end SaturationMonoid
