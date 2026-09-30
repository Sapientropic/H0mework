import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone

/-!
# A mapping-cocone atom from an actual mapped boundary

An integral degree-one cycle whose image is an explicit degree-zero boundary
canonically generates a morphism from the integral single complex to the
shifted mapping cocone.  This is a generic cochain-complex construction; no
BSD-specific carrier occurs here.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace CochainMappingCoconeMappedBoundaryAtom

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex

noncomputable section

/-- Canonical extension embedding used by every integral mapped-boundary
atom.  Exposed so downstream homotopy-homology readouts can name the exact
same carrier. -/
abbrev integralExtensionEmbedding := ComplexShape.embeddingUpNat

abbrev e := integralExtensionEmbedding

abbrev IntegralUnit : ModuleCat ℤ := ModuleCat.of ℤ ℤ

abbrev IntegralSingleOne : CochainComplex (ModuleCat ℤ) ℤ :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 1).obj IntegralUnit

/-- The canonical integral scalar arrow selecting one element. -/
noncomputable def elementHom {M : ModuleCat ℤ} (x : M) :
    IntegralUnit ⟶ M :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ M x)

@[simp] theorem elementHom_one (M : ModuleCat ℤ) (x : M) :
    (elementHom x).hom 1 = x := by
  change (inferInstance : Module ℤ M).smul 1 x = x
  exact (int_smul_eq_zsmul (inferInstance : Module ℤ M) 1 x).trans
    (one_zsmul x)

@[simp] theorem elementHom_comp
    {M N : ModuleCat ℤ} (x : M) (f : M ⟶ N) :
    elementHom x ≫ f = elementHom (f.hom x) := by
  ext
  simp [elementHom, LinearMap.toSpanSingleton_apply]

@[simp] theorem elementHom_neg {M : ModuleCat ℤ} (x : M) :
    elementHom (-x) = -elementHom x := by
  ext
  simp [elementHom, LinearMap.toSpanSingleton_apply]

@[simp] theorem elementHom_add {M : ModuleCat ℤ} (x y : M) :
    elementHom (x + y) = elementHom x + elementHom y := by
  ext
  exact smul_add (1 : ℤ) x y

@[simp] theorem elementHom_sub {M : ModuleCat ℤ} (x y : M) :
    elementHom (x - y) = elementHom x - elementHom y := by
  ext
  exact smul_sub (1 : ℤ) x y

@[simp] theorem elementHom_zero (M : ModuleCat ℤ) :
  elementHom (0 : M) = 0 := by
  ext
  simp [elementHom]

noncomputable def extendedCycle
    {K : CochainComplex (ModuleCat ℤ) ℕ}
    (z : K.cycles 1) : (K.extend e).cycles 1 :=
  (K.extendCyclesIso e rfl).inv.hom z

noncomputable def extendedBoundary
    {L : CochainComplex (ModuleCat ℤ) ℕ}
    (q : L.X 0) : (L.extend e).X 0 :=
  (L.extendXIso e rfl).inv.hom q

set_option backward.isDefEq.respectTransparency false in
/-- The mapped-boundary equation survives the canonical extension from
`Nat`-indexed to `Int`-indexed cochain complexes. -/
theorem extendedMappedBoundary
    {K L : CochainComplex (ModuleCat ℤ) ℕ}
    (phi : K ⟶ L) (z : K.cycles 1) (q : L.X 0)
    (mapped : (L.d 0 1).hom q =
      (L.iCycles 1).hom ((cyclesMap phi 1).hom z)) :
    let phiZ := extendMap phi e
    let LZ := L.extend e
    (LZ.d 0 1).hom (extendedBoundary q) =
      (LZ.iCycles 1).hom
        ((cyclesMap phiZ 1).hom (extendedCycle z)) := by
  dsimp only
  let LZ := L.extend e
  let zZ := extendedCycle z
  let qZ := extendedBoundary q
  let mappedZ := (cyclesMap (extendMap phi e) 1).hom zZ
  have zero_eq : e.f (0 : ℕ) = (0 : ℤ) := rfl
  have one_eq : e.f (1 : ℕ) = (1 : ℤ) := rfl
  apply (ModuleCat.mono_iff_injective
    (L.extendXIso e one_eq).hom).mp inferInstance
  have dTransport :
      (L.extendXIso e one_eq).hom.hom ((LZ.d 0 1).hom qZ) =
        (L.d 0 1).hom q := by
    have dEq := ConcreteCategory.congr_hom
      (L.extend_d_eq e zero_eq one_eq) qZ
    have qSource : (L.extendXIso e zero_eq).hom.hom qZ = q := by
      unfold qZ extendedBoundary
      exact Iso.inv_hom_id_apply _ q
    calc
      _ = (L.extendXIso e one_eq).hom.hom
          (((L.extendXIso e zero_eq).hom ≫ L.d 0 1 ≫
            (L.extendXIso e one_eq).inv).hom qZ) :=
        congrArg (L.extendXIso e one_eq).hom.hom dEq
      _ = (L.d 0 1).hom ((L.extendXIso e zero_eq).hom.hom qZ) := by
        simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
      _ = (L.d 0 1).hom q := congrArg (L.d 0 1).hom qSource
  have cycleNaturality := ConcreteCategory.congr_hom
    (extendCyclesIso_hom_naturality phi e one_eq) zZ
  have sourceCycle :
      (K.extendCyclesIso e one_eq).hom.hom zZ = z := by
    unfold zZ extendedCycle
    exact Iso.inv_hom_id_apply _ z
  have cycleNaturality' :
      (L.extendCyclesIso e one_eq).hom.hom mappedZ =
        (cyclesMap phi 1).hom z := by
    simpa only [ConcreteCategory.comp_apply, sourceCycle] using cycleNaturality
  have included := ConcreteCategory.congr_hom
    (L.extendCyclesIso_hom_iCycles e one_eq) mappedZ
  have included' :
      (L.iCycles 1).hom
          ((L.extendCyclesIso e one_eq).hom.hom mappedZ) =
        (L.extendXIso e one_eq).hom.hom
          ((LZ.iCycles 1).hom mappedZ) := by
    simpa only [ConcreteCategory.comp_apply] using included
  calc
    (L.extendXIso e one_eq).hom.hom ((LZ.d 0 1).hom qZ) =
        (L.d 0 1).hom q := dTransport
    _ = (L.iCycles 1).hom ((cyclesMap phi 1).hom z) := mapped
    _ = (L.iCycles 1).hom
        ((L.extendCyclesIso e one_eq).hom.hom mappedZ) := by
      rw [cycleNaturality']
    _ = (L.extendXIso e one_eq).hom.hom
        ((LZ.iCycles 1).hom mappedZ) := included'

/-- The extended cycle as an integral generator arrow in degree one. -/
noncomputable def cycleGenerator
    {K : CochainComplex (ModuleCat ℤ) ℕ}
    (z : K.cycles 1) :
    IntegralUnit ⟶ (K.extend e).X 1 :=
  elementHom (extendedCycle z) ≫ (K.extend e).iCycles 1

/-- The extended boundary as an integral generator arrow in degree zero. -/
noncomputable def boundaryGenerator
    {L : CochainComplex (ModuleCat ℤ) ℕ}
    (q : L.X 0) :
    IntegralUnit ⟶ (L.extend e).X 0 :=
  elementHom (extendedBoundary q)

/-- A genuine degree-zero complex morphism carrying the single generator to
the supplied degree-one cycle. -/
noncomputable def cycleMorphism
    {K : CochainComplex (ModuleCat ℤ) ℕ}
    (z : K.cycles 1) : IntegralSingleOne ⟶ K.extend e :=
  (CochainComplex.HomComplex.Cocycle.fromSingleMk
    (cycleGenerator z) (by norm_num) 2 (by norm_num) (by
      unfold cycleGenerator
      rw [Category.assoc, (K.extend e).iCycles_d 1 2,
        comp_zero])).homOf

/-- The negative boundary cochain supplies the homotopy component required by
the shifted mapping cocone convention. -/
noncomputable def negativeBoundaryCochain
    {L : CochainComplex (ModuleCat ℤ) ℕ}
    (q : L.X 0) :
    CochainComplex.HomComplex.Cochain
      IntegralSingleOne (L.extend e) (-1) :=
  CochainComplex.HomComplex.Cochain.fromSingleMk
    (-boundaryGenerator q) (by norm_num)

set_option backward.isDefEq.respectTransparency false in
/-- Scalar generation preserves the exact mapped-boundary equation. -/
theorem cycleGenerator_mapsToBoundary
    {K L : CochainComplex (ModuleCat ℤ) ℕ}
    (phi : K ⟶ L) (z : K.cycles 1) (q : L.X 0)
    (mapped : (L.d 0 1).hom q =
      (L.iCycles 1).hom ((cyclesMap phi 1).hom z)) :
    cycleGenerator z ≫ (extendMap phi e).f 1 =
      boundaryGenerator q ≫ (L.extend e).d 0 1 := by
  let KZ := K.extend e
  let LZ := L.extend e
  let phiZ := extendMap phi e
  let zZ := extendedCycle z
  let qZ := extendedBoundary q
  have boundaryZ := extendedMappedBoundary phi z q mapped
  change (elementHom zZ ≫ KZ.iCycles 1) ≫ phiZ.f 1 =
    elementHom qZ ≫ LZ.d 0 1
  calc
    (elementHom zZ ≫ KZ.iCycles 1) ≫ phiZ.f 1 =
        elementHom zZ ≫ (cyclesMap phiZ 1 ≫ LZ.iCycles 1) := by
      rw [Category.assoc, cyclesMap_i]
    _ = elementHom
        ((LZ.iCycles 1).hom ((cyclesMap phiZ 1).hom zZ)) := by
      rw [← Category.assoc, elementHom_comp, elementHom_comp]
    _ = elementHom ((LZ.d 0 1).hom qZ) := by
      rw [boundaryZ]
    _ = elementHom qZ ≫ LZ.d 0 1 := by
      rw [elementHom_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The cycle morphism and the negative boundary cochain satisfy exactly the
compatibility equation required by `mappingCocone.lift`. -/
theorem negativeBoundaryCompatibility
    {K L : CochainComplex (ModuleCat ℤ) ℕ}
    (phi : K ⟶ L) (z : K.cycles 1) (q : L.X 0)
    (mapped : (L.d 0 1).hom q =
      (L.iCycles 1).hom ((cyclesMap phi 1).hom z)) :
    CochainComplex.HomComplex.δ (-1) 0
          (negativeBoundaryCochain q) +
        CochainComplex.HomComplex.Cochain.ofHom
          (cycleMorphism z ≫ extendMap phi e) = 0 := by
  let LZ := L.extend e
  let phiZ := extendMap phi e
  have generated := cycleGenerator_mapsToBoundary phi z q mapped
  have alphaCochain :
      CochainComplex.HomComplex.Cochain.ofHom (cycleMorphism z) =
        CochainComplex.HomComplex.Cochain.fromSingleMk
          (cycleGenerator z) (by norm_num) := by
    unfold cycleMorphism
    exact CochainComplex.HomComplex.Cocycle.cochain_ofHom_homOf_eq_coe _
  rw [CochainComplex.HomComplex.Cochain.ofHom_comp, alphaCochain]
  rw [← CochainComplex.HomComplex.Cochain.fromSingleMk_postcomp]
  unfold negativeBoundaryCochain
  rw [CochainComplex.HomComplex.Cochain.δ_fromSingleMk]
  rw [← CochainComplex.HomComplex.Cochain.fromSingleMk_add]
  have generatorSum :
      (-boundaryGenerator q) ≫ LZ.d 0 1 +
          cycleGenerator z ≫ phiZ.f 1 = 0 := by
    rw [Preadditive.neg_comp, generated, neg_add_cancel]
  rw [generatorSum]
  exact CochainComplex.HomComplex.Cochain.fromSingleMk_zero
    IntegralUnit LZ 1 1 0 (by norm_num)

/-- Universal atom generated only from an actual cycle and its calculated
mapped boundary. -/
noncomputable def mappedBoundaryAtom
    {K L : CochainComplex (ModuleCat ℤ) ℕ}
    (phi : K ⟶ L) (z : K.cycles 1) (q : L.X 0)
    (mapped : (L.d 0 1).hom q =
      (L.iCycles 1).hom ((cyclesMap phi 1).hom z)) :
    IntegralSingleOne ⟶
      CochainComplex.mappingCocone (extendMap phi e) :=
  CochainComplex.mappingCocone.lift
    (extendMap phi e)
    (cycleMorphism z)
    (negativeBoundaryCochain q)
    (negativeBoundaryCompatibility phi z q mapped)

@[reassoc (attr := simp)] theorem mappedBoundaryAtom_fst
    {K L : CochainComplex (ModuleCat ℤ) ℕ}
    (phi : K ⟶ L) (z : K.cycles 1) (q : L.X 0)
    (mapped : (L.d 0 1).hom q =
      (L.iCycles 1).hom ((cyclesMap phi 1).hom z)) :
    mappedBoundaryAtom phi z q mapped ≫
        CochainComplex.mappingCocone.fst (extendMap phi e) =
      cycleMorphism z :=
  CochainComplex.mappingCocone.lift_fst
    (extendMap phi e)
    (cycleMorphism z)
    (negativeBoundaryCochain q)
    (negativeBoundaryCompatibility phi z q mapped)

end

end CochainMappingCoconeMappedBoundaryAtom
end SaturationMonoid
