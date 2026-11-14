import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import H0mework.Versions.R21a4a7ce.ReleaseMaterials.SaturationMonoid.UniversalBSDGeometricGalois

/-!
# Universal BSD real-place full-point coefficient

For every rational elliptic curve, this module generates the source-independent continuous
homomorphism `G_R → G_Q`, the chosen `Qbar → Rbar` embedding, the actual jointly continuous
`E(Rbar)` point representation, and the equivariant global-to-real coefficient morphism.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace UniversalBSDAllPlaceSelmerComplex

open CategoryTheory
open UniversalBSDGeometricGalois

noncomputable section

set_option linter.style.haveILetI false
/-! ## Source-independent archimedean Galois infrastructure -/

/-- Chosen algebraic closure of `R`. -/
abbrev RealAlgebraicClosure := AlgebraicClosure ℝ

local instance realGlobalClosureDecidableEq :
    DecidableEq (AlgebraicClosure ℚ) :=
  Classical.decEq _

noncomputable instance realClosureDecidableEq :
    DecidableEq RealAlgebraicClosure :=
  Classical.decEq _

local instance realGlobalClosureIsAlgebraic :
    Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ

local instance realGlobalIsAlgClosure :
    IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
  ⟨AlgebraicClosure.isAlgClosed ℚ, realGlobalClosureIsAlgebraic⟩

local instance realGlobalClosureNormal :
    Normal ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

local instance realClosureIsAlgebraic :
    Algebra.IsAlgebraic ℝ RealAlgebraicClosure :=
  AlgebraicClosure.isAlgebraic ℝ

local instance realIsAlgClosure :
    IsAlgClosure ℝ RealAlgebraicClosure :=
  ⟨AlgebraicClosure.isAlgClosed ℝ, realClosureIsAlgebraic⟩

/-- Source-independent embedding `Qbar → Rbar`. -/
noncomputable def globalClosureToRealEmbedding :
    AlgebraicClosure ℚ →ₐ[ℚ] RealAlgebraicClosure :=
  IsAlgClosed.lift

abbrev GlobalClosureRealImage :
    IntermediateField ℚ RealAlgebraicClosure :=
  globalClosureToRealEmbedding.fieldRange

noncomputable def globalClosureEquivRealImage :
    AlgebraicClosure ℚ ≃ₐ[ℚ] GlobalClosureRealImage := by
  let f := globalClosureToRealEmbedding
  exact (AlgEquiv.ofInjectiveField f).trans
    (Subalgebra.equivOfEq f.range f.fieldRange.toSubalgebra
      (AlgHom.fieldRange_toSubalgebra f).symm)

local instance globalClosureRealImageNormal :
    Normal ℚ GlobalClosureRealImage :=
  Normal.of_algEquiv globalClosureEquivRealImage

noncomputable def realToImageGaloisMonoidHom :
    Field.absoluteGaloisGroup ℝ →*
      (GlobalClosureRealImage ≃ₐ[ℚ] GlobalClosureRealImage) :=
  (AlgEquiv.restrictNormalHom GlobalClosureRealImage).comp
    (AlgEquiv.restrictScalarsHom ℚ)

noncomputable def realToGlobalGaloisMonoidHom :
    Field.absoluteGaloisGroup ℝ →* Field.absoluteGaloisGroup ℚ :=
  (AlgEquiv.autCongr globalClosureEquivRealImage).symm.toMonoidHom.comp
    realToImageGaloisMonoidHom

private theorem realRestrictScalarsHom_continuous :
    Continuous (AlgEquiv.restrictScalarsHom ℚ :
      (RealAlgebraicClosure ≃ₐ[ℝ] RealAlgebraicClosure) →*
      (RealAlgebraicClosure ≃ₐ[ℚ] RealAlgebraicClosure)) := by
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr ?_)
  intro N hN
  rw [map_one, krullTopology_mem_nhds_one_iff] at hN
  obtain ⟨E, hEfin, hEN⟩ := hN
  letI : FiniteDimensional ℚ E := hEfin
  let b := Module.Basis.ofVectorSpace ℚ E
  letI : Fintype (Module.Basis.ofVectorSpaceIndex ℚ E) :=
    FiniteDimensional.fintypeBasisIndex b
  let U : Set (RealAlgebraicClosure ≃ₐ[ℝ] RealAlgebraicClosure) :=
    ⋂ i, (MulAction.stabilizer
      (RealAlgebraicClosure ≃ₐ[ℝ] RealAlgebraicClosure)
      ((b i : E) : RealAlgebraicClosure) : Set _)
  have hUopen : IsOpen U := by
    apply isOpen_iInter_of_finite
    intro i
    exact stabilizer_isOpen_of_isIntegral
      ((b i : E) : RealAlgebraicClosure)
  apply mem_nhds_iff.mpr
  refine ⟨U, ?_, hUopen, ?_⟩
  · intro sigma hsigma
    apply hEN
    change (AlgEquiv.restrictScalarsHom ℚ) sigma ∈ E.fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    let yE : E := ⟨y, hy⟩
    suffices hlin :
        (sigma.restrictScalars ℚ).toLinearMap.comp E.val.toLinearMap =
          E.val.toLinearMap by
      exact DFunLike.congr_fun hlin yE
    apply b.ext
    intro i
    exact Set.mem_iInter.mp hsigma i
  · simp [U]

universe u v w

private theorem realAutCongr_continuous
    {k : Type u} {A : Type v} {B : Type w}
    [Field k] [Field A] [Field B]
    [Algebra k A] [Algebra k B]
    [Algebra.IsIntegral k A] [Algebra.IsIntegral k B]
    (e : A ≃ₐ[k] B) :
    Continuous (AlgEquiv.autCongr e) := by
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr ?_)
  intro N hN
  rw [map_one, krullTopology_mem_nhds_one_iff] at hN
  obtain ⟨E, hEfin, hEN⟩ := hN
  letI : FiniteDimensional k E := hEfin
  let b := Module.Basis.ofVectorSpace k E
  letI : Fintype (Module.Basis.ofVectorSpaceIndex k E) :=
    FiniteDimensional.fintypeBasisIndex b
  let U : Set (A ≃ₐ[k] A) :=
    ⋂ i, (MulAction.stabilizer (A ≃ₐ[k] A)
      (e.symm ((b i : E) : B)) : Set (A ≃ₐ[k] A))
  have hUopen : IsOpen U := by
    apply isOpen_iInter_of_finite
    intro i
    exact stabilizer_isOpen_of_isIntegral (e.symm ((b i : E) : B))
  apply mem_nhds_iff.mpr
  refine ⟨U, ?_, hUopen, ?_⟩
  · intro sigma hsigma
    apply hEN
    change (AlgEquiv.autCongr e) sigma ∈ E.fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    let yE : E := ⟨y, hy⟩
    suffices hlin :
        ((AlgEquiv.autCongr e) sigma).toLinearMap.comp E.val.toLinearMap =
          E.val.toLinearMap by
      exact DFunLike.congr_fun hlin yE
    apply b.ext
    intro i
    have hi := Set.mem_iInter.mp hsigma i
    change sigma (e.symm ((b i : E) : B)) =
      e.symm ((b i : E) : B) at hi
    change e (sigma (e.symm ((b i : E) : B))) = ((b i : E) : B)
    rw [hi, e.apply_symm_apply]
  · simp [U]

private theorem realAutCongr_symm_continuous
    {k : Type u} {A : Type v} {B : Type w}
    [Field k] [Field A] [Field B]
    [Algebra k A] [Algebra k B]
    [Algebra.IsIntegral k A] [Algebra.IsIntegral k B]
    (e : A ≃ₐ[k] B) :
    Continuous (AlgEquiv.autCongr e).symm := by
  rw [AlgEquiv.autCongr_symm]
  exact realAutCongr_continuous e.symm

theorem realToGlobalGaloisMonoidHom_continuous :
    Continuous realToGlobalGaloisMonoidHom := by
  have hres : Continuous
      (AlgEquiv.restrictNormalHom GlobalClosureRealImage :
        (RealAlgebraicClosure ≃ₐ[ℚ] RealAlgebraicClosure) →*
        (GlobalClosureRealImage ≃ₐ[ℚ] GlobalClosureRealImage)) :=
    @InfiniteGalois.restrictNormalHom_continuous
      ℚ RealAlgebraicClosure _ _ _
      GlobalClosureRealImage globalClosureRealImageNormal
  exact (realAutCongr_symm_continuous globalClosureEquivRealImage).comp
    (hres.comp realRestrictScalarsHom_continuous)

/-- Source-independent continuous archimedean decomposition homomorphism. -/
noncomputable def realToGlobalGaloisHom :
    Field.absoluteGaloisGroup ℝ →ₜ* Field.absoluteGaloisGroup ℚ where
  toMonoidHom := realToGlobalGaloisMonoidHom
  continuous_toFun := realToGlobalGaloisMonoidHom_continuous

theorem globalClosureToRealEmbedding_galois_commutes
    (sigma : Field.absoluteGaloisGroup ℝ) (x : AlgebraicClosure ℚ) :
    globalClosureToRealEmbedding
        ((realToGlobalGaloisHom sigma).toAlgHom x) =
      sigma.toAlgHom (globalClosureToRealEmbedding x) := by
  let e := globalClosureEquivRealImage
  let tau := realToImageGaloisMonoidHom sigma
  have he_val (z : AlgebraicClosure ℚ) :
      ((e z : GlobalClosureRealImage) : RealAlgebraicClosure) =
        globalClosureToRealEmbedding z := by
    rfl
  have he_symm_val (z : GlobalClosureRealImage) :
      globalClosureToRealEmbedding (e.symm z) = z.1 := by
    calc
      globalClosureToRealEmbedding (e.symm z) =
          (e (e.symm z)).1 := (he_val (e.symm z)).symm
      _ = z.1 := congrArg Subtype.val (e.apply_symm_apply z)
  have hglobal :
      (realToGlobalGaloisHom sigma).toAlgHom x =
        e.symm (tau (e x)) := by
    rfl
  rw [hglobal, he_symm_val]
  have htau : (tau (e x)).1 = sigma.toAlgHom (e x).1 := by
    have haction :
        realToImageGaloisMonoidHom sigma =
          (AlgEquiv.restrictNormalHom GlobalClosureRealImage)
            (sigma.restrictScalars ℚ) := by
      rfl
    rw [show tau = realToImageGaloisMonoidHom sigma from rfl, haction]
    exact @AlgEquiv.restrictNormalHom_apply
      ℚ inferInstance RealAlgebraicClosure inferInstance inferInstance
      GlobalClosureRealImage globalClosureRealImageNormal
      (sigma.restrictScalars ℚ) (e x)
  rw [htau, he_val]

/-! ## Actual real geometric-point representation -/

/-- The source curve over the chosen algebraic closure of `R`. -/
abbrev RealGeometricCurve (source : RationalEllipticCurveSource) :
    WeierstrassCurve RealAlgebraicClosure :=
  source.curve.baseChange RealAlgebraicClosure

instance realGeometricCurve_isElliptic
    (source : RationalEllipticCurveSource) :
    (RealGeometricCurve source).IsElliptic := by
  unfold RealGeometricCurve WeierstrassCurve.baseChange
  infer_instance

/-- Actual real geometric points `E(Rbar)`. -/
abbrev RealGeometricPoints (source : RationalEllipticCurveSource) :=
  (RealGeometricCurve source).toAffine.Point

local instance realClosureGaloisSMul :
    SMul (Field.absoluteGaloisGroup ℝ) RealAlgebraicClosure :=
  ⟨fun sigma x ↦ sigma.toAlgHom x⟩

local instance realClosureGaloisMulAction :
    MulAction (Field.absoluteGaloisGroup ℝ) RealAlgebraicClosure where
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

noncomputable def realGeometricPointGaloisMap
    (source : RationalEllipticCurveSource)
    (sigma : Field.absoluteGaloisGroup ℝ) :
    RealGeometricPoints source →+ RealGeometricPoints source :=
  WeierstrassCurve.Affine.Point.map
    (W' := source.curve) (sigma.restrictScalars ℚ).toAlgHom

theorem realGeometricPointGaloisMap_comp
    (source : RationalEllipticCurveSource)
    (sigma tau : Field.absoluteGaloisGroup ℝ)
    (point : RealGeometricPoints source) :
    realGeometricPointGaloisMap source (sigma * tau) point =
      realGeometricPointGaloisMap source sigma
        (realGeometricPointGaloisMap source tau point) := by
  simp only [realGeometricPointGaloisMap]
  rw [WeierstrassCurve.Affine.Point.map_map]
  rfl

/-- Public real-point Galois action. -/
instance realGeometricPointsGaloisSMul
    (source : RationalEllipticCurveSource) :
    SMul (Field.absoluteGaloisGroup ℝ) (RealGeometricPoints source) :=
  ⟨fun sigma point ↦ realGeometricPointGaloisMap source sigma point⟩

/-- Public real-point Galois multiplication law. -/
instance realGeometricPointsGaloisMulAction
    (source : RationalEllipticCurveSource) :
    MulAction (Field.absoluteGaloisGroup ℝ) (RealGeometricPoints source) where
  one_smul point := by
    rcases point with (_ | ⟨x, y, hpoint⟩) <;> rfl
  mul_smul sigma tau point :=
    realGeometricPointGaloisMap_comp source sigma tau point

/-- Public discrete topology of the real geometric coefficient. -/
instance realGeometricPointsTopology
    (source : RationalEllipticCurveSource) :
    TopologicalSpace (RealGeometricPoints source) :=
  ⊥

instance realGeometricPointsDiscreteTopology
    (source : RationalEllipticCurveSource) :
    DiscreteTopology (RealGeometricPoints source) :=
  ⟨rfl⟩

/-- Public joint continuity of the integral coefficient action. -/
instance realGeometricPointsContinuousIntSMul
    (source : RationalEllipticCurveSource) :
    ContinuousSMul ℤ (RealGeometricPoints source) :=
  ⟨continuous_of_discreteTopology⟩

theorem realGeometricPoints_stabilizer_isOpen
    (source : RationalEllipticCurveSource)
    (point : RealGeometricPoints source) :
    IsOpen
      (MulAction.stabilizer (Field.absoluteGaloisGroup ℝ) point :
        Set (Field.absoluteGaloisGroup ℝ)) := by
  rcases point with (_ | ⟨x, y, hpoint⟩)
  · have htop :
        (MulAction.stabilizer (Field.absoluteGaloisGroup ℝ)
          (WeierstrassCurve.Affine.Point.zero : RealGeometricPoints source) :
          Set (Field.absoluteGaloisGroup ℝ)) = Set.univ := by
      ext sigma
      simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff,
        Set.mem_univ, iff_true]
      rfl
    rw [htop]
    exact isOpen_univ
  · have hx : IsOpen
        (MulAction.stabilizer (Field.absoluteGaloisGroup ℝ) x :
          Set (Field.absoluteGaloisGroup ℝ)) :=
      stabilizer_isOpen_of_isIntegral x
    have hy : IsOpen
        (MulAction.stabilizer (Field.absoluteGaloisGroup ℝ) y :
          Set (Field.absoluteGaloisGroup ℝ)) :=
      stabilizer_isOpen_of_isIntegral y
    have hcoordinates :
        (MulAction.stabilizer (Field.absoluteGaloisGroup ℝ)
          (WeierstrassCurve.Affine.Point.some x y hpoint) :
          Set (Field.absoluteGaloisGroup ℝ)) =
        (MulAction.stabilizer (Field.absoluteGaloisGroup ℝ) x : Set _) ∩
          (MulAction.stabilizer (Field.absoluteGaloisGroup ℝ) y : Set _) := by
      ext sigma
      simp only [Set.mem_inter_iff, SetLike.mem_coe,
        MulAction.mem_stabilizer_iff]
      change
        WeierstrassCurve.Affine.Point.some (sigma.toAlgHom x)
            (sigma.toAlgHom y) _ =
            WeierstrassCurve.Affine.Point.some x y hpoint ↔
          sigma.toAlgHom x = x ∧ sigma.toAlgHom y = y
      constructor
      · intro h
        exact WeierstrassCurve.Affine.Point.some.inj h
      · rintro ⟨hx, hy⟩
        exact Eq.mpr
          (WeierstrassCurve.Affine.Point.some.injEq
            (sigma.toAlgHom x) (sigma.toAlgHom y) _ x y hpoint)
          ⟨hx, hy⟩
    rw [hcoordinates]
    exact hx.inter hy

/-- Public joint continuity of the real absolute-Galois action. -/
instance realGeometricPointsContinuousGaloisSMul
    (source : RationalEllipticCurveSource) :
    ContinuousSMul (Field.absoluteGaloisGroup ℝ)
      (RealGeometricPoints source) :=
  continuousSMul_iff_stabilizer_isOpen.mpr
    (realGeometricPoints_stabilizer_isOpen source)

noncomputable def realGeometricPointGaloisContinuousLinearMap
    (source : RationalEllipticCurveSource)
    (sigma : Field.absoluteGaloisGroup ℝ) :
    RealGeometricPoints source →L[ℤ] RealGeometricPoints source :=
  ContinuousLinearMap.mk
    (realGeometricPointGaloisMap source sigma).toIntLinearMap
    continuous_of_discreteTopology

noncomputable def realGeometricPointGaloisMonoidHom
    (source : RationalEllipticCurveSource) :
    Field.absoluteGaloisGroup ℝ →*
      (RealGeometricPoints source →L[ℤ] RealGeometricPoints source) where
  toFun := realGeometricPointGaloisContinuousLinearMap source
  map_one' := by
    ext point
    rcases point with (_ | ⟨x, y, h⟩) <;> rfl
  map_mul' sigma tau := by
    ext point
    exact realGeometricPointGaloisMap_comp source sigma tau point

/-- Actual real full-point Galois representation. -/
noncomputable def realGeometricPointTopRep
    (source : RationalEllipticCurveSource) :
    TopRep ℤ (Field.absoluteGaloisGroup ℝ) :=
  TopRep.of (ContRepresentation.ofMonoidHom
    (realGeometricPointGaloisMonoidHom source))

@[simp]
theorem realGeometricPointTopRep_rho_apply
    (source : RationalEllipticCurveSource)
    (sigma : Field.absoluteGaloisGroup ℝ)
    (point : RealGeometricPoints source) :
    (realGeometricPointTopRep source).ρ sigma point = sigma • point :=
  rfl

/-- The chosen embedding `Qbar → Rbar` applied to actual geometric points. -/
noncomputable def globalGeometricPointToReal
    (source : RationalEllipticCurveSource) :
    GeometricPoints source →+ RealGeometricPoints source :=
  WeierstrassCurve.Affine.Point.map
    (W' := source.curve) globalClosureToRealEmbedding

theorem globalGeometricPointToReal_galois_commutes
    (source : RationalEllipticCurveSource)
    (sigma : Field.absoluteGaloisGroup ℝ)
    (point : GeometricPoints source) :
    globalGeometricPointToReal source
        (geometricPointGaloisMap source
          (realToGlobalGaloisHom sigma) point) =
      realGeometricPointGaloisMap source sigma
        (globalGeometricPointToReal source point) := by
  rcases point with (_ | ⟨x, y, hpoint⟩)
  · rfl
  · change WeierstrassCurve.Affine.Point.some
        (globalClosureToRealEmbedding
          ((realToGlobalGaloisHom sigma).toAlgHom x))
        (globalClosureToRealEmbedding
          ((realToGlobalGaloisHom sigma).toAlgHom y)) _ =
      WeierstrassCurve.Affine.Point.some
        (sigma.toAlgHom (globalClosureToRealEmbedding x))
        (sigma.toAlgHom (globalClosureToRealEmbedding y)) _
    congr 1
    · exact globalClosureToRealEmbedding_galois_commutes sigma x
    · exact globalClosureToRealEmbedding_galois_commutes sigma y

noncomputable def globalGeometricPointToRealContinuousLinearMap
    (source : RationalEllipticCurveSource) :
    GeometricPoints source →L[ℤ] RealGeometricPoints source :=
  ContinuousLinearMap.mk
    (globalGeometricPointToReal source).toIntLinearMap
    continuous_of_discreteTopology

/-- Actual equivariant coefficient morphism at the real place. -/
noncomputable def globalGeometricPointToRealTopRepHom
    (source : RationalEllipticCurveSource) :
    TopRep.res realToGlobalGaloisHom.toMonoidHom
        (geometricPointTopRep source) ⟶
      realGeometricPointTopRep source :=
  TopRep.ofHom ⟨
    globalGeometricPointToRealContinuousLinearMap source,
    by
      intro sigma
      ext point
      exact globalGeometricPointToReal_galois_commutes source sigma point
  ⟩

end

end UniversalBSDAllPlaceSelmerComplex
end SaturationMonoid
