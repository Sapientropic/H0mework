import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import H0mework.Versions.R21a4a7ce.ReleaseMaterials.SaturationMonoid.UniversalBSDGeometricGalois

/-!
# Universal BSD finite-place full-point coefficient

For every rational elliptic curve and finite rational prime, this module generates the local
field and algebraic closure, the continuous decomposition homomorphism `G_{Q_q} → G_Q`, the
actual local geometric-point representation, and the equivariant global-to-local point map.
No fixed-CM, torsion, Selmer, Sha, rank, or localization-kernel premise is used.
-/
set_option autoImplicit false

namespace SaturationMonoid
namespace UniversalBSDFinitePlaceFullPoint

open CategoryTheory
open UniversalBSDGeometricGalois

noncomputable section

set_option linter.style.haveILetI false

noncomputable instance finitePrimeFact (q : Nat.Primes) :
    Fact (Nat.Prime (q : Nat)) :=
  ⟨q.property⟩

/-- The actual `q`-adic local field. -/
abbrev FiniteLocalField (q : Nat.Primes) :=
  Padic (q : Nat)

/-- A chosen algebraic closure of the actual local field. -/
abbrev FiniteAlgebraicClosure (q : Nat.Primes) :=
  AlgebraicClosure (FiniteLocalField q)

local instance globalClosureIsAlgebraic :
    Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ

local instance globalIsAlgClosure :
    IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
  ⟨AlgebraicClosure.isAlgClosed ℚ, globalClosureIsAlgebraic⟩

local instance globalClosureNormal :
    Normal ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

noncomputable instance finiteLocalFieldDecidableEq (q : Nat.Primes) :
    DecidableEq (FiniteLocalField q) :=
  Classical.decEq _

local instance globalClosureDecidableEq :
    DecidableEq (AlgebraicClosure ℚ) :=
  Classical.decEq _

noncomputable instance finiteClosureDecidableEq (q : Nat.Primes) :
    DecidableEq (FiniteAlgebraicClosure q) :=
  Classical.decEq _

local instance finiteClosureIsAlgebraic (q : Nat.Primes) :
    Algebra.IsAlgebraic (FiniteLocalField q) (FiniteAlgebraicClosure q) :=
  AlgebraicClosure.isAlgebraic (FiniteLocalField q)

local instance finiteIsAlgClosure (q : Nat.Primes) :
    IsAlgClosure (FiniteLocalField q) (FiniteAlgebraicClosure q) :=
  ⟨AlgebraicClosure.isAlgClosed (FiniteLocalField q),
    finiteClosureIsAlgebraic q⟩

/-- Source-independent embedding of the chosen global algebraic closure into
the chosen local algebraic closure. -/
noncomputable def globalClosureEmbedding (q : Nat.Primes) :
    AlgebraicClosure ℚ →ₐ[ℚ] FiniteAlgebraicClosure q :=
  IsAlgClosed.lift

abbrev GlobalClosureImage (q : Nat.Primes) :
    IntermediateField ℚ (FiniteAlgebraicClosure q) :=
  (globalClosureEmbedding q).fieldRange

noncomputable def globalClosureEquivImage (q : Nat.Primes) :
    AlgebraicClosure ℚ ≃ₐ[ℚ] GlobalClosureImage q := by
  let f := globalClosureEmbedding q
  exact (AlgEquiv.ofInjectiveField f).trans
    (Subalgebra.equivOfEq f.range f.fieldRange.toSubalgebra
      (AlgHom.fieldRange_toSubalgebra f).symm)

local instance globalClosureImageNormal (q : Nat.Primes) :
    Normal ℚ (GlobalClosureImage q) :=
  Normal.of_algEquiv (globalClosureEquivImage q)

noncomputable def localToImageGaloisMonoidHom (q : Nat.Primes) :
    Field.absoluteGaloisGroup (FiniteLocalField q) →*
      (GlobalClosureImage q ≃ₐ[ℚ] GlobalClosureImage q) :=
  (AlgEquiv.restrictNormalHom (GlobalClosureImage q)).comp
    (AlgEquiv.restrictScalarsHom ℚ)

noncomputable def localToGlobalGaloisMonoidHom (q : Nat.Primes) :
    Field.absoluteGaloisGroup (FiniteLocalField q) →*
      Field.absoluteGaloisGroup ℚ :=
  (AlgEquiv.autCongr (globalClosureEquivImage q)).symm.toMonoidHom.comp
    (localToImageGaloisMonoidHom q)

private theorem restrictScalarsHom_continuous (q : Nat.Primes) :
    Continuous (AlgEquiv.restrictScalarsHom ℚ :
      (FiniteAlgebraicClosure q ≃ₐ[FiniteLocalField q]
        FiniteAlgebraicClosure q) →*
      (FiniteAlgebraicClosure q ≃ₐ[ℚ] FiniteAlgebraicClosure q)) := by
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr ?_)
  intro N hN
  rw [map_one, krullTopology_mem_nhds_one_iff] at hN
  obtain ⟨E, hEfin, hEN⟩ := hN
  letI : FiniteDimensional ℚ E := hEfin
  let b := Module.Basis.ofVectorSpace ℚ E
  letI : Fintype (Module.Basis.ofVectorSpaceIndex ℚ E) :=
    FiniteDimensional.fintypeBasisIndex b
  let U : Set (FiniteAlgebraicClosure q ≃ₐ[FiniteLocalField q]
      FiniteAlgebraicClosure q) :=
    ⋂ i, (MulAction.stabilizer
      (FiniteAlgebraicClosure q ≃ₐ[FiniteLocalField q]
        FiniteAlgebraicClosure q)
      ((b i : E) : FiniteAlgebraicClosure q) : Set _)
  have hUopen : IsOpen U := by
    apply isOpen_iInter_of_finite
    intro i
    exact stabilizer_isOpen_of_isIntegral
      ((b i : E) : FiniteAlgebraicClosure q)
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

private theorem autCongr_continuous
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

private theorem autCongr_symm_continuous
    {k : Type u} {A : Type v} {B : Type w}
    [Field k] [Field A] [Field B]
    [Algebra k A] [Algebra k B]
    [Algebra.IsIntegral k A] [Algebra.IsIntegral k B]
    (e : A ≃ₐ[k] B) :
    Continuous (AlgEquiv.autCongr e).symm := by
  rw [AlgEquiv.autCongr_symm]
  exact autCongr_continuous e.symm

theorem localToGlobalGaloisMonoidHom_continuous (q : Nat.Primes) :
    Continuous (localToGlobalGaloisMonoidHom q) := by
  have hres : Continuous
      (AlgEquiv.restrictNormalHom (GlobalClosureImage q) :
        (FiniteAlgebraicClosure q ≃ₐ[ℚ] FiniteAlgebraicClosure q) →*
        (GlobalClosureImage q ≃ₐ[ℚ] GlobalClosureImage q)) :=
    @InfiniteGalois.restrictNormalHom_continuous
      ℚ (FiniteAlgebraicClosure q) _ _ _
      (GlobalClosureImage q) (globalClosureImageNormal q)
  exact (autCongr_symm_continuous (globalClosureEquivImage q)).comp
    (hres.comp (restrictScalarsHom_continuous q))

/-- The source-independent continuous decomposition homomorphism. -/
noncomputable def localToGlobalGaloisHom (q : Nat.Primes) :
    Field.absoluteGaloisGroup (FiniteLocalField q) →ₜ*
      Field.absoluteGaloisGroup ℚ where
  toMonoidHom := localToGlobalGaloisMonoidHom q
  continuous_toFun := localToGlobalGaloisMonoidHom_continuous q

theorem globalClosureEmbedding_galois_commutes
    (q : Nat.Primes)
    (sigma : Field.absoluteGaloisGroup (FiniteLocalField q))
    (x : AlgebraicClosure ℚ) :
    globalClosureEmbedding q
        ((localToGlobalGaloisHom q sigma).toAlgHom x) =
      sigma.toAlgHom (globalClosureEmbedding q x) := by
  let e := globalClosureEquivImage q
  let tau := localToImageGaloisMonoidHom q sigma
  have he_val (z : AlgebraicClosure ℚ) :
      ((e z : GlobalClosureImage q) : FiniteAlgebraicClosure q) =
        globalClosureEmbedding q z := by
    rfl
  have he_symm_val (z : GlobalClosureImage q) :
      globalClosureEmbedding q (e.symm z) = z.1 := by
    calc
      globalClosureEmbedding q (e.symm z) =
          (e (e.symm z)).1 := (he_val (e.symm z)).symm
      _ = z.1 := congrArg Subtype.val (e.apply_symm_apply z)
  have hglobal :
      (localToGlobalGaloisHom q sigma).toAlgHom x =
        e.symm (tau (e x)) := by
    rfl
  rw [hglobal, he_symm_val]
  have htau : (tau (e x)).1 = sigma.toAlgHom (e x).1 := by
    have haction :
        localToImageGaloisMonoidHom q sigma =
          (AlgEquiv.restrictNormalHom (GlobalClosureImage q))
            (sigma.restrictScalars ℚ) := by
      rfl
    rw [show tau = localToImageGaloisMonoidHom q sigma from rfl, haction]
    exact @AlgEquiv.restrictNormalHom_apply
      ℚ inferInstance (FiniteAlgebraicClosure q) inferInstance inferInstance
      (GlobalClosureImage q) (globalClosureImageNormal q)
      (sigma.restrictScalars ℚ) (e x)
  rw [htau, he_val]

/-! ## Actual local geometric-point representation -/

/-- The source curve over the chosen algebraic closure of `Q_q`. -/
abbrev FiniteGeometricCurve
    (source : RationalEllipticCurveSource) (q : Nat.Primes) :
    WeierstrassCurve (FiniteAlgebraicClosure q) :=
  source.curve.baseChange (FiniteAlgebraicClosure q)

instance finiteGeometricCurve_isElliptic
    (source : RationalEllipticCurveSource) (q : Nat.Primes) :
    (FiniteGeometricCurve source q).IsElliptic := by
  unfold FiniteGeometricCurve WeierstrassCurve.baseChange
  infer_instance

/-- Actual local geometric points `E(Qbar_q)`. -/
abbrev FiniteGeometricPoints
    (source : RationalEllipticCurveSource) (q : Nat.Primes) :=
  (FiniteGeometricCurve source q).toAffine.Point

local instance finiteClosureGaloisSMul (q : Nat.Primes) :
    SMul (Field.absoluteGaloisGroup (FiniteLocalField q))
      (FiniteAlgebraicClosure q) :=
  ⟨fun sigma x ↦ sigma.toAlgHom x⟩

local instance finiteClosureGaloisMulAction (q : Nat.Primes) :
    MulAction (Field.absoluteGaloisGroup (FiniteLocalField q))
      (FiniteAlgebraicClosure q) where
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- Coordinate action of the local absolute Galois group. -/
noncomputable def finiteGeometricPointGaloisMap
    (source : RationalEllipticCurveSource) (q : Nat.Primes)
    (sigma : Field.absoluteGaloisGroup (FiniteLocalField q)) :
    FiniteGeometricPoints source q →+ FiniteGeometricPoints source q :=
  WeierstrassCurve.Affine.Point.map
    (W' := source.curve) (sigma.restrictScalars ℚ).toAlgHom

theorem finiteGeometricPointGaloisMap_comp
    (source : RationalEllipticCurveSource) (q : Nat.Primes)
    (sigma tau : Field.absoluteGaloisGroup (FiniteLocalField q))
    (point : FiniteGeometricPoints source q) :
    finiteGeometricPointGaloisMap source q (sigma * tau) point =
      finiteGeometricPointGaloisMap source q sigma
        (finiteGeometricPointGaloisMap source q tau point) := by
  simp only [finiteGeometricPointGaloisMap]
  rw [WeierstrassCurve.Affine.Point.map_map]
  rfl

instance finiteGeometricPointsGaloisSMul
    (source : RationalEllipticCurveSource) (q : Nat.Primes) :
    SMul (Field.absoluteGaloisGroup (FiniteLocalField q))
      (FiniteGeometricPoints source q) :=
  ⟨fun sigma point ↦ finiteGeometricPointGaloisMap source q sigma point⟩

instance finiteGeometricPointsGaloisMulAction
    (source : RationalEllipticCurveSource) (q : Nat.Primes) :
    MulAction (Field.absoluteGaloisGroup (FiniteLocalField q))
      (FiniteGeometricPoints source q) where
  one_smul point := by
    rcases point with (_ | ⟨x, y, hpoint⟩) <;> rfl
  mul_smul sigma tau point :=
    finiteGeometricPointGaloisMap_comp source q sigma tau point

instance finiteGeometricPointsTopology
    (source : RationalEllipticCurveSource) (q : Nat.Primes) :
    TopologicalSpace (FiniteGeometricPoints source q) :=
  ⊥

instance finiteGeometricPointsDiscreteTopology
    (source : RationalEllipticCurveSource) (q : Nat.Primes) :
    DiscreteTopology (FiniteGeometricPoints source q) :=
  ⟨rfl⟩

instance finiteGeometricPointsContinuousIntSMul
    (source : RationalEllipticCurveSource) (q : Nat.Primes) :
    ContinuousSMul ℤ (FiniteGeometricPoints source q) :=
  ⟨continuous_of_discreteTopology⟩

/-- Every actual local geometric point has open local-Galois stabilizer. -/
theorem finiteGeometricPoints_stabilizer_isOpen
    (source : RationalEllipticCurveSource) (q : Nat.Primes)
    (point : FiniteGeometricPoints source q) :
    IsOpen
      (MulAction.stabilizer
        (Field.absoluteGaloisGroup (FiniteLocalField q)) point :
        Set (Field.absoluteGaloisGroup (FiniteLocalField q))) := by
  rcases point with (_ | ⟨x, y, hpoint⟩)
  · have htop :
        (MulAction.stabilizer
          (Field.absoluteGaloisGroup (FiniteLocalField q))
          (WeierstrassCurve.Affine.Point.zero :
            FiniteGeometricPoints source q) :
          Set (Field.absoluteGaloisGroup (FiniteLocalField q))) = Set.univ := by
      ext sigma
      simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff,
        Set.mem_univ, iff_true]
      rfl
    rw [htop]
    exact isOpen_univ
  · have hx : IsOpen
        (MulAction.stabilizer
          (Field.absoluteGaloisGroup (FiniteLocalField q)) x :
          Set (Field.absoluteGaloisGroup (FiniteLocalField q))) :=
      stabilizer_isOpen_of_isIntegral x
    have hy : IsOpen
        (MulAction.stabilizer
          (Field.absoluteGaloisGroup (FiniteLocalField q)) y :
          Set (Field.absoluteGaloisGroup (FiniteLocalField q))) :=
      stabilizer_isOpen_of_isIntegral y
    have hcoordinates :
        (MulAction.stabilizer
          (Field.absoluteGaloisGroup (FiniteLocalField q))
          (WeierstrassCurve.Affine.Point.some x y hpoint) :
          Set (Field.absoluteGaloisGroup (FiniteLocalField q))) =
        (MulAction.stabilizer
          (Field.absoluteGaloisGroup (FiniteLocalField q)) x : Set _) ∩
        (MulAction.stabilizer
          (Field.absoluteGaloisGroup (FiniteLocalField q)) y : Set _) := by
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

instance finiteGeometricPointsContinuousGaloisSMul
    (source : RationalEllipticCurveSource) (q : Nat.Primes) :
    ContinuousSMul (Field.absoluteGaloisGroup (FiniteLocalField q))
      (FiniteGeometricPoints source q) :=
  continuousSMul_iff_stabilizer_isOpen.mpr
    (finiteGeometricPoints_stabilizer_isOpen source q)

noncomputable def finiteGeometricPointGaloisContinuousLinearMap
    (source : RationalEllipticCurveSource) (q : Nat.Primes)
    (sigma : Field.absoluteGaloisGroup (FiniteLocalField q)) :
    FiniteGeometricPoints source q →L[ℤ]
      FiniteGeometricPoints source q :=
  ContinuousLinearMap.mk
    (finiteGeometricPointGaloisMap source q sigma).toIntLinearMap
    continuous_of_discreteTopology

noncomputable def finiteGeometricPointGaloisMonoidHom
    (source : RationalEllipticCurveSource) (q : Nat.Primes) :
    Field.absoluteGaloisGroup (FiniteLocalField q) →*
      (FiniteGeometricPoints source q →L[ℤ]
        FiniteGeometricPoints source q) where
  toFun := finiteGeometricPointGaloisContinuousLinearMap source q
  map_one' := by
    ext point
    rcases point with (_ | ⟨x, y, h⟩) <;> rfl
  map_mul' sigma tau := by
    ext point
    exact finiteGeometricPointGaloisMap_comp source q sigma tau point

/-- Actual full local geometric-point representation. -/
noncomputable def finiteGeometricPointTopRep
    (source : RationalEllipticCurveSource) (q : Nat.Primes) :
    TopRep ℤ (Field.absoluteGaloisGroup (FiniteLocalField q)) :=
  TopRep.of (ContRepresentation.ofMonoidHom
    (finiteGeometricPointGaloisMonoidHom source q))

@[simp]
theorem finiteGeometricPointTopRep_rho_apply
    (source : RationalEllipticCurveSource) (q : Nat.Primes)
    (sigma : Field.absoluteGaloisGroup (FiniteLocalField q))
    (point : FiniteGeometricPoints source q) :
    (finiteGeometricPointTopRep source q).ρ sigma point = sigma • point :=
  rfl

/-- The bundled local representation is definitionally the explicit coordinate action. -/
@[simp]
theorem finiteGeometricPointTopRep_rho_apply_explicit
    (source : RationalEllipticCurveSource) (q : Nat.Primes)
    (sigma : Field.absoluteGaloisGroup (FiniteLocalField q))
    (point : FiniteGeometricPoints source q) :
    (finiteGeometricPointTopRep source q).ρ sigma point =
      finiteGeometricPointGaloisMap source q sigma point :=
  rfl

/-! ## Equivariant global-to-local coefficient map -/

/-- The chosen global algebraic-closure embedding applied to actual points. -/
noncomputable def globalGeometricPointToFinite
    (source : RationalEllipticCurveSource) (q : Nat.Primes) :
    GeometricPoints source →+ FiniteGeometricPoints source q :=
  WeierstrassCurve.Affine.Point.map
    (W' := source.curve) (globalClosureEmbedding q)

theorem globalGeometricPointToFinite_galois_commutes
    (source : RationalEllipticCurveSource) (q : Nat.Primes)
    (sigma : Field.absoluteGaloisGroup (FiniteLocalField q))
    (point : GeometricPoints source) :
    globalGeometricPointToFinite source q
        (geometricPointGaloisMap source
          (localToGlobalGaloisHom q sigma) point) =
      finiteGeometricPointGaloisMap source q sigma
        (globalGeometricPointToFinite source q point) := by
  rcases point with (_ | ⟨x, y, hpoint⟩)
  · rfl
  · change WeierstrassCurve.Affine.Point.some
        (globalClosureEmbedding q
          ((localToGlobalGaloisHom q sigma).toAlgHom x))
        (globalClosureEmbedding q
          ((localToGlobalGaloisHom q sigma).toAlgHom y)) _ =
      WeierstrassCurve.Affine.Point.some
        (sigma.toAlgHom (globalClosureEmbedding q x))
        (sigma.toAlgHom (globalClosureEmbedding q y)) _
    congr 1
    · exact globalClosureEmbedding_galois_commutes q sigma x
    · exact globalClosureEmbedding_galois_commutes q sigma y

noncomputable def globalGeometricPointToFiniteContinuousLinearMap
    (source : RationalEllipticCurveSource) (q : Nat.Primes) :
    GeometricPoints source →L[ℤ] FiniteGeometricPoints source q :=
  ContinuousLinearMap.mk
    (globalGeometricPointToFinite source q).toIntLinearMap
    continuous_of_discreteTopology

/-- The actual coefficient morphism over the generated decomposition map. -/
noncomputable def globalGeometricPointToFiniteTopRepHom
    (source : RationalEllipticCurveSource) (q : Nat.Primes) :
    TopRep.res (localToGlobalGaloisHom q).toMonoidHom
        (geometricPointTopRep source) ⟶
      finiteGeometricPointTopRep source q :=
  TopRep.ofHom ⟨
    globalGeometricPointToFiniteContinuousLinearMap source q,
    by
      intro sigma
      ext point
      exact globalGeometricPointToFinite_galois_commutes
        source q sigma point
  ⟩

end

end UniversalBSDFinitePlaceFullPoint
end SaturationMonoid
