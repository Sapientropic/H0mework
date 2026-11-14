import H0mework.Versions.R21a4a7ce.ReleaseMaterials.SaturationMonoid.UniversalBSDGeometricDivisibility
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.GroupTheory.Index
import H0mework.Versions.R21a4a7ce.ReleaseMaterials.SaturationMonoid.UniversalBSDNTorsionCohomology
import H0mework.Versions.R21a4a7ce.ReleaseMaterials.SaturationMonoid.UniversalBSDRationalMordellWeilHeight
import H0mework.Versions.R21a4a7ce.ReleaseMaterials.SaturationMonoid.UniversalBSDUnramifiedCocycleNormalization

/-!
# Universal BSD rational Kummer cohomology

Actual geometric divisibility generates the continuous rational Kummer
boundary class. Its cohomology class is independent of the chosen division
point, has kernel exactly `nE(ℚ)`, and turns finite global Kummer H¹ into the
weak Mordell--Weil finite-index input.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace UniversalBSDRationalKummerCohomology

open CategoryTheory
open UniversalBSDGeometricDivisibility
open UniversalBSDGeometricGalois
open UniversalBSDGeometricNTorsion
open UniversalBSDNTorsionCohomology
open UniversalBSDUnramifiedCocycleNormalization
open UniversalBSDSelmerCohomology
open UniversalBSDRationalMordellWeilHeight

noncomputable section

set_option maxHeartbeats 1200000

local instance rationalGlobalClosureIsAlgebraic :
    Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ

local instance rationalGlobalIsAlgClosure :
    IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
  ⟨AlgebraicClosure.isAlgClosed ℚ, rationalGlobalClosureIsAlgebraic⟩

local instance rationalGlobalClosureNormal :
    Normal ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

abbrev RationalPoints (source : RationalEllipticCurveSource) :=
  source.curve.toAffine.Point

noncomputable def rationalPointToGeometric
    (source : RationalEllipticCurveSource) :
    RationalPoints source →+ GeometricPoints source :=
  WeierstrassCurve.Affine.Point.map (W' := source.curve)
    (Algebra.ofId ℚ (AlgebraicClosure ℚ))

theorem rationalPointToGeometric_injective
    (source : RationalEllipticCurveSource) :
    Function.Injective (rationalPointToGeometric source) :=
  WeierstrassCurve.Affine.Point.map_injective
    (W' := source.curve) (Algebra.ofId ℚ (AlgebraicClosure ℚ))

@[simp]
theorem rationalPointToGeometric_galois_fixed
    (source : RationalEllipticCurveSource)
    (sigma : Field.absoluteGaloisGroup ℚ)
    (P : RationalPoints source) :
    geometricPointGaloisMap source sigma
        (rationalPointToGeometric source P) =
      rationalPointToGeometric source P := by
  rcases P with (_ | ⟨x, y, hPoint⟩)
  · rfl
  · have hx :
        sigma.toAlgHom (algebraMap ℚ (AlgebraicClosure ℚ) x) =
          algebraMap ℚ (AlgebraicClosure ℚ) x :=
      sigma.toAlgHom.commutes x
    have hy :
        sigma.toAlgHom (algebraMap ℚ (AlgebraicClosure ℚ) y) =
          algebraMap ℚ (AlgebraicClosure ℚ) y :=
      sigma.toAlgHom.commutes y
    change WeierstrassCurve.Affine.Point.some
        (sigma.toAlgHom (algebraMap ℚ (AlgebraicClosure ℚ) x))
        (sigma.toAlgHom (algebraMap ℚ (AlgebraicClosure ℚ) y)) _ =
      WeierstrassCurve.Affine.Point.some
        (algebraMap ℚ (AlgebraicClosure ℚ) x)
        (algebraMap ℚ (AlgebraicClosure ℚ) y) _
    exact Eq.mpr
      (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _)
      ⟨hx, hy⟩

theorem exists_geometric_division_of_rationalPoint
    (source : RationalEllipticCurveSource)
    (n : ℕ) (hn : 0 < n) (P : RationalPoints source) :
    ∃ Q : GeometricPoints source,
      n • Q = rationalPointToGeometric source P :=
  exists_actual_nsmul_eq (GeometricCurve source) n hn
    (rationalPointToGeometric source P)

private theorem homogeneousZeroBoundary_apply
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (X : TopRep ℤ G)
    (q₀ : (TopRep.homogeneousCochains X).X 0)
    (sigma tau : G) :
    (((TopRep.homogeneousCochains X).d 0 1).hom q₀).1 sigma tau =
      q₀.1 tau - q₀.1 sigma := by
  rw [TopRep.homogeneousCochains.d_apply]
  rfl

set_option linter.style.haveILetI false in
private theorem geometricNTorsion_topology_eq_induced
    (source : RationalEllipticCurveSource) (n : ℕ) :
    (inferInstance : TopologicalSpace (GeometricNTorsion source n)) =
      TopologicalSpace.induced
        (fun point : GeometricNTorsion source n ↦ point.1)
        (inferInstance : TopologicalSpace (GeometricPoints source)) := by
  change (⊥ : TopologicalSpace (GeometricNTorsion source n)) =
    TopologicalSpace.induced
      (fun point : GeometricNTorsion source n ↦ point.1)
      (⊥ : TopologicalSpace (GeometricPoints source))
  let t : TopologicalSpace (GeometricNTorsion source n) :=
    TopologicalSpace.induced
      (fun point : GeometricNTorsion source n ↦ point.1)
      (⊥ : TopologicalSpace (GeometricPoints source))
  change (⊥ : TopologicalSpace (GeometricNTorsion source n)) = t
  symm
  letI : TopologicalSpace (GeometricNTorsion source n) := t
  haveI : DiscreteTopology (GeometricNTorsion source n) :=
    Topology.IsEmbedding.subtypeVal.discreteTopology
  exact DiscreteTopology.eq_bot

private theorem geometricNTorsion_subtypeVal_isEmbedding
    (source : RationalEllipticCurveSource) (n : ℕ) :
    Topology.IsEmbedding (fun point : GeometricNTorsion source n ↦ point.1) := by
  exact ⟨⟨geometricNTorsion_topology_eq_induced source n⟩,
    Subtype.val_injective⟩

private theorem geometricPointTopRep_topology_eq
    (source : RationalEllipticCurveSource) :
    (inferInstance : TopologicalSpace (geometricPointTopRep source)) =
      geometricPointsTopology source :=
  rfl

private theorem resolutionX_one_topology_eq
    (source : RationalEllipticCurveSource) :
    (inferInstance : TopologicalSpace
      (TopRep.resolutionX (geometricPointTopRep source) 1)) =
        ContinuousMap.compactOpen :=
  rfl

private theorem homogeneous_iCycles_one_injective
    (X : TopRep ℤ (Field.absoluteGaloisGroup ℚ)) :
    Function.Injective ((TopRep.homogeneousCochains X).iCycles 1).hom := by
  intro x y hxy
  let K := TopRep.homogeneousCochains X
  let S := K.sc' 0 1 2
  let eKS := K.cyclesIsoSc' 0 1 2 (by simp) (by simp)
  let eKer := S.isoCyclesOfIsLimit (TopModuleCat.isLimitKer S.g)
  have hxKS : S.iCycles.hom (eKS.hom.hom x) = (K.iCycles 1).hom x :=
    ConcreteCategory.congr_hom
      (K.cyclesIsoSc'_hom_iCycles 0 1 2 (by simp) (by simp)) x
  have hyKS : S.iCycles.hom (eKS.hom.hom y) = (K.iCycles 1).hom y :=
    ConcreteCategory.congr_hom
      (K.cyclesIsoSc'_hom_iCycles 0 1 2 (by simp) (by simp)) y
  have hSval : S.iCycles.hom (eKS.hom.hom x) =
      S.iCycles.hom (eKS.hom.hom y) :=
    hxKS.trans (hxy.trans hyKS.symm)
  have hxKer : (TopModuleCat.kerι S.g).hom
      (eKer.inv.hom (eKS.hom.hom x)) = S.iCycles.hom (eKS.hom.hom x) :=
    ConcreteCategory.congr_hom
      (S.isoCyclesOfIsLimit_inv_ι (TopModuleCat.isLimitKer S.g))
      (eKS.hom.hom x)
  have hyKer : (TopModuleCat.kerι S.g).hom
      (eKer.inv.hom (eKS.hom.hom y)) = S.iCycles.hom (eKS.hom.hom y) :=
    ConcreteCategory.congr_hom
      (S.isoCyclesOfIsLimit_inv_ι (TopModuleCat.isLimitKer S.g))
      (eKS.hom.hom y)
  have hKer : eKer.inv.hom (eKS.hom.hom x) =
      eKer.inv.hom (eKS.hom.hom y) := by
    apply Subtype.ext
    exact hxKer.trans (hSval.trans hyKer.symm)
  have hS : eKS.hom.hom x = eKS.hom.hom y := by
    have h := congrArg (fun z ↦ eKer.hom.hom z) hKer
    have hxBack : eKer.hom.hom (eKer.inv.hom (eKS.hom.hom x)) =
        eKS.hom.hom x :=
      ConcreteCategory.congr_hom eKer.inv_hom_id (eKS.hom.hom x)
    have hyBack : eKer.hom.hom (eKer.inv.hom (eKS.hom.hom y)) =
        eKS.hom.hom y :=
      ConcreteCategory.congr_hom eKer.inv_hom_id (eKS.hom.hom y)
    exact hxBack.symm.trans (h.trans hyBack)
  have h := congrArg (fun z ↦ eKS.inv.hom z) hS
  have hxBack : eKS.inv.hom (eKS.hom.hom x) = x :=
    ConcreteCategory.congr_hom eKS.hom_inv_id x
  have hyBack : eKS.inv.hom (eKS.hom.hom y) = y :=
    ConcreteCategory.congr_hom eKS.hom_inv_id y
  exact hxBack.symm.trans (h.trans hyBack)

private theorem homogeneous_pi_eq_of_sub_iCycles_eq_d
    (X : TopRep ℤ (Field.absoluteGaloisGroup ℚ))
    (z₁ z₂ : ContinuousCohomology.cocycles X 1)
    (q : (TopRep.homogeneousCochains X).X 0)
    (hboundary :
      ((TopRep.homogeneousCochains X).iCycles 1).hom (z₁ - z₂) =
        ((TopRep.homogeneousCochains X).d 0 1).hom q) :
    (ContinuousCohomology.π X 1).hom z₁ =
      (ContinuousCohomology.π X 1).hom z₂ := by
  let K := TopRep.homogeneousCochains X
  have hto : (K.iCycles 1).hom ((K.toCycles 0 1).hom q) =
      (K.d 0 1).hom q :=
    ConcreteCategory.congr_hom (K.toCycles_i 0 1) q
  have hcycles : z₁ - z₂ = (K.toCycles 0 1).hom q := by
    apply homogeneous_iCycles_one_injective X
    exact hboundary.trans hto.symm
  have hzero : (K.homologyπ 1).hom (z₁ - z₂) = 0 := by
    rw [hcycles]
    exact ConcreteCategory.congr_hom (K.toCycles_comp_homologyπ 0 1) q
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact hzero

structure RationalKummerBoundaryCochainData
    (source : RationalEllipticCurveSource) (n : ℕ)
    (P : RationalPoints source) : Type where
  private mk ::
  divisionPoint : GeometricPoints source
  divides : n • divisionPoint = rationalPointToGeometric source P
  zeroCochain : (TopRep.homogeneousCochains (geometricPointTopRep source)).X 0
  zeroCochain_apply : ∀ sigma : Field.absoluteGaloisGroup ℚ,
    zeroCochain.1 sigma = (geometricPointTopRep source).ρ sigma divisionPoint
  torsionCochain : (NTorsionContinuousCochainComplex source n).X 1
  torsion_cycle :
    ((NTorsionContinuousCochainComplex source n).d 1 2).hom torsionCochain = 0
  mapped_eq_boundary :
    ((nTorsionToPointCochainMap source n).f 1).hom torsionCochain =
      ((TopRep.homogeneousCochains (geometricPointTopRep source)).d 0 1).hom
        zeroCochain

noncomputable def sourceGeneratedRationalKummerBoundaryCochain
    (source : RationalEllipticCurveSource)
    (n : ℕ) (hn : 0 < n) (P : RationalPoints source) :
    RationalKummerBoundaryCochainData source n P := by
  let Q := Classical.choose
    (exists_geometric_division_of_rationalPoint source n hn P)
  have hQ : n • Q = rationalPointToGeometric source P :=
    Classical.choose_spec
      (exists_geometric_division_of_rationalPoint source n hn P)
  have orbitContinuous : Continuous
      (fun sigma : Field.absoluteGaloisGroup ℚ ↦
        (geometricPointTopRep source).ρ sigma Q) := by
    change Continuous
      (fun sigma : Field.absoluteGaloisGroup ℚ ↦ sigma • Q)
    exact continuous_smul.comp (continuous_id.prodMk continuous_const)
  let q₀ : (TopRep.homogeneousCochains (geometricPointTopRep source)).X 0 :=
    orbitZeroCochain (geometricPointTopRep source) Q orbitContinuous
  let boundary :
      (TopRep.homogeneousCochains (geometricPointTopRep source)).X 1 :=
    ((TopRep.homogeneousCochains (geometricPointTopRep source)).d 0 1).hom q₀
  have boundary_torsion (sigma tau : Field.absoluteGaloisGroup ℚ) :
      n • boundary.1 sigma tau = 0 := by
    rw [homogeneousZeroBoundary_apply]
    have hTau : q₀.1 tau = (geometricPointTopRep source).ρ tau Q := by
      dsimp only [q₀]
      exact orbitZeroCochain_apply (geometricPointTopRep source)
        Q orbitContinuous tau
    have hSigma : q₀.1 sigma = (geometricPointTopRep source).ρ sigma Q := by
      dsimp only [q₀]
      exact orbitZeroCochain_apply (geometricPointTopRep source)
        Q orbitContinuous sigma
    rw [hTau, hSigma]
    rw [nsmul_sub]
    change n • geometricPointGaloisMap source tau Q -
        n • geometricPointGaloisMap source sigma Q = 0
    rw [← AddMonoidHom.map_nsmul, ← AddMonoidHom.map_nsmul, hQ]
    rw [rationalPointToGeometric_galois_fixed,
      rationalPointToGeometric_galois_fixed, sub_self]
  let zValue (sigma tau : Field.absoluteGaloisGroup ℚ) :
      GeometricNTorsion source n :=
    ⟨boundary.1 sigma tau,
      AddSubgroup.torsionBy.nsmul_iff.mpr (boundary_torsion sigma tau)⟩
  let inclusion : C(GeometricNTorsion source n,
      TopRep.resolutionX (geometricPointTopRep source) 0) :=
    ⟨fun point ↦ point.1,
      (geometricNTorsionToGeometricPointContinuousLinearMap source n).continuous⟩
  have inclusionEmbedding : Topology.IsEmbedding inclusion := by
    refine ⟨⟨?_⟩, Subtype.val_injective⟩
    exact geometricNTorsion_topology_eq_induced source n
  let zInner (sigma : Field.absoluteGaloisGroup ℚ) :
      C(Field.absoluteGaloisGroup ℚ, GeometricNTorsion source n) :=
    ⟨fun tau ↦ zValue sigma tau,
      inclusionEmbedding.continuous_iff.mpr (by
        have heq : inclusion ∘ (fun tau ↦ zValue sigma tau) =
            fun tau ↦ boundary.1 sigma tau := by
          funext tau
          rfl
        rw [heq]
        exact (boundary.1 sigma).continuous)⟩
  have zInnerContinuous : Continuous zInner := by
    apply (inclusion.isEmbedding_postcomp inclusionEmbedding).continuous_iff.mpr
    have heq : (fun sigma ↦ inclusion.comp (zInner sigma)) =
        fun sigma ↦ boundary.1 sigma := by
      funext sigma
      apply ContinuousMap.ext
      intro tau
      rfl
    change Continuous (fun sigma ↦ inclusion.comp (zInner sigma))
    rw [heq]
    have hcontinuous := boundary.1.continuous
    rw [continuous_iff_coinduced_le] at hcontinuous ⊢
    exact hcontinuous.trans_eq (resolutionX_one_topology_eq source)
  let zMap : C(Field.absoluteGaloisGroup ℚ,
      C(Field.absoluteGaloisGroup ℚ, GeometricNTorsion source n)) :=
    ⟨zInner, zInnerContinuous⟩
  have zInvariant :
      zMap ∈ ((geometricNTorsionIntTopRep source n).resolution'.X 1).ρ.invariants := by
    intro t
    ext sigma tau
    apply Subtype.ext
    have hBoundary := boundary.2 t
    exact congrArg (fun cochain ↦ cochain sigma tau) hBoundary
  let z : (NTorsionContinuousCochainComplex source n).X 1 :=
    ⟨zMap, zInvariant⟩
  have pointBoundaryCycle :
      ((GlobalContinuousCochainComplex source).d 1 2).hom boundary = 0 := by
    dsimp only [boundary]
    have dd := ConcreteCategory.congr_hom
      ((GlobalContinuousCochainComplex source).d_comp_d 0 1 2) q₀
    simp only [ConcreteCategory.comp_apply] at dd
    have zeroApply :
        ((0 : (GlobalContinuousCochainComplex source).X 0 ⟶
          (GlobalContinuousCochainComplex source).X 2).hom q₀) = 0 := rfl
    exact dd.trans zeroApply
  have mapTwoInjective : Function.Injective
      ((nTorsionToPointCochainMap source n).f 2).hom := by
    intro x y hxy
    apply Subtype.ext
    apply ContinuousMap.ext
    intro sigma
    apply ContinuousMap.ext
    intro tau
    apply ContinuousMap.ext
    intro upsilon
    apply Subtype.ext
    have heval := congrArg (fun cochain ↦ cochain.1 sigma tau upsilon) hxy
    exact heval
  have zCycle :
      ((NTorsionContinuousCochainComplex source n).d 1 2).hom z = 0 := by
    apply mapTwoInjective
    have commutes := ConcreteCategory.congr_hom
      ((nTorsionToPointCochainMap source n).comm 1 2) z
    simp only [ConcreteCategory.comp_apply] at commutes
    have mappedEq :
        ((nTorsionToPointCochainMap source n).f 1).hom z = boundary := by
      apply Subtype.ext
      apply ContinuousMap.ext
      intro sigma
      apply ContinuousMap.ext
      intro tau
      rfl
    rw [map_zero]
    exact commutes.symm.trans (by rw [mappedEq]; exact pointBoundaryCycle)
  refine ⟨Q, hQ, q₀, ?_, z, zCycle, ?_⟩
  · intro sigma
    exact orbitZeroCochain_apply (geometricPointTopRep source)
      Q orbitContinuous sigma
  · apply Subtype.ext
    apply ContinuousMap.ext
    intro sigma
    apply ContinuousMap.ext
    intro tau
    rfl

theorem exists_homogeneousBoundary_of_h1_eq_zero
    (source : RationalEllipticCurveSource) (n : ℕ)
    (z : ContinuousCohomology.cocycles
      (geometricNTorsionIntTopRep source n) 1)
    (hzero : (ContinuousCohomology.π
      (geometricNTorsionIntTopRep source n) 1).hom z = 0) :
    ∃ q : (TopRep.homogeneousCochains
        (geometricNTorsionIntTopRep source n)).X 0,
      ((TopRep.homogeneousCochains
        (geometricNTorsionIntTopRep source n)).d 0 1).hom q =
        ((TopRep.homogeneousCochains
          (geometricNTorsionIntTopRep source n)).iCycles 1).hom z := by
  let K := TopRep.homogeneousCochains
    (geometricNTorsionIntTopRep source n)
  let S := K.sc' 0 1 2
  let zS : S.cycles := (K.cyclesIsoSc' 0 1 2 (by simp) (by simp)).hom z
  have hzeroS : S.homologyπ.hom zS = 0 := by
    have h := ConcreteCategory.congr_hom
      (K.π_homologyIsoSc'_hom 0 1 2 (by simp) (by simp)) z
    simp only [ConcreteCategory.comp_apply] at h
    rw [hzero] at h
    simpa [zS] using h.symm
  let D : S.LeftHomologyData :=
    ⟨_, _, _, _, _, TopModuleCat.isLimitKer _, by simp,
      TopModuleCat.isColimitCoker _⟩
  have hzeroLeft : S.leftHomologyπ.hom zS = 0 := by
    have h := ConcreteCategory.congr_hom
      S.homologyπ_comp_leftHomologyIso_inv zS
    simp only [ConcreteCategory.comp_apply] at h
    rw [hzeroS] at h
    simpa using h.symm
  have hzeroD : D.π.hom (D.cyclesIso.hom.hom zS) = 0 := by
    have h := ConcreteCategory.congr_hom
      D.leftHomologyπ_comp_leftHomologyIso_hom zS
    simp only [ConcreteCategory.comp_apply] at h
    rw [hzeroLeft] at h
    simpa using h.symm
  change Submodule.mkQ D.f'.hom.range (D.cyclesIso.hom.hom zS) = 0 at hzeroD
  have hrange : D.cyclesIso.hom.hom zS ∈ D.f'.hom.range :=
    (Submodule.Quotient.mk_eq_zero _).mp hzeroD
  rcases hrange with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  have hqi := congrArg (fun x ↦ D.i.hom x) hq
  have hf'i := ConcreteCategory.congr_hom D.f'_i q
  have hcyclesi := ConcreteCategory.congr_hom D.cyclesIso_hom_comp_i zS
  have hSf : S.f.hom q = S.iCycles.hom zS := by
    calc
      S.f.hom q = D.i.hom (D.f'.hom q) := hf'i.symm
      _ = D.i.hom (D.cyclesIso.hom.hom zS) := hqi
      _ = S.iCycles.hom zS := hcyclesi
  have hKcycles := ConcreteCategory.congr_hom
    (K.cyclesIsoSc'_hom_iCycles 0 1 2 (by simp) (by simp)) z
  simp only [ConcreteCategory.comp_apply] at hKcycles
  change S.iCycles.hom zS = (K.iCycles 1).hom z at hKcycles
  rw [hKcycles] at hSf
  exact hSf

private theorem homogeneousZeroCochain_apply_eq_action
    (X : TopRep ℤ (Field.absoluteGaloisGroup ℚ))
    (q₀ : (TopRep.homogeneousCochains X).X 0)
    (sigma : Field.absoluteGaloisGroup ℚ) :
    q₀.1 sigma = X.ρ sigma (q₀.1 1) := by
  have h := DFunLike.ext_iff.1 (q₀.2 sigma) sigma
  simpa [ContRepresentation.coind₁_apply_apply] using h.symm

theorem exists_rationalPoint_of_geometric_galoisFixed
    (source : RationalEllipticCurveSource)
    (point : GeometricPoints source)
    (hfixed : ∀ sigma : Field.absoluteGaloisGroup ℚ,
      geometricPointGaloisMap source sigma point = point) :
    ∃ rationalPoint : RationalPoints source,
      rationalPointToGeometric source rationalPoint = point := by
  rcases point with _ | ⟨x, y, hPoint⟩
  · exact ⟨0, rfl⟩
  · have hxFixed : ∀ sigma : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        sigma x = x := by
      intro sigma
      have h := hfixed sigma
      change WeierstrassCurve.Affine.Point.map sigma.toAlgHom
          (WeierstrassCurve.Affine.Point.some x y hPoint) =
        WeierstrassCurve.Affine.Point.some x y hPoint at h
      exact (WeierstrassCurve.Affine.Point.some.inj h).1
    have hyFixed : ∀ sigma : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        sigma y = y := by
      intro sigma
      have h := hfixed sigma
      change WeierstrassCurve.Affine.Point.map sigma.toAlgHom
          (WeierstrassCurve.Affine.Point.some x y hPoint) =
        WeierstrassCurve.Affine.Point.some x y hPoint at h
      exact (WeierstrassCurve.Affine.Point.some.inj h).2
    obtain ⟨xQ, hxQ⟩ :=
      (InfiniteGalois.mem_range_algebraMap_iff_fixed x).2 hxFixed
    obtain ⟨yQ, hyQ⟩ :=
      (InfiniteGalois.mem_range_algebraMap_iff_fixed y).2 hyFixed
    have hNonsingularQ : source.curve.toAffine.Nonsingular xQ yQ := by
      apply (source.curve.toAffine.baseChange_nonsingular
        (Algebra.ofId ℚ (AlgebraicClosure ℚ)).injective xQ yQ).mp
      rw [Algebra.ofId_apply, Algebra.ofId_apply, hxQ, hyQ]
      exact hPoint
    let rationalPoint : RationalPoints source :=
      WeierstrassCurve.Affine.Point.some xQ yQ hNonsingularQ
    refine ⟨rationalPoint, ?_⟩
    change WeierstrassCurve.Affine.Point.some
        (algebraMap ℚ (AlgebraicClosure ℚ) xQ)
        (algebraMap ℚ (AlgebraicClosure ℚ) yQ) _ =
      WeierstrassCurve.Affine.Point.some x y hPoint
    exact Eq.mpr
      (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _)
      ⟨hxQ, hyQ⟩

namespace RationalKummerBoundaryCochainData

abbrev GlobalKummerH1
    (source : RationalEllipticCurveSource) (n : ℕ) :=
  TopModuleCat.ker
    (HomologicalComplex.homologyMap
      (nTorsionToPointCochainMap source n) 1)

noncomputable def cycle
    {source : RationalEllipticCurveSource} {n : ℕ}
    {P : RationalPoints source}
    (data : RationalKummerBoundaryCochainData source n P) :
    (NTorsionContinuousCochainComplex source n).cycles 1 := by
  let T := NTorsionContinuousCochainComplex source n
  let S := T.sc' 0 1 2
  let zker : TopModuleCat.ker S.g :=
    ⟨data.torsionCochain, data.torsion_cycle⟩
  let zS : S.cycles :=
    (S.isoCyclesOfIsLimit (TopModuleCat.isLimitKer S.g)).hom.hom zker
  exact (T.cyclesIsoSc' 0 1 2 (by simp) (by simp)).inv.hom zS

theorem cycle_iCycles
    {source : RationalEllipticCurveSource} {n : ℕ}
    {P : RationalPoints source}
    (data : RationalKummerBoundaryCochainData source n P) :
    ((NTorsionContinuousCochainComplex source n).iCycles 1).hom data.cycle =
      data.torsionCochain := by
  let T := NTorsionContinuousCochainComplex source n
  let S := T.sc' 0 1 2
  let zker : TopModuleCat.ker S.g :=
    ⟨data.torsionCochain, data.torsion_cycle⟩
  let zS : S.cycles :=
    (S.isoCyclesOfIsLimit (TopModuleCat.isLimitKer S.g)).hom.hom zker
  have hz : data.cycle =
      (T.cyclesIsoSc' 0 1 2 (by simp) (by simp)).inv.hom zS := rfl
  rw [hz]
  have h1 : (T.iCycles 1).hom
      ((T.cyclesIsoSc' 0 1 2 (by simp) (by simp)).inv.hom zS) =
        S.iCycles.hom zS :=
    ConcreteCategory.congr_hom
      (T.cyclesIsoSc'_inv_iCycles 0 1 2 (by simp) (by simp)) zS
  have h2 : S.iCycles.hom zS = (TopModuleCat.kerι S.g).hom zker :=
    ConcreteCategory.congr_hom
      (S.isoCyclesOfIsLimit_hom_iCycles (TopModuleCat.isLimitKer S.g)) zker
  exact h1.trans (h2.trans rfl)

noncomputable def h1Class
    {source : RationalEllipticCurveSource} {n : ℕ}
    {P : RationalPoints source}
    (data : RationalKummerBoundaryCochainData source n P) :
    NTorsionGaloisH1 source n :=
  ((NTorsionContinuousCochainComplex source n).homologyπ 1).hom data.cycle

theorem h1Class_mapsTo_zero
    {source : RationalEllipticCurveSource} {n : ℕ}
    {P : RationalPoints source}
    (data : RationalKummerBoundaryCochainData source n P) :
    (HomologicalComplex.homologyMap
      (nTorsionToPointCochainMap source n) 1).hom data.h1Class = 0 := by
  let T := NTorsionContinuousCochainComplex source n
  let F := GlobalContinuousCochainComplex source
  let coefficient := nTorsionToPointCochainMap source n
  have cyclesMap := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i coefficient 1) data.cycle
  simp only [ConcreteCategory.comp_apply] at cyclesMap
  have targetCycles :
      (HomologicalComplex.cyclesMap coefficient 1).hom data.cycle =
        (F.toCycles 0 1).hom data.zeroCochain := by
    apply homogeneous_iCycles_one_injective (geometricPointTopRep source)
    have toCycles := ConcreteCategory.congr_hom
      (F.toCycles_i 0 1) data.zeroCochain
    simp only [ConcreteCategory.comp_apply] at toCycles
    exact calc
      (F.iCycles 1).hom
          ((HomologicalComplex.cyclesMap coefficient 1).hom data.cycle) =
        (coefficient.f 1).hom ((T.iCycles 1).hom data.cycle) := cyclesMap
      _ = (coefficient.f 1).hom data.torsionCochain := by rw [cycle_iCycles]
      _ = (F.d 0 1).hom data.zeroCochain := data.mapped_eq_boundary
      _ = (F.iCycles 1).hom ((F.toCycles 0 1).hom data.zeroCochain) :=
        toCycles.symm
  have targetHomology :
      (F.homologyπ 1).hom
          ((HomologicalComplex.cyclesMap coefficient 1).hom data.cycle) = 0 := by
    rw [targetCycles]
    have zero := ConcreteCategory.congr_hom
      (F.toCycles_comp_homologyπ 0 1) data.zeroCochain
    simp only [ConcreteCategory.comp_apply] at zero
    exact zero.trans rfl
  have naturality := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality coefficient 1) data.cycle
  simp only [ConcreteCategory.comp_apply] at naturality
  exact naturality.trans targetHomology

noncomputable def kummerClass
    {source : RationalEllipticCurveSource} {n : ℕ}
    {P : RationalPoints source}
    (data : RationalKummerBoundaryCochainData source n P) :
    GlobalKummerH1 source n :=
  ⟨data.h1Class, data.h1Class_mapsTo_zero⟩

theorem h1Class_independent
    {source : RationalEllipticCurveSource} {n : ℕ}
    {P : RationalPoints source}
    (data₁ data₂ : RationalKummerBoundaryCochainData source n P) :
    data₁.h1Class = data₂.h1Class := by
  let X := geometricNTorsionIntTopRep source n
  let T := NTorsionContinuousCochainComplex source n
  let F := GlobalContinuousCochainComplex source
  let differencePointCochain : F.X 0 :=
    data₁.zeroCochain - data₂.zeroCochain
  have difference_torsion (sigma : Field.absoluteGaloisGroup ℚ) :
      n • differencePointCochain.1 sigma = 0 := by
    have hdiff : differencePointCochain.1 sigma =
        data₁.zeroCochain.1 sigma - data₂.zeroCochain.1 sigma := rfl
    rw [hdiff, data₁.zeroCochain_apply, data₂.zeroCochain_apply, nsmul_sub]
    change n • geometricPointGaloisMap source sigma data₁.divisionPoint -
        n • geometricPointGaloisMap source sigma data₂.divisionPoint = 0
    rw [← AddMonoidHom.map_nsmul, ← AddMonoidHom.map_nsmul,
      data₁.divides, data₂.divides,
      rationalPointToGeometric_galois_fixed, sub_self]
  let torsionValue (sigma : Field.absoluteGaloisGroup ℚ) :
      GeometricNTorsion source n :=
    ⟨differencePointCochain.1 sigma,
      AddSubgroup.torsionBy.nsmul_iff.mpr (difference_torsion sigma)⟩
  let inclusion : C(GeometricNTorsion source n,
      TopRep.resolutionX (geometricPointTopRep source) 0) :=
    ⟨fun point ↦ point.1,
      (geometricNTorsionToGeometricPointContinuousLinearMap source n).continuous⟩
  have inclusionEmbedding : Topology.IsEmbedding inclusion := by
    refine ⟨⟨?_⟩, Subtype.val_injective⟩
    exact geometricNTorsion_topology_eq_induced source n
  have torsionValueContinuous : Continuous torsionValue := by
    apply inclusionEmbedding.continuous_iff.mpr
    have heq : inclusion ∘ torsionValue = fun sigma ↦ differencePointCochain.1 sigma := by
      funext sigma
      rfl
    rw [heq]
    exact differencePointCochain.1.continuous
  let torsionMap : C(Field.absoluteGaloisGroup ℚ, GeometricNTorsion source n) :=
    ⟨torsionValue, torsionValueContinuous⟩
  have torsionInvariant :
      torsionMap ∈ (X.resolution'.X 0).ρ.invariants := by
    intro t
    ext sigma
    apply Subtype.ext
    have h := DFunLike.ext_iff.1 (differencePointCochain.2 t) sigma
    exact h
  let torsionZeroCochain : T.X 0 := ⟨torsionMap, torsionInvariant⟩
  have hboundary :
      (T.iCycles 1).hom (data₁.cycle - data₂.cycle) =
        (T.d 0 1).hom torsionZeroCochain := by
    rw [map_sub, cycle_iCycles, cycle_iCycles]
    apply Subtype.ext
    apply ContinuousMap.ext
    intro sigma
    apply ContinuousMap.ext
    intro tau
    apply Subtype.ext
    have heval₁ := congrArg (fun cochain ↦ cochain.1 sigma tau)
      data₁.mapped_eq_boundary
    have heval₂ := congrArg (fun cochain ↦ cochain.1 sigma tau)
      data₂.mapped_eq_boundary
    have hboundary₁ := homogeneousZeroBoundary_apply
      (geometricPointTopRep source) data₁.zeroCochain sigma tau
    have hboundary₂ := homogeneousZeroBoundary_apply
      (geometricPointTopRep source) data₂.zeroCochain sigma tau
    have hz₁ : (data₁.torsionCochain.1 sigma tau).1 =
        data₁.zeroCochain.1 tau - data₁.zeroCochain.1 sigma := by
      exact heval₁.trans hboundary₁
    have hz₂ : (data₂.torsionCochain.1 sigma tau).1 =
        data₂.zeroCochain.1 tau - data₂.zeroCochain.1 sigma := by
      exact heval₂.trans hboundary₂
    have hqt := homogeneousZeroBoundary_apply
      X torsionZeroCochain sigma tau
    have hqtVal := congrArg Subtype.val hqt
    change (data₁.torsionCochain.1 sigma tau).1 -
        (data₂.torsionCochain.1 sigma tau).1 =
      (((T.d 0 1).hom torsionZeroCochain).1 sigma tau).1
    rw [hz₁, hz₂, hqtVal]
    change
      (data₁.zeroCochain.1 tau - data₁.zeroCochain.1 sigma) -
          (data₂.zeroCochain.1 tau - data₂.zeroCochain.1 sigma) =
        (data₁.zeroCochain.1 tau - data₂.zeroCochain.1 tau) -
          (data₁.zeroCochain.1 sigma - data₂.zeroCochain.1 sigma)
    abel
  exact homogeneous_pi_eq_of_sub_iCycles_eq_d X
    data₁.cycle data₂.cycle torsionZeroCochain hboundary

noncomputable def sourceGeneratedRationalKummerClass
    (source : RationalEllipticCurveSource)
    (n : ℕ) (hn : 0 < n) (P : RationalPoints source) :
    GlobalKummerH1 source n :=
  (sourceGeneratedRationalKummerBoundaryCochain source n hn P).kummerClass

theorem sourceGeneratedRationalKummerClass_eq_zero_of_divisible
    (source : RationalEllipticCurveSource)
    (n : ℕ) (hn : 0 < n) (P R : RationalPoints source)
    (hR : n • R = P) :
    sourceGeneratedRationalKummerClass source n hn P = 0 := by
  let geometricR := rationalPointToGeometric source R
  have orbitContinuous : Continuous
      (fun sigma : Field.absoluteGaloisGroup ℚ ↦
        (geometricPointTopRep source).ρ sigma geometricR) := by
    change Continuous
      (fun sigma : Field.absoluteGaloisGroup ℚ ↦ sigma • geometricR)
    exact continuous_smul.comp (continuous_id.prodMk continuous_const)
  let qR : (TopRep.homogeneousCochains (geometricPointTopRep source)).X 0 :=
    orbitZeroCochain (geometricPointTopRep source) geometricR orbitContinuous
  have qRBoundary :
      ((TopRep.homogeneousCochains
        (geometricPointTopRep source)).d 0 1).hom qR = 0 := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro sigma
    apply ContinuousMap.ext
    intro tau
    rw [homogeneousZeroBoundary_apply]
    have hTau : qR.1 tau = (geometricPointTopRep source).ρ tau geometricR := by
      dsimp only [qR]
      exact orbitZeroCochain_apply (geometricPointTopRep source)
        geometricR orbitContinuous tau
    have hSigma : qR.1 sigma = (geometricPointTopRep source).ρ sigma geometricR := by
      dsimp only [qR]
      exact orbitZeroCochain_apply (geometricPointTopRep source)
        geometricR orbitContinuous sigma
    rw [hTau, hSigma]
    change geometricPointGaloisMap source tau geometricR -
      geometricPointGaloisMap source sigma geometricR = 0
    dsimp only [geometricR]
    rw [rationalPointToGeometric_galois_fixed,
      rationalPointToGeometric_galois_fixed, sub_self]
  let reference : RationalKummerBoundaryCochainData source n P :=
    { divisionPoint := geometricR
      divides := by
        dsimp only [geometricR]
        rw [← map_nsmul, hR]
      zeroCochain := qR
      zeroCochain_apply := fun sigma ↦
        orbitZeroCochain_apply (geometricPointTopRep source)
          geometricR orbitContinuous sigma
      torsionCochain := 0
      torsion_cycle := map_zero _
      mapped_eq_boundary := by rw [map_zero, qRBoundary] }
  let generated := sourceGeneratedRationalKummerBoundaryCochain source n hn P
  have hindependent : generated.h1Class = reference.h1Class :=
    h1Class_independent generated reference
  have hreferenceCycle : reference.cycle = 0 := by
    apply homogeneous_iCycles_one_injective
      (geometricNTorsionIntTopRep source n)
    rw [cycle_iCycles, map_zero]
  have hreference : reference.h1Class = 0 := by
    rw [h1Class, hreferenceCycle, map_zero]
  apply Subtype.ext
  exact hindependent.trans hreference

theorem kummerClass_eq_zero_implies_divisible
    {source : RationalEllipticCurveSource} {n : ℕ}
    {P : RationalPoints source}
    (data : RationalKummerBoundaryCochainData source n P)
    (hzero : data.kummerClass = 0) :
    ∃ R : RationalPoints source, n • R = P := by
  have hClassZero : data.h1Class = 0 := by
    have h := congrArg
      (fun x : GlobalKummerH1 source n ↦ x.1) hzero
    exact h
  obtain ⟨qT, hqT⟩ := exists_homogeneousBoundary_of_h1_eq_zero
    source n data.cycle hClassZero
  let T := NTorsionContinuousCochainComplex source n
  let F := GlobalContinuousCochainComplex source
  let coefficient := nTorsionToPointCochainMap source n
  let qTPoint : F.X 0 := (coefficient.f 0).hom qT
  have mappedTorsionBoundary :
      (F.d 0 1).hom qTPoint = (F.d 0 1).hom data.zeroCochain := by
    have commutes := ConcreteCategory.congr_hom (coefficient.comm 0 1) qT
    simp only [ConcreteCategory.comp_apply] at commutes
    calc
      (F.d 0 1).hom qTPoint =
          (coefficient.f 1).hom ((T.d 0 1).hom qT) := commutes
      _ = (coefficient.f 1).hom ((T.iCycles 1).hom data.cycle) := by rw [hqT]
      _ = (coefficient.f 1).hom data.torsionCochain := by rw [cycle_iCycles]
      _ = (F.d 0 1).hom data.zeroCochain := data.mapped_eq_boundary
  let fixedCochain : F.X 0 := data.zeroCochain - qTPoint
  have fixedCochain_boundary : (F.d 0 1).hom fixedCochain = 0 := by
    dsimp only [fixedCochain]
    rw [map_sub, mappedTorsionBoundary, sub_self]
  let fixedPoint : GeometricPoints source := fixedCochain.1 1
  let zeroBasePoint : GeometricPoints source := data.zeroCochain.1 1
  let torsionCorrectionPoint : GeometricPoints source := qTPoint.1 1
  have fixedPoint_fixed (sigma : Field.absoluteGaloisGroup ℚ) :
      geometricPointGaloisMap source sigma fixedPoint = fixedPoint := by
    have haction := homogeneousZeroCochain_apply_eq_action
      (geometricPointTopRep source) fixedCochain sigma
    have heval := congrArg (fun cochain ↦ cochain.1 1 sigma)
      fixedCochain_boundary
    have hboundary := homogeneousZeroBoundary_apply
      (geometricPointTopRep source) fixedCochain 1 sigma
    have hdiff : fixedCochain.1 sigma - fixedCochain.1 1 = 0 := by
      rw [← hboundary]
      exact heval
    change (geometricPointTopRep source).ρ sigma fixedPoint = fixedPoint
    rw [← haction]
    exact sub_eq_zero.mp hdiff
  have fixedPoint_eq :
      fixedPoint = data.divisionPoint - torsionCorrectionPoint := by
    have hbase : zeroBasePoint = data.divisionPoint := by
      dsimp only [zeroBasePoint]
      rw [data.zeroCochain_apply]
      change geometricPointGaloisMap source 1 data.divisionPoint =
        data.divisionPoint
      change (1 : Field.absoluteGaloisGroup ℚ) • data.divisionPoint =
        data.divisionPoint
      exact one_smul _ data.divisionPoint
    calc
      fixedPoint = zeroBasePoint - torsionCorrectionPoint := by rfl
      _ = data.divisionPoint - torsionCorrectionPoint := by rw [hbase]
  have qTPoint_torsion : n • torsionCorrectionPoint = 0 := by
    dsimp only [torsionCorrectionPoint, qTPoint]
    change n • (qT.1 1).1 = 0
    exact AddSubgroup.torsionBy.nsmul_iff.mp (qT.1 1).property
  have fixedPoint_multiple :
      n • fixedPoint = rationalPointToGeometric source P := by
    rw [fixedPoint_eq, nsmul_sub, data.divides, qTPoint_torsion, sub_zero]
  obtain ⟨R, hR⟩ :=
    exists_rationalPoint_of_geometric_galoisFixed source fixedPoint fixedPoint_fixed
  refine ⟨R, rationalPointToGeometric_injective source ?_⟩
  rw [map_nsmul, hR, fixedPoint_multiple]

theorem sourceGeneratedRationalKummerClass_eq_zero_iff
    (source : RationalEllipticCurveSource)
    (n : ℕ) (hn : 0 < n) (P : RationalPoints source) :
    sourceGeneratedRationalKummerClass source n hn P = 0 ↔
      ∃ R : RationalPoints source, n • R = P := by
  constructor
  · intro hzero
    exact kummerClass_eq_zero_implies_divisible
      (sourceGeneratedRationalKummerBoundaryCochain source n hn P) hzero
  · rintro ⟨R, hR⟩
    exact sourceGeneratedRationalKummerClass_eq_zero_of_divisible
      source n hn P R hR

theorem sourceGeneratedRationalKummerClass_sub
    (source : RationalEllipticCurveSource)
    (n : ℕ) (hn : 0 < n) (P Q : RationalPoints source) :
    sourceGeneratedRationalKummerClass source n hn P -
        sourceGeneratedRationalKummerClass source n hn Q =
      sourceGeneratedRationalKummerClass source n hn (P - Q) := by
  let dataP := sourceGeneratedRationalKummerBoundaryCochain source n hn P
  let dataQ := sourceGeneratedRationalKummerBoundaryCochain source n hn Q
  let differenceData : RationalKummerBoundaryCochainData source n (P - Q) :=
    { divisionPoint := dataP.divisionPoint - dataQ.divisionPoint
      divides := by
        rw [nsmul_sub, dataP.divides, dataQ.divides, ← map_sub]
      zeroCochain := dataP.zeroCochain - dataQ.zeroCochain
      zeroCochain_apply := fun sigma ↦ by
        have hP := dataP.zeroCochain_apply sigma
        have hQ := dataQ.zeroCochain_apply sigma
        change dataP.zeroCochain.1 sigma - dataQ.zeroCochain.1 sigma = _
        rw [hP, hQ]
        exact (((geometricPointTopRep source).ρ sigma).map_sub
          dataP.divisionPoint dataQ.divisionPoint).symm
      torsionCochain := dataP.torsionCochain - dataQ.torsionCochain
      torsion_cycle := by
        rw [map_sub, dataP.torsion_cycle, dataQ.torsion_cycle, sub_self]
      mapped_eq_boundary := by
        rw [map_sub, dataP.mapped_eq_boundary, dataQ.mapped_eq_boundary,
          map_sub] }
  let generatedDifference :=
    sourceGeneratedRationalKummerBoundaryCochain source n hn (P - Q)
  have hindependent : generatedDifference.h1Class = differenceData.h1Class :=
    h1Class_independent generatedDifference differenceData
  have hcycle : differenceData.cycle = dataP.cycle - dataQ.cycle := by
    apply homogeneous_iCycles_one_injective
      (geometricNTorsionIntTopRep source n)
    rw [cycle_iCycles, map_sub, cycle_iCycles, cycle_iCycles]
  apply Subtype.ext
  change dataP.h1Class - dataQ.h1Class = generatedDifference.h1Class
  rw [hindependent, h1Class, h1Class, h1Class, hcycle, map_sub]

noncomputable def rationalKummerAddHom
    (source : RationalEllipticCurveSource)
    (n : ℕ) (hn : 0 < n) :
    RationalPoints source →+ GlobalKummerH1 source n where
  toFun := sourceGeneratedRationalKummerClass source n hn
  map_zero' := by
    have hsub := sourceGeneratedRationalKummerClass_sub source n hn 0 0
    simpa only [sub_self] using hsub.symm
  map_add' P Q := by
    have hsub := sourceGeneratedRationalKummerClass_sub source n hn (P + Q) Q
    have hsub' :
        sourceGeneratedRationalKummerClass source n hn (P + Q) -
            sourceGeneratedRationalKummerClass source n hn Q =
          sourceGeneratedRationalKummerClass source n hn P := by
      simpa only [add_sub_cancel_right] using hsub
    exact sub_eq_iff_eq_add.mp hsub'

theorem rationalKummerAddHom_ker
    (source : RationalEllipticCurveSource)
    (n : ℕ) (hn : 0 < n) :
    (rationalKummerAddHom source n hn).ker =
      (nsmulAddMonoidHom n : RationalPoints source →+ RationalPoints source).range := by
  ext P
  rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
  exact (sourceGeneratedRationalKummerClass_eq_zero_iff source n hn P).trans
    ⟨fun ⟨R, hR⟩ ↦ ⟨R, hR⟩, fun ⟨R, hR⟩ ↦ ⟨R, hR⟩⟩

theorem rationalNsmulRange_finiteIndex_of_finite_globalKummerH1
    (source : RationalEllipticCurveSource)
    (n : ℕ) (hn : 0 < n)
    [Finite (GlobalKummerH1 source n)] :
    (nsmulAddMonoidHom n :
      RationalPoints source →+ RationalPoints source).range.FiniteIndex := by
  let delta := rationalKummerAddHom source n hn
  have hker : delta.ker.FiniteIndex := AddSubgroup.finiteIndex_ker delta
  rw [rationalKummerAddHom_ker source n hn] at hker
  exact hker

theorem rationalMordellWeil_fg_of_finite_globalTwoKummerH1
    (source : RationalEllipticCurveSource)
    [Finite (GlobalKummerH1 source 2)] :
    AddGroup.FG (RationalPoints source) :=
  rationalMordellWeil_fg_of_finiteIndex source
    (rationalNsmulRange_finiteIndex_of_finite_globalKummerH1
      source 2 (by norm_num))

end RationalKummerBoundaryCochainData

end

end UniversalBSDRationalKummerCohomology
end SaturationMonoid

