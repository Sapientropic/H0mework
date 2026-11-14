import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.RepresentationTheory.Continuous.TopRep

/-!
# Universal BSD geometric Galois coefficient

For every elliptic curve over `Q`, this module constructs the actual geometric point
carrier over `Qbar`, proves that its coordinate Galois action has open stabilizers, and packages
the resulting jointly continuous integral action as a `TopRep`.  No fixed-CM source is imported.
-/

namespace SaturationMonoid
namespace UniversalBSDGeometricGalois

open CategoryTheory

noncomputable section

/-- An actual elliptic curve over `Q`, with ellipticity stored at the source. -/
structure RationalEllipticCurveSource where
  curve : WeierstrassCurve ℚ
  isElliptic : curve.IsElliptic

attribute [instance] RationalEllipticCurveSource.isElliptic

/-- The source curve over the chosen algebraic closure of `Q`. -/
abbrev GeometricCurve (source : RationalEllipticCurveSource) :
    WeierstrassCurve (AlgebraicClosure ℚ) :=
  source.curve.baseChange (AlgebraicClosure ℚ)

instance geometricCurve_isElliptic (source : RationalEllipticCurveSource) :
    (GeometricCurve source).IsElliptic := by
  unfold GeometricCurve WeierstrassCurve.baseChange
  infer_instance

/-- Actual geometric points `E(Qbar)`. -/
abbrev GeometricPoints (source : RationalEllipticCurveSource) :=
  (GeometricCurve source).toAffine.Point

noncomputable instance globalClosureDecidableEq : DecidableEq (AlgebraicClosure ℚ) :=
  Classical.decEq _

local instance globalClosureGaloisSMul :
    SMul (Field.absoluteGaloisGroup ℚ) (AlgebraicClosure ℚ) :=
  ⟨fun sigma x ↦ sigma.toAlgHom x⟩

local instance globalClosureGaloisMulAction :
    MulAction (Field.absoluteGaloisGroup ℚ) (AlgebraicClosure ℚ) where
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- Coordinate action of `G_Q` on actual geometric points. -/
noncomputable def geometricPointGaloisMap
    (source : RationalEllipticCurveSource)
    (sigma : Field.absoluteGaloisGroup ℚ) :
    GeometricPoints source →+ GeometricPoints source :=
  WeierstrassCurve.Affine.Point.map (W' := source.curve) sigma.toAlgHom

theorem geometricPointGaloisMap_comp
    (source : RationalEllipticCurveSource)
    (sigma tau : Field.absoluteGaloisGroup ℚ)
    (point : GeometricPoints source) :
    geometricPointGaloisMap source (sigma * tau) point =
      geometricPointGaloisMap source sigma
        (geometricPointGaloisMap source tau point) := by
  simp only [geometricPointGaloisMap]
  rw [WeierstrassCurve.Affine.Point.map_map]
  rfl

instance geometricPointsGaloisSMul
    (source : RationalEllipticCurveSource) :
    SMul (Field.absoluteGaloisGroup ℚ) (GeometricPoints source) :=
  ⟨fun sigma point ↦ geometricPointGaloisMap source sigma point⟩

instance geometricPointsGaloisMulAction
    (source : RationalEllipticCurveSource) :
    MulAction (Field.absoluteGaloisGroup ℚ) (GeometricPoints source) where
  one_smul point := by
    rcases point with (_ | ⟨x, y, hpoint⟩) <;> rfl
  mul_smul sigma tau point := geometricPointGaloisMap_comp source sigma tau point

instance geometricPointsTopology (source : RationalEllipticCurveSource) :
    TopologicalSpace (GeometricPoints source) := ⊥

instance geometricPointsDiscreteTopology (source : RationalEllipticCurveSource) :
    DiscreteTopology (GeometricPoints source) := ⟨rfl⟩

instance geometricPointsContinuousIntSMul (source : RationalEllipticCurveSource) :
    ContinuousSMul ℤ (GeometricPoints source) :=
  ⟨continuous_of_discreteTopology⟩

/-- Every actual geometric point has an open absolute-Galois stabilizer. -/
theorem geometricPoints_stabilizer_isOpen
    (source : RationalEllipticCurveSource)
    (point : GeometricPoints source) :
    IsOpen
      (MulAction.stabilizer (Field.absoluteGaloisGroup ℚ) point :
        Set (Field.absoluteGaloisGroup ℚ)) := by
  rcases point with (_ | ⟨x, y, hpoint⟩)
  · have htop :
        (MulAction.stabilizer (Field.absoluteGaloisGroup ℚ)
          (WeierstrassCurve.Affine.Point.zero : GeometricPoints source) :
            Set (Field.absoluteGaloisGroup ℚ)) = Set.univ := by
      ext sigma
      simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff,
        Set.mem_univ, iff_true]
      rfl
    rw [htop]
    exact isOpen_univ
  · have hx : IsOpen
        (MulAction.stabilizer (Field.absoluteGaloisGroup ℚ) x :
          Set (Field.absoluteGaloisGroup ℚ)) :=
      stabilizer_isOpen_of_isIntegral x
    have hy : IsOpen
        (MulAction.stabilizer (Field.absoluteGaloisGroup ℚ) y :
          Set (Field.absoluteGaloisGroup ℚ)) :=
      stabilizer_isOpen_of_isIntegral y
    have hcoordinates :
        (MulAction.stabilizer (Field.absoluteGaloisGroup ℚ)
            (WeierstrassCurve.Affine.Point.some x y hpoint) :
          Set (Field.absoluteGaloisGroup ℚ)) =
        (MulAction.stabilizer (Field.absoluteGaloisGroup ℚ) x : Set _) ∩
          (MulAction.stabilizer (Field.absoluteGaloisGroup ℚ) y : Set _) := by
      ext sigma
      simp only [Set.mem_inter_iff, SetLike.mem_coe, MulAction.mem_stabilizer_iff]
      change
        WeierstrassCurve.Affine.Point.some (sigma.toAlgHom x)
            (sigma.toAlgHom y) _ =
            WeierstrassCurve.Affine.Point.some x y hpoint ↔
          sigma.toAlgHom x = x ∧ sigma.toAlgHom y = y
      constructor
      · intro h
        exact WeierstrassCurve.Affine.Point.some.inj h
      · rintro ⟨hx, hy⟩
        simpa only [WeierstrassCurve.Affine.Point.some.injEq] using
          (And.intro hx hy)
    rw [hcoordinates]
    exact hx.inter hy

instance geometricPointsContinuousGaloisSMul
    (source : RationalEllipticCurveSource) :
    ContinuousSMul (Field.absoluteGaloisGroup ℚ) (GeometricPoints source) :=
  continuousSMul_iff_stabilizer_isOpen.mpr
    (geometricPoints_stabilizer_isOpen source)

noncomputable def geometricPointGaloisContinuousLinearMap
    (source : RationalEllipticCurveSource)
    (sigma : Field.absoluteGaloisGroup ℚ) :
    GeometricPoints source →L[ℤ] GeometricPoints source :=
  ContinuousLinearMap.mk
    (geometricPointGaloisMap source sigma).toIntLinearMap
    continuous_of_discreteTopology

noncomputable def geometricPointGaloisMonoidHom
    (source : RationalEllipticCurveSource) :
    Field.absoluteGaloisGroup ℚ →*
      (GeometricPoints source →L[ℤ] GeometricPoints source) where
  toFun := geometricPointGaloisContinuousLinearMap source
  map_one' := by
    ext point
    rcases point with (_ | ⟨x, y, hpoint⟩) <;> rfl
  map_mul' sigma tau := by
    ext point
    exact geometricPointGaloisMap_comp source sigma tau point

/-- Universal actual geometric coefficient representation `E(Qbar)` for every `E/Q`. -/
noncomputable def geometricPointTopRep
    (source : RationalEllipticCurveSource) :
    TopRep ℤ (Field.absoluteGaloisGroup ℚ) :=
  TopRep.of (ContRepresentation.ofMonoidHom
    (geometricPointGaloisMonoidHom source))

@[simp]
theorem geometricPointTopRep_rho_apply
    (source : RationalEllipticCurveSource)
    (sigma : Field.absoluteGaloisGroup ℚ)
    (point : GeometricPoints source) :
    (geometricPointTopRep source).ρ sigma point = sigma • point :=
  rfl

/-- The representation action is definitionally the source-coordinate Galois map. -/
@[simp]
theorem geometricPointTopRep_rho_apply_explicit
    (source : RationalEllipticCurveSource)
    (sigma : Field.absoluteGaloisGroup ℚ)
    (point : GeometricPoints source) :
    (geometricPointTopRep source).ρ sigma point =
      geometricPointGaloisMap source sigma point :=
  rfl

/-- Multiplication by `a` on the actual full geometric-point coefficient. -/
noncomputable def geometricPointNsmulContinuousLinearMap
    (source : RationalEllipticCurveSource) (a : ℕ) :
    GeometricPoints source →L[ℤ] GeometricPoints source :=
  ContinuousLinearMap.mk
    (nsmulAddMonoidHom a).toIntLinearMap continuous_of_discreteTopology

/-- Multiplication by `a` as a Galois-equivariant endomorphism of `E(Qbar)`. -/
noncomputable def geometricPointNsmulTopRepHom
    (source : RationalEllipticCurveSource) (a : ℕ) :
    geometricPointTopRep source ⟶ geometricPointTopRep source :=
  TopRep.ofHom ⟨
    geometricPointNsmulContinuousLinearMap source a,
    by
      intro sigma
      ext point
      simpa [geometricPointNsmulContinuousLinearMap, geometricPointTopRep,
        geometricPointGaloisMonoidHom,
        geometricPointGaloisContinuousLinearMap] using
        (AddMonoidHom.map_nsmul
          (geometricPointGaloisMap source sigma) a point).symm
  ⟩

end

end UniversalBSDGeometricGalois
end SaturationMonoid
