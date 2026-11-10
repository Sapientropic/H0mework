import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The gauge-group quantifier uses the group's actual tangent Lie algebra.
No condition is imposed on its finite centre or on an independent quantum object. -/

set_option autoImplicit false
open scoped Manifold ContDiff

namespace SaturationMonoid.PhysicsCore.YangMills.Terminal

noncomputable section

universe u

private instance : ENat.LEInfty (minSmoothness ℝ 3) := ⟨by simpa only [minSmoothness_of_isRCLikeNormedField] using (ENat.LEInfty.out (m := (3 : ℕ∞ω)))⟩

structure GaugeGroup where
  Model : Type u
  Carrier : Type u
  [modelNorm : NormedAddCommGroup Model]
  [modelSpace : NormedSpace ℝ Model]
  [modelFinite : FiniteDimensional ℝ Model]
  [group : Group Carrier]
  [topology : TopologicalSpace Carrier]
  [charted : ChartedSpace Model Carrier]
  [hausdorff : T2Space Carrier]
  [compact : CompactSpace Carrier]
  [connected : ConnectedSpace Carrier]
  [lie : LieGroup 𝓘(ℝ, Model) ∞ Carrier]
  [simple : LieAlgebra.IsSimple ℝ (GroupLieAlgebra 𝓘(ℝ, Model) Carrier)]

attribute [instance] GaugeGroup.modelNorm GaugeGroup.modelSpace GaugeGroup.modelFinite
  GaugeGroup.group GaugeGroup.topology GaugeGroup.charted GaugeGroup.hausdorff
  GaugeGroup.compact GaugeGroup.connected GaugeGroup.lie GaugeGroup.simple

namespace GaugeGroup

abbrev Algebra (G : GaugeGroup) := GroupLieAlgebra 𝓘(ℝ, G.Model) G.Carrier

instance (G : GaugeGroup) : NormedAddCommGroup G.Algebra :=
  inferInstanceAs (NormedAddCommGroup G.Model)

instance (G : GaugeGroup) : NormedSpace ℝ G.Algebra :=
  inferInstanceAs (NormedSpace ℝ G.Model)

instance (G : GaugeGroup) : IsTopologicalGroup G.Carrier :=
  topologicalGroup_of_lieGroup 𝓘(ℝ, G.Model) ∞

instance (G : GaugeGroup) : SecondCountableTopology G.Carrier :=
  ChartedSpace.secondCountable_of_sigmaCompact G.Model G.Carrier

theorem algebra_nonabelian (G : GaugeGroup) : ¬ IsLieAbelian G.Algebra :=
  LieAlgebra.IsSimple.non_abelian (R := ℝ) (L := G.Algebra)

def of (E : Type u) (K : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Group K] [TopologicalSpace K] [ChartedSpace E K]
    [T2Space K] [CompactSpace K] [ConnectedSpace K] [LieGroup 𝓘(ℝ, E) ∞ K]
    [LieAlgebra.IsSimple ℝ (GroupLieAlgebra 𝓘(ℝ, E) K)] : GaugeGroup where
  Model := E
  Carrier := K

end GaugeGroup

abbrev GaugeSpacetime := EuclideanSpace ℝ (Fin 4)

instance (G : GaugeGroup) : NormedAddCommGroup (GaugeSpacetime →L[ℝ] G.Algebra) := by
  change NormedAddCommGroup (GaugeSpacetime →L[ℝ] G.Model)
  infer_instance

instance (G : GaugeGroup) : NormedSpace ℝ (GaugeSpacetime →L[ℝ] G.Algebra) := by
  change NormedSpace ℝ (GaugeSpacetime →L[ℝ] G.Model)
  infer_instance

abbrev Connection (G : GaugeGroup) :=
  {A : GaugeSpacetime → (GaugeSpacetime →L[ℝ] G.Algebra) // ContDiff ℝ ∞ A}

def curvature (G : GaugeGroup) (A : Connection G) (x u v : GaugeSpacetime) : G.Algebra :=
  (fderiv ℝ A.val x u) v - (fderiv ℝ A.val x v) u + ⁅A.val x u, A.val x v⁆

def covariantDerivative (G : GaugeGroup) (A : Connection G)
    (field : GaugeSpacetime → G.Algebra) (x u : GaugeSpacetime) : G.Algebra :=
  fderiv ℝ field x u + ⁅A.val x u, field x⁆

end
end SaturationMonoid.PhysicsCore.YangMills.Terminal
