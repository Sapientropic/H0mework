import H0mework.Versions.AB.Physics.LowEnergyMatterSpace.DualPairing
import H0mework.Versions.R3bbcbd59.Physics.LowEnergyActive.Projection
import H0mework.Physics.Dirac.FullDiracAdjointLocalOperator

/-! The original exterior-triplet projection is orthogonal and reduces every
source P286 action; its two-sided law is generated from source skew pairing. -/
set_option autoImplicit false
open scoped Matrix
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.FullCurrentSymbol
open DiracExteriorMatterAction SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction
open ActiveSector MatterSpace StageNineFullDiracAdjointLocalOperator SU7MotherLieAlgebra
open SU7ExteriorBreakingYukawa StageNineHolonomicField
noncomputable section
local instance projectIndex : DecidableEq Quantum.Index := Classical.decEq _

def tripletRestrict : DiracExteriorMatterCarrier →ₗ[ℂ] (SourceIndex → ℂ) where
  toFun v index := (su7ExteriorBasis 2).coord (colorTripletIndex index.2) (v index.1).2.1
  map_add' u v := by ext index; simp
  map_smul' z v := by ext index; simp

theorem restrict_lift (v : SourceIndex → ℂ) : tripletRestrict (tripletLift v)=v := by
  ext index
  exact tripletLift_coordinate v index.1 index.2

theorem lift_restrict (v : DiracExteriorMatterCarrier) : tripletLift (tripletRestrict v)=projection v := rfl

theorem projection_pair_left (u v : DiracExteriorMatterCarrier) :
    Quantum.coordinatePair (projection u) v=Fermion.modePair (tripletRestrict u) (tripletRestrict v) := by
  rw [Quantum.coordinatePair_full]
  change (∑ spin, StageNineFullDiracAdjointMaterial.fullInternalPair
    (∑ color, tripletRestrict u (spin,color) • colorTripletMatter color) (v spin))=_
  simp only [triplet_internal_pair,Fermion.modePair,Fintype.sum_prod_type]
  rfl

private theorem pair_star (u v : DiracExteriorMatterCarrier) :
    star (Quantum.coordinatePair v u)=Quantum.coordinatePair u v := by
  simp only [Quantum.coordinatePair,star_sum,star_mul,star_star]

theorem projection_pair (u v : DiracExteriorMatterCarrier) :
    Quantum.coordinatePair (projection u) v=Quantum.coordinatePair u (projection v) := by
  rw [← pair_star u (projection v),projection_pair_left,projection_pair_left]
  simp only [Fermion.modePair,star_sum,star_mul,star_star]

theorem coordinate_pair_ext (u v : DiracExteriorMatterCarrier)
    (same : ∀ w, Quantum.coordinatePair w u=Quantum.coordinatePair w v) : u=v := by
  apply Quantum.coordinates.injective
  ext index
  have tested := same (Quantum.coordinates.symm (Pi.single index 1))
  simpa [Quantum.coordinatePair,Pi.single_apply] using tested

theorem gauge_projection_right (data : P286LieBlockData) (v : DiracExteriorMatterCarrier) :
    projection (diracExteriorMotherLieAction (p286LieBlockEmbed data) (projection v))=
      diracExteriorMotherLieAction (p286LieBlockEmbed data) (projection v) := by
  change projection (diracExteriorMotherLieAction (p286LieBlockEmbed data)
    (tripletMatter (fun spin color => tripletRestrict v (spin,color))))=
    diracExteriorMotherLieAction (p286LieBlockEmbed data)
      (tripletMatter (fun spin color => tripletRestrict v (spin,color)))
  simp only [original_P286_triplet,projection_triplet]

private theorem gauge_pair (data : P286LieBlockData) (u v : DiracExteriorMatterCarrier) :
    Quantum.coordinatePair (diracExteriorMotherLieAction (p286LieBlockEmbed data) u) v+
      Quantum.coordinatePair u (diracExteriorMotherLieAction (p286LieBlockEmbed data) v)=0 := by
  simp only [Quantum.coordinatePair_full,← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro spin _
  exact fullInternalPair_motherLie_skew (p286LieBlockEmbed data) (u spin) (v spin)

theorem projection_gauge (data : P286LieBlockData) :
    projection.comp (diracExteriorMotherLieAction (p286LieBlockEmbed data))=
      (diracExteriorMotherLieAction (p286LieBlockEmbed data)).comp projection := by
  apply LinearMap.ext
  intro v
  apply coordinate_pair_ext
  intro u
  change Quantum.coordinatePair u (projection (diracExteriorMotherLieAction (p286LieBlockEmbed data) v))=
    Quantum.coordinatePair u (diracExteriorMotherLieAction (p286LieBlockEmbed data) (projection v))
  calc
    _ = Quantum.coordinatePair (projection u) (diracExteriorMotherLieAction (p286LieBlockEmbed data) v) :=
      (projection_pair u _).symm
    _ = -Quantum.coordinatePair (diracExteriorMotherLieAction (p286LieBlockEmbed data) (projection u)) v :=
      eq_neg_of_add_eq_zero_right (gauge_pair data (projection u) v)
    _ = -Quantum.coordinatePair (projection (diracExteriorMotherLieAction (p286LieBlockEmbed data) (projection u))) v := by
      rw [gauge_projection_right]
    _ = -Quantum.coordinatePair (diracExteriorMotherLieAction (p286LieBlockEmbed data) (projection u)) (projection v) := by
      rw [projection_pair]
    _ = Quantum.coordinatePair (projection u) (diracExteriorMotherLieAction (p286LieBlockEmbed data) (projection v)) :=
      (eq_neg_of_add_eq_zero_right (gauge_pair data (projection u) (projection v))).symm
    _ = Quantum.coordinatePair u (projection (diracExteriorMotherLieAction (p286LieBlockEmbed data) (projection v))) :=
      projection_pair u _
    _ = _ := by rw [gauge_projection_right]

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.FullCurrentSymbol
