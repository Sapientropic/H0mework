import H0mework.Physics.LowEnergyMatterSpace.GaugeForce
import H0mework.Physics.LowEnergyKinetic.Density

/-! The source's full independent dual graph and kinetic pairing on spatial fibers. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
open DiracCliffordRepresentation DiracExteriorMatterAction ActiveSector
open SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction
open StageNineFullDiracAdjointMaterial Stage9C.Material.SpinPair Fermion
open scoped Matrix Kronecker InnerProductSpace
noncomputable section
attribute [local instance] instLinearOrderSourceIndex

theorem triplet_internal_pair (u : Fin 3 → ℂ) (v : SU7ExteriorSpinorMatterCarrier) :
    fullInternalPair (∑ color, u color • colorTripletMatter color) v=
      ∑ color, star (u color)*(su7ExteriorBasis 2).coord (colorTripletIndex color) v.2.1 := by
  have singlePair (index : ExteriorBasisIndex 2) (z : ℂ) :
      (∑ x, starRingEnd ℂ ((Finsupp.single index z) x)*(su7ExteriorBasis 2).repr v.2.1 x)=
        starRingEnd ℂ z*(su7ExteriorBasis 2).repr v.2.1 index := by
    rw [Finset.sum_eq_single index]
    · simp
    · intro other _ different
      simp [different]
    · simp
  simp [Fin.sum_univ_three,fullInternalPair,exteriorCoordinatePair,colorTripletMatter,
    add_mul,Finset.sum_add_distrib,singlePair]

theorem triplet_coordinate_pair (u v : SourceIndex → ℂ) :
    Quantum.coordinatePair (tripletLift u) (tripletLift v)=∑ index, star (u index)*v index := by
  rw [Quantum.coordinatePair_full]
  change (∑ spin, fullInternalPair (∑ color, u (spin,color) • colorTripletMatter color)
    (tripletLift v spin))=_
  simp only [triplet_internal_pair,tripletLift_coordinate,Fintype.sum_prod_type]

theorem triplet_euclidean_pair (u v : MatterFiber) :
    Quantum.coordinatePair (tripletLift u) (tripletLift v)=inner ℂ u v := by
  rw [triplet_coordinate_pair,EuclideanSpace.inner_eq_star_dotProduct]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

theorem triplet_spin_lift (A : DiracMatrix) (v : SourceIndex → ℂ) :
    tripletLift ((A ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ))*ᵥv)=
      diracMatrixMatterAction A (tripletLift v) := by
  rw [tripletLift_tensor]
  simp [tripletLift,Matrix.one_apply]

theorem triplet_kinetic_pair (density : ℝ) (u v : MatterFiber) :
    Kinetic.kineticPair density (tripletLift u) (tripletLift v)=
      (density : ℂ)*inner ℂ u (hamiltonianOperator sourceCharge v) := by
  rw [Kinetic.kineticPair,← triplet_spin_lift,triplet_coordinate_pair]
  congr 1
  change _ = inner ℂ u ((Matrix.toEuclideanCLM (n := SourceIndex) (𝕜 := ℂ)) sourceCharge v)
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ i, star (u i)*(sourceCharge*ᵥ(fun j => v j)) i)=
    ∑ i, (sourceCharge*ᵥ(fun j => v j)) i*star (u i)
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

def sourceExchange : SourceMatrix := diracAdjointSpinSwap ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ)

theorem triplet_canonical_dual (u v : MatterFiber) :
    fullCanonicalDiracAdjoint (tripletLift u) (tripletLift v)=
      inner ℂ u (hamiltonianOperator sourceExchange v) := by
  rw [Quantum.canonicalDual_full_response,Quantum.spinExchange_selfAdjoint]
  change Quantum.coordinatePair (tripletLift u)
    (diracMatrixMatterAction diracAdjointSpinSwap (tripletLift v))=_
  rw [← triplet_spin_lift]
  exact triplet_euclidean_pair u (hamiltonianOperator sourceExchange v)

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
