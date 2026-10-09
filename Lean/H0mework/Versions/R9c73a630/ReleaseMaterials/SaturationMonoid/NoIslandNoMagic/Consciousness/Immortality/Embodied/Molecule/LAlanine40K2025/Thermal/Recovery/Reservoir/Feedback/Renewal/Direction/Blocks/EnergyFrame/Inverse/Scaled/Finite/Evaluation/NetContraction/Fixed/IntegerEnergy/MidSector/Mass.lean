import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidSector.Address
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidStage.PhysicalEnergy
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

/-! The complete original mid-sector is the disjoint union of the 36 two-orientation bodies. -/

private theorem mid_anchor_injective : Function.Injective midAnchor := by
  intro a b h
  exact Fin.ext (congrArg (fun x : Basis => x.val) h)

private theorem mid_partner_injective : Function.Injective midPartner := by
  intro a b h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change 6+a.val = 6+b.val at hv
  omega

private theorem mid_anchor_ne_partner (a : Fin 2) (b : Fin 18) :
    midAnchor a ≠ midPartner b := by
  intro h
  have hv := congrArg Fin.val h
  change a.val = 6+b.val at hv
  omega

def midSectorEmbedding (s : (Fin 2 × Fin 18) × Fin 2) :
    PairSector (fun p => midCond p.1 p.2) :=
  ⟨if s.2=0 then (midAnchor s.1.1,midPartner s.1.2)
    else (midPartner s.1.2,midAnchor s.1.1), by
    split_ifs
    · exact mid_address_sector _ _
    · have h := mid_address_sector s.1.1 s.1.2
      exact Or.symm h⟩

theorem mid_sector_embedding_bijective : Function.Bijective midSectorEmbedding := by
  constructor
  · rintro ⟨⟨a,b⟩,o⟩ ⟨⟨c,d⟩,p⟩ h
    have v := congrArg Subtype.val h
    fin_cases o <;> fin_cases p
    all_goals norm_num [midSectorEmbedding] at v
    · have ac := mid_anchor_injective v.1
      have bd := mid_partner_injective v.2
      subst c; subst d; rfl
    · exact False.elim (mid_anchor_ne_partner a d v.1)
    · exact False.elim (mid_anchor_ne_partner c b v.1.symm)
    · have bd := mid_partner_injective v.1
      have ac := mid_anchor_injective v.2
      subst c; subst d; rfl
  · rintro ⟨⟨a,b⟩,h⟩
    change midCond a b at h
    rcases h with h | h
    · refine ⟨((⟨a.val,h.1⟩,⟨b.val-6,by omega⟩),0),?_⟩
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · apply Fin.ext
        change 6+(b.val-6) = b.val
        omega
    · refine ⟨((⟨b.val,h.1⟩,⟨a.val-6,by omega⟩),1),?_⟩
      apply Subtype.ext
      apply Prod.ext
      · apply Fin.ext
        change 6+(a.val-6) = a.val
        omega
      · rfl

theorem mid_sector_sum (f : Basis × Basis → ℝ) :
    (∑ s : (Fin 2 × Fin 18) × Fin 2, f (midSectorEmbedding s).val) =
      ∑ p : PairSector (fun p => midCond p.1 p.2), f p.val :=
  Fintype.sum_bijective midSectorEmbedding mid_sector_embedding_bijective _ _ (fun _ => rfl)

def midSectorPair (a : Fin 2) (b : Fin 18) : Matrix (Fin 2) (Fin 2) ℂ :=
  Field.computedPair.submatrix (pairAddress (midAnchor a) (midPartner b))
    (pairAddress (midAnchor a) (midPartner b))

def midSectorBody (a : Fin 2) (b : Fin 18) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.kronecker (midSectorPair a b) environmentState

theorem mid_sector_body_positive (a : Fin 2) (b : Fin 18) :
    (midSectorBody a b).PosSemidef :=
  (computed_pair_positive.submatrix _).kronecker environmentState_positive

theorem mid_sector_body_trace (a : Fin 2) (b : Fin 18) :
    (midSectorBody a b).trace.re = (midSectorPair a b).trace.re := by
  rw [midSectorBody]
  simp only [Matrix.kronecker, Matrix.trace_kronecker, environmentState_trace, mul_one]

theorem mid_sector_body_mass_sum :
    (∑ a : Fin 2, ∑ b : Fin 18, (midSectorBody a b).trace.re) = midComputedMass := by
  simp only [mid_sector_body_trace]
  change _ = ∑ p : PairSector (fun p => midCond p.1 p.2), (Field.computedPair p.val p.val).re
  rw [← mid_sector_sum (fun p : Basis × Basis => (Field.computedPair p p).re)]
  simp [midSectorPair, Matrix.trace, Matrix.diag, Fintype.sum_prod_type,
    Fin.sum_univ_two, midSectorEmbedding, pairAddress]

theorem mid_sector_body_mass_lower :
    (74580/100000 : ℝ) < ∑ a : Fin 2, ∑ b : Fin 18, (midSectorBody a b).trace.re := by
  rw [mid_sector_body_mass_sum]
  exact mid_computed_mass_bound

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
