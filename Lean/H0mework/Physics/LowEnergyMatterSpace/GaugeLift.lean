import H0mework.Physics.LowEnergyMatterSpace.GaugeTriplet
import H0mework.Physics.LowEnergyMatterSpace.Connection

/-! The original exterior gauge force, with every P286 direction retained. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
open DiracCliffordRepresentation DiracExteriorMatterAction ActiveSector
open SU7MotherLieAlgebra SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction
open StageNineHolonomicField StageNineP286GaugeConnectionVariation
open Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous
open ProofFreeRicherAnholonomicSource
open scoped Matrix Kronecker BigOperators
noncomputable section

def tripletLift : (SourceIndex → ℂ) →ₗ[ℂ] DiracExteriorMatterCarrier where
  toFun v := tripletMatter (fun spin color => v (spin,color))
  map_add' u v := by
    funext spin
    simp [tripletMatter,add_smul,Finset.sum_add_distrib]
  map_smul' c v := by
    funext spin
    simp [tripletMatter,smul_smul,Finset.smul_sum]

theorem tripletLift_coordinate (v : SourceIndex → ℂ) (spin : DiracSpinorIndex) (color : Fin 3) :
    (su7ExteriorBasis 2).coord (colorTripletIndex color) (tripletLift v spin).2.1=v (spin,color) := by
  fin_cases color <;>
    simp +decide [tripletLift,tripletMatter,colorTripletMatter,colorTripletIndex,Fin.sum_univ_three]

theorem tripletLift_injective : Function.Injective tripletLift := by
  intro u v same
  funext index
  have coordinate := congrArg (fun matter : DiracExteriorMatterCarrier =>
    (su7ExteriorBasis 2).coord (colorTripletIndex index.2) (matter index.1).2.1) same
  simpa only [tripletLift_coordinate] using coordinate

theorem tripletLift_tensor (spin : DiracMatrix) (color : Matrix (Fin 3) (Fin 3) ℂ)
    (v : SourceIndex → ℂ) :
    tripletLift ((spin ⊗ₖ color)*ᵥv)=
      diracMatrixMatterAction spin
        (tripletMatter (fun a b => ∑ c, color b c*v (a,c))) := by
  rw [triplet_spin_action]
  apply congrArg tripletMatter
  funext a b
  simp only [Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply,Fintype.sum_prod_type,
    Finset.mul_sum,mul_assoc]

def tripletGaugeMatrix (data : P286LieBlockData) : Matrix (Fin 3) (Fin 3) ℂ :=
  (data.1 : Matrix (Fin 3) (Fin 3) ℂ)+data.2.2.1 • 1

theorem tripletGaugeMatrix_apply (data : P286LieBlockData) (v : Fin 3 → ℂ) (target : Fin 3) :
    (tripletGaugeMatrix data*ᵥv) target=
      (∑ color, (data.1 : Matrix (Fin 3) (Fin 3) ℂ) target color*v color)+data.2.2.1*v target := by
  simp only [tripletGaugeMatrix,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  rfl

theorem tripletLift_spin_gauge (spin : DiracMatrix) (data : P286LieBlockData)
    (v : SourceIndex → ℂ) :
    tripletLift ((spin ⊗ₖ tripletGaugeMatrix data)*ᵥv)=
      diracMatrixMatterAction spin
        (diracExteriorMotherLieAction (p286LieBlockEmbed data) (tripletLift v)) := by
  rw [tripletLift_tensor]
  change _ = diracMatrixMatterAction spin
    (diracExteriorMotherLieAction (p286LieBlockEmbed data) (tripletMatter _))
  rw [original_P286_triplet]
  congr 2
  funext a b
  exact tripletGaugeMatrix_apply data (fun c => v (a,c)) b

def sourceInverseGamma (mu : LorentzianIndex) : DiracMatrix :=
  ((if mu=0 then lapse⁻¹ else 1 : ℝ) : ℂ) • diracGamma mu

theorem sourceInverseGamma_original (point : BasePoint) (mu : LorentzianIndex) :
    sourceInverseGamma mu=
      inverseCoframeDiracGamma { coframe := actual.coframe point, derivative := 0 } mu := by
  rw [actual_coframe,homogeneousInverseGamma lapse (ne_of_gt lapse_pos)]
  by_cases zero : mu=0 <;> simp [sourceInverseGamma,zero]

def gaugeDiracMatrix (data : LorentzianIndex → P286LieBlockData) : SourceMatrix :=
  Complex.I • ∑ mu, sourceInverseGamma mu ⊗ₖ tripletGaugeMatrix (data mu)

theorem gaugeDirac_original (data : LorentzianIndex → P286LieBlockData)
    (v : SourceIndex → ℂ) :
    tripletLift (gaugeDiracMatrix data*ᵥv)=
      Complex.I • ∑ mu, diracMatrixMatterAction (sourceInverseGamma mu)
        (diracExteriorMotherLieAction (p286LieBlockEmbed (data mu)) (tripletLift v)) := by
  simp only [gaugeDiracMatrix,Matrix.smul_mulVec,Matrix.sum_mulVec,map_smul,map_sum,
    tripletLift_spin_gauge]

def actualTripletVector (point : BasePoint) : SourceIndex → ℂ :=
  fun index => originalTripletCoefficients (upperPhase point) (lowerPhase point) index.1 index.2

theorem actual_matter_tripletLift (point : BasePoint) :
    actual.matter point=tripletLift (actualTripletVector point) := by
  change spinPairMatter (upperPhase point) (lowerPhase point)=_
  rw [original_matter_triplet]
  rfl

theorem gaugeDirac_holonomic_variation (variation : BasePoint → P286GaugeOneForm)
    (point : BasePoint) :
    tripletLift (gaugeDiracMatrix (fun mu => p286CoordinateEquiv.symm (variation point mu))*ᵥ
      actualTripletVector point)=
      Complex.I • ∑ mu, diracMatrixMatterAction
        (inverseCoframeDiracGamma { coframe := actual.coframe point, derivative := 0 } mu)
        (holonomicMatterGaugeConnectionVariation actual variation point mu) := by
  rw [gaugeDirac_original]
  simp_rw [sourceInverseGamma_original point,← actual_matter_tripletLift point]
  rfl

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
