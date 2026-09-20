import H0mework.Physics.LowEnergyKinetic.Density
import H0mework.Physics.LowEnergyFermion.Source

/-! The source kinetic normalization and its exact current and four-leg amplitudes. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Kinetic
open DiracExteriorMatterAction DiracCliffordRepresentation StageNineFullDiracAdjointMaterial
open Stage9C.Material.SpinPair ProofFreeRicherAnholonomicSource SU7MotherLieAlgebra
open StageNineDynamicBreakingVacuum StageNineDiracDualYukawaSpinJurisdiction
open QuantizationCheck.Fermion
noncomputable section
attribute [local instance] Fermion.fullIndexOrder

def externalScale : ℝ := (Real.sqrt spinScale)⁻¹

theorem externalScale_positive : 0<externalScale :=
  inv_pos.mpr (Real.sqrt_pos.mpr spinScale_pos)

theorem externalScale_square : externalScale^2=spinScale⁻¹ := by
  rw [externalScale,inv_pow,Real.sq_sqrt (le_of_lt spinScale_pos)]

theorem density_scale_one : spinScale*externalScale^2=1 := by
  rw [externalScale_square,mul_inv_cancel₀ (ne_of_gt spinScale_pos)]

theorem externalScale_fourth : externalScale^4=1/2 := by
  calc
    _ = (externalScale^2)^2 := by ring
    _ = (spinScale^2)⁻¹ := by rw [externalScale_square,inv_pow]
    _ = _ := by rw [spinScale_sq]; norm_num

def normalized (matter : DiracExteriorMatterCarrier) : DiracExteriorMatterCarrier :=
  (externalScale : ℂ) • matter

private theorem scale_star : star (externalScale : ℂ)=(externalScale : ℂ) := by simp

theorem coordinatePair_normalized (left right : DiracExteriorMatterCarrier) :
    Quantum.coordinatePair (normalized left) (normalized right) =
      (spinScale : ℂ)⁻¹*Quantum.coordinatePair left right := by
  unfold normalized
  rw [Quantum.coordinatePair_smul,scale_star]
  have factor : (externalScale : ℂ)^2=(spinScale : ℂ)⁻¹ := by exact_mod_cast externalScale_square
  rw [← pow_two,factor]

theorem existing_Fock_pair_normalized (left right : DiracExteriorMatterCarrier) :
    pairing (oneParticle (Quantum.coordinates (normalized left)))
      (oneParticle (Quantum.coordinates (normalized right))) =
      (spinScale : ℂ)⁻¹*Quantum.coordinatePair left right := by
  rw [pairing_oneParticle]
  exact coordinatePair_normalized left right

theorem kineticPair_normalized (left right : DiracExteriorMatterCarrier) :
    kineticPair spinScale (normalized left) (normalized right) =
      Quantum.coordinatePair left (diracMatrixMatterAction diracGammaFive right) := by
  unfold kineticPair normalized
  rw [map_smul,Quantum.coordinatePair_smul,scale_star]
  have factor : (spinScale : ℂ)*(externalScale : ℂ)^2=1 := by exact_mod_cast density_scale_one
  calc
    _ = ((spinScale : ℂ)*(externalScale : ℂ)^2)*
        Quantum.coordinatePair left (diracMatrixMatterAction diracGammaFive right) := by ring
    _ = _ := by rw [factor,one_mul]

theorem normalized_right_pair (left right : DiracExteriorMatterCarrier)
    (right_chiral : diracMatrixMatterAction diracGammaFive right=right) :
    kineticPair spinScale (normalized left) (normalized right)=Quantum.coordinatePair left right := by
  rw [kineticPair_normalized,right_chiral]

theorem normalized_right_unit (matter : DiracExteriorMatterCarrier)
    (right_chiral : diracMatrixMatterAction diracGammaFive matter=matter)
    (unit : Quantum.coordinatePair matter matter=1) :
    kineticPair spinScale (normalized matter) (normalized matter)=1 := by
  rw [normalized_right_pair _ _ right_chiral,unit]

theorem phaseChargePair_normalized (left right : DiracExteriorMatterCarrier) :
    phaseChargePair spinScale (normalized left) (normalized right) =
      Quantum.coordinatePair left (diracMatrixMatterAction diracGammaFive (FullPhase.phaseGenerator right)) := by
  unfold phaseChargePair
  have commute : FullPhase.phaseGenerator (normalized right)=normalized (FullPhase.phaseGenerator right) := by
    simp [normalized]
  rw [commute,kineticPair_normalized]

theorem unit_charge_pair_eq (left right : DiracExteriorMatterCarrier)
    (unit_charge : FullPhase.phaseGenerator right=right) :
    phaseChargePair spinScale (normalized left) (normalized right) =
      kineticPair spinScale (normalized left) (normalized right) := by
  rw [phaseChargePair_normalized,unit_charge,kineticPair_normalized]

def sourceBilinear (action : Module.End ℂ DiracExteriorMatterCarrier)
    (left right : DiracExteriorMatterCarrier) : ℂ :=
  (spinScale : ℂ)*fullCanonicalDiracAdjoint left (action right)

theorem sourceBilinear_normalized (action : Module.End ℂ DiracExteriorMatterCarrier)
    (left right : DiracExteriorMatterCarrier) :
    sourceBilinear action (normalized left) (normalized right) =
      (spinScale : ℂ)⁻¹*sourceBilinear action left right := by
  unfold sourceBilinear normalized
  rw [fullCanonicalDiracAdjoint_smul,map_smul,LinearMap.smul_apply,map_smul]
  simp only [starRingEnd_apply,scale_star,smul_eq_mul]
  have factor : (externalScale : ℂ)^2=(spinScale : ℂ)⁻¹ := by exact_mod_cast externalScale_square
  calc
    _ = (externalScale : ℂ)^2*((spinScale : ℂ)*fullCanonicalDiracAdjoint left (action right)) := by ring
    _ = _ := by rw [factor]

theorem original_current_normalized (coframe : LorentzianCoframe) (mu : LorentzianIndex)
    (data : P286LieBlockData) (left right : DiracExteriorMatterCarrier) :
    Exchange.current coframe (normalized right)
      ((spinScale : ℂ) • fullCanonicalDiracAdjoint (normalized left)) mu data =
      spinScale⁻¹*Exchange.current coframe right ((spinScale : ℂ) • fullCanonicalDiracAdjoint left) mu data := by
  change |coframe.det| *(sourceBilinear (Exchange.currentOperator coframe mu data)
      (normalized left) (normalized right)).re =
    spinScale⁻¹*(|coframe.det| *(sourceBilinear (Exchange.currentOperator coframe mu data) left right).re)
  rw [sourceBilinear_normalized,← Complex.ofReal_inv]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

theorem original_scalar_normalized (coframe : LorentzianCoframe) (direction : ScalarCoordinateCarrier)
    (left right : DiracExteriorMatterCarrier) :
    Exchange.yukawaSource coframe (normalized right)
      ((spinScale : ℂ) • fullCanonicalDiracAdjoint (normalized left)) direction =
      spinScale⁻¹*Exchange.yukawaSource coframe right ((spinScale : ℂ) • fullCanonicalDiracAdjoint left) direction := by
  change |coframe.det| *(sourceBilinear
      (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm direction))
      (normalized left) (normalized right)).re =
    spinScale⁻¹*(|coframe.det| *(sourceBilinear
      (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm direction)) left right).re)
  rw [sourceBilinear_normalized,← Complex.ofReal_inv]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

theorem sourcePair_normalized (left right : DiracExteriorMatterCarrier) :
    Fermion.sourcePair (normalized left) (normalized right) =
      (spinScale : ℂ)⁻¹ • Fermion.sourcePair left right := by
  unfold Fermion.sourcePair normalized
  rw [map_smul,map_smul,Fermion.twoParticle_smul]
  have factor : (externalScale : ℂ)^2=(spinScale : ℂ)⁻¹ := by exact_mod_cast externalScale_square
  rw [← pow_two,factor]

theorem four_leg_amplitude_normalized (operator : Module.End ℂ (Fock Quantum.Index))
    (first second third fourth : DiracExteriorMatterCarrier) :
    pairing (Fermion.sourcePair (normalized first) (normalized second))
      (operator (Fermion.sourcePair (normalized third) (normalized fourth))) =
      (1/2 : ℂ)*pairing (Fermion.sourcePair first second) (operator (Fermion.sourcePair third fourth)) := by
  rw [sourcePair_normalized,sourcePair_normalized,map_smul,Fermion.pairing_smul_left,
    Fermion.pairing_smul_right]
  have conjugate : star ((spinScale : ℂ)⁻¹)=(spinScale : ℂ)⁻¹ := by simp
  rw [conjugate]
  have square : (spinScale : ℂ)^2=2 := by exact_mod_cast spinScale_sq
  calc
    _ = ((spinScale : ℂ)^2)⁻¹*
      pairing (Fermion.sourcePair first second) (operator (Fermion.sourcePair third fourth)) := by
        rw [← inv_pow]
        ring
    _ = _ := by rw [square]; norm_num

end
end SaturationMonoid.PhysicsCore.LowEnergy.Kinetic
