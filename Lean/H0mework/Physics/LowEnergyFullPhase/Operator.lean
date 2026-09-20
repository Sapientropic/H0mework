import H0mework.Physics.LowEnergyCanonicalActive.Phase
import H0mework.Physics.LowEnergyMixed.Degree

/-! The original occupied phase extended along the one-way degree-two to degree-six arrow. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullPhase
open ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair
open DiracCliffordRepresentation DiracExteriorMatterAction SU7ExteriorMatterRepresentation
open SU7ExteriorBreakingYukawa StageNineDiracDualYukawaSpinJurisdiction
noncomputable section
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

def otherRate : DiracSpinorIndex → ℝ := ![frequency,frequency,-frequency,-frequency]
def sixPrimalRate : DiracSpinorIndex → ℝ := ![-frequency,-frequency,-(3*frequency),-(3*frequency)]
def sixDualRate : DiracSpinorIndex → ℝ := ![3*frequency,3*frequency,frequency,frequency]

def phaseOperator (six other : DiracSpinorIndex → ℝ) (point : BasePoint) :
    Module.End ℂ DiracExteriorMatterCarrier where
  toFun matter spin := (phase (six spin) point • (matter spin).1,
    phase (other spin) point • (matter spin).2.1,
    phase (other spin) point • (matter spin).2.2)
  map_add' := by intros; funext spin; simp [smul_add]
  map_smul' := by
    intro scalar matter
    funext spin
    exact Prod.ext (smul_comm _ _ _) (Prod.ext (smul_comm _ _ _) (smul_comm _ _ _))

def primal (point : BasePoint) := phaseOperator sixPrimalRate otherRate point
def dual (point : BasePoint) := phaseOperator sixDualRate otherRate point

theorem phaseOperator_inverse (six other : DiracSpinorIndex → ℝ) (point : BasePoint) :
    (phaseOperator six other point).comp (phaseOperator (-six) (-other) point) = LinearMap.id := by
  apply LinearMap.ext
  intro matter
  funext spin
  simp [phaseOperator, smul_smul, phase_opposite]

theorem phaseOperator_inverse_reverse (six other : DiracSpinorIndex → ℝ) (point : BasePoint) :
    (phaseOperator (-six) (-other) point).comp (phaseOperator six other point) = LinearMap.id := by
  simpa only [neg_neg] using phaseOperator_inverse (-six) (-other) point

theorem primal_zero : primal 0 = LinearMap.id := by
  apply LinearMap.ext
  intro matter
  funext spin
  simp [primal,phaseOperator,phase_zero]

theorem dual_zero : dual 0 = LinearMap.id := by
  apply LinearMap.ext
  intro matter
  funext spin
  simp [dual,phaseOperator,phase_zero]

private theorem opposite_phase (rate : ℝ) (point : BasePoint) :
    phase (-rate) point * phase rate point = 1 := by
  rw [mul_comm,phase_opposite]

private theorem phase_middle (rate : ℝ) (point : BasePoint) (value : ℂ) :
    phase rate point * (value * phase (-rate) point) = value := by
  calc
    _ = value*(phase rate point*phase (-rate) point) := by ring
    _ = _ := by rw [phase_opposite,mul_one]

private theorem opposite_phase_middle (rate : ℝ) (point : BasePoint) (value : ℂ) :
    phase (-rate) point * (value * phase rate point) = value := by
  calc
    _ = value*(phase (-rate) point*phase rate point) := by ring
    _ = _ := by rw [opposite_phase,mul_one]

private theorem gamma_zero (point : BasePoint) (matter : DiracExteriorMatterCarrier) :
    dual point (diracMatrixMatterAction diracGammaZero (primal point matter)) =
      diracMatrixMatterAction diracGammaZero matter := by
  funext spin
  fin_cases spin
  all_goals apply Prod.ext
  all_goals try apply Prod.ext
  all_goals simp [primal,dual,phaseOperator,otherRate,sixPrimalRate,sixDualRate,
    diracMatrixMatterAction,diracGammaZero,Fin.sum_univ_four,smul_smul,
    phase_opposite,opposite_phase]
  all_goals module

private theorem gamma_one (point : BasePoint) (matter : DiracExteriorMatterCarrier) :
    dual point (diracMatrixMatterAction diracGammaOne (primal point matter)) =
      diracMatrixMatterAction diracGammaOne matter := by
  funext spin
  fin_cases spin
  all_goals apply Prod.ext
  all_goals try apply Prod.ext
  all_goals simp [primal,dual,phaseOperator,otherRate,sixPrimalRate,sixDualRate,
    diracMatrixMatterAction,diracGammaOne,Fin.sum_univ_four,smul_smul,
    phase_opposite,opposite_phase]

private theorem gamma_two (point : BasePoint) (matter : DiracExteriorMatterCarrier) :
    dual point (diracMatrixMatterAction diracGammaTwo (primal point matter)) =
      diracMatrixMatterAction diracGammaTwo matter := by
  funext spin
  fin_cases spin
  all_goals apply Prod.ext
  all_goals try apply Prod.ext
  all_goals simp [primal,dual,phaseOperator,otherRate,sixPrimalRate,sixDualRate,
    diracMatrixMatterAction,diracGammaTwo,Fin.sum_univ_four,smul_smul,
    phase_middle,opposite_phase_middle]
  all_goals module

private theorem gamma_three (point : BasePoint) (matter : DiracExteriorMatterCarrier) :
    dual point (diracMatrixMatterAction diracGammaThree (primal point matter)) =
      diracMatrixMatterAction diracGammaThree matter := by
  funext spin
  fin_cases spin
  all_goals apply Prod.ext
  all_goals try apply Prod.ext
  all_goals simp [primal,dual,phaseOperator,otherRate,sixPrimalRate,sixDualRate,
    diracMatrixMatterAction,diracGammaThree,Fin.sum_univ_four,smul_smul,
    phase_opposite,opposite_phase]
  all_goals module

theorem gamma_preserved (point : BasePoint) (mu : LorentzianIndex)
    (matter : DiracExteriorMatterCarrier) :
    dual point (diracMatrixMatterAction (diracGamma mu) (primal point matter)) =
      diracMatrixMatterAction (diracGamma mu) matter := by
  fin_cases mu
  · exact gamma_zero point matter
  · exact gamma_one point matter
  · exact gamma_two point matter
  · exact gamma_three point matter

theorem yukawa_preserved (point : BasePoint) (scalar : ExteriorBreakingScalarCarrier)
    (matter : DiracExteriorMatterCarrier) :
    dual point (diracDualRightChiralYukawaAction scalar (primal point matter)) =
      diracDualRightChiralYukawaAction scalar matter := by
  funext spin
  fin_cases spin
  all_goals simp [primal,dual,phaseOperator,otherRate,sixPrimalRate,sixDualRate,
    diracDualRightChiralYukawaAction,diracExteriorYukawaInternalAction,internalMatterLinearAction,
    exteriorYukawaInternalAction,diracMatrixMatterAction,rightChiralityProjector,diracGammaFive,
    Fin.sum_univ_four,smul_smul]
  all_goals norm_num
  all_goals simp [phase_opposite]

theorem original_matter (point : BasePoint) :
    actual.matter point = primal point (spinPairMatter 1 1) := by
  rw [actual_matter]
  funext spin
  fin_cases spin
  all_goals simp [primal,phaseOperator,otherRate,sixPrimalRate,spinPairMatter,
    sourceColorDiracMatter,spinPairCoefficients,sourceColorDoubletMatter,
    Fin.sum_univ_two,upperPhase,lowerPhase]
  all_goals module

theorem original_mixing_stationary (point : BasePoint) (scalar : ExteriorBreakingScalarCarrier) :
    dual point (MixedSymbol.scalarMixing point scalar) = MixedSymbol.scalarMixing 0 scalar := by
  unfold MixedSymbol.scalarMixing
  rw [original_matter,yukawa_preserved,original_matter,primal_zero,LinearMap.id_apply]

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullPhase
