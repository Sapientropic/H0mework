import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeHamiltonianForceReduction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceInverseCoframeNeutralBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussQuantumMultiplier
open GaussNativeForm GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory GaussMatterCore
open SourceMixedNativeReturn SourceScalarDoubleCurrent SourceScalarGaugeForce
open SourceInverseCompressionCurrent SourceInverseGaugeSingleDefectJoin SourceInverseHamiltonianForceReduction
open SourceHamiltonianScaleJet SourceDilationRemainder SourceKineticTranspose SourceCoframeVolumeCurrent
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge SourceQuantumScalarChart
open SourceGaugeCoframeWard
open scoped ContDiff InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] diagonalAction kineticAction gaugeKinetic matterAction scaleDerivative
  SourceScalarDoubleCurrent.fullInsertion SourceMixedNativeReturn.fullAction SourceMixedNativeReturn.thetaAction
  firstHamiltonianCurrent matterInsertion matterHamiltonianCurrent neutralCurrent
  localAction spatialAction kineticMinus electricSpatial sourceRead

private theorem scale_product (A B : End) :
    scaleDerivative (A*B)=scaleDerivative A*B+A*scaleDerivative B := by
  rw [←SourceGaugeCoframeJets.K_commutator,←SourceGaugeCoframeJets.K_commutator,←SourceGaugeCoframeJets.K_commutator]
  noncomm_ring

private theorem scale_bracket (A B : End) :
    scaleDerivative (bracket A B)=bracket (scaleDerivative A) B+bracket A (scaleDerivative B) := by
  simp only [bracket,map_sub,scale_product]
  noncomm_ring

private theorem source_split : diagonalAction=kineticMinus+matterAction+electricSpatial+localAction := by
  rw [original_action_split]
  unfold kineticMinus electricSpatial
  abel

private theorem neutral_split (sharp : Bool) (m ell : ℕ) :
    neutralCurrent sharp m ell=bracket kineticMinus (SourceScalarDoubleCurrent.fullInsertion sharp m ell) := by
  have he := (original_electric_insertion sharp m ell).eq
  have hl := (local_full_insertion sharp m ell).eq
  unfold neutralCurrent firstHamiltonianCurrent matterInsertion
  rw [source_split]
  unfold bracket
  linear_combination (norm := noncomm_ring) he+hl

private theorem kinetic_minus_scale : scaleDerivative kineticMinus=(-3 : ℂ) • kineticMinus := by
  simp only [kineticMinus,map_sub,scale_kinetic,scale_electric]
  module

/-- The original full matter insertion has coframe weight −1. -/
theorem original_matter_current_coframe (sharp : Bool) (m ell : ℕ) :
    scaleDerivative (matterInsertion sharp m ell)=(-1 : ℂ) • matterInsertion sharp m ell := by
  rw [matterInsertion,scale_bracket,scale_matter,full_insertion_scale]
  simp only [bracket,smul_mul_assoc,mul_smul_comm,mul_zero,zero_mul,sub_self,add_zero,smul_sub]

/-- The actual neutral source current has weight −3, including the original coframe volume disposition. -/
theorem original_neutral_coframe (sharp : Bool) (m ell : ℕ) :
    scaleDerivative (neutralCurrent sharp m ell)=(-3 : ℂ) • neutralCurrent sharp m ell := by
  rw [neutral_split,scale_bracket,kinetic_minus_scale,full_insertion_scale]
  simp only [bracket,smul_mul_assoc,mul_smul_comm,mul_zero,zero_mul,sub_self,add_zero,smul_sub]

/-- The first H-current retains the exact source correction 2W under coframe differentiation. -/
theorem original_first_current_coframe (sharp : Bool) (m ell : ℕ) :
    scaleDerivative (firstHamiltonianCurrent sharp m ell)=
      (-3 : ℂ) • firstHamiltonianCurrent sharp m ell+(2 : ℂ) • matterInsertion sharp m ell := by
  have h := original_neutral_coframe sharp m ell
  simp only [neutralCurrent,map_sub,original_matter_current_coframe] at h
  linear_combination (norm := module) h

private theorem bracket_weight (A B : End) (a b : ℂ)
    (hA : scaleDerivative A=a • A) (hB : scaleDerivative B=b • B) :
    scaleDerivative (bracket A B)=(a+b) • bracket A B := by
  rw [scale_bracket,hA,hB]
  simp only [bracket,smul_mul_assoc,mul_smul_comm]
  module

private theorem cubic_weight (A : End) (a : ℂ) (h : scaleDerivative A=a • A) :
    cubic A=(a^3+12*a^2+44*a+48) • A := by
  simp only [cubic,LinearMap.add_apply,LinearMap.comp_apply,LinearMap.smul_apply,LinearMap.id_apply,h,map_smul,smul_smul]
  module

/-- The actual Kg weight is +1, so its Q cross is annihilated by the original coframe cubic. -/
theorem original_kinetic_cross_cubic (sharp : Bool) (m ell : ℕ) :
    cubic (bracket gaugeKinetic (neutralCurrent sharp m ell))=0 := by
  have h := bracket_weight gaugeKinetic (neutralCurrent sharp m ell) 1 (-3)
    (by simpa only [one_smul] using scale_electric) (original_neutral_coframe sharp m ell)
  have hc := cubic_weight _ (1-3) h
  norm_num at hc
  exact hc

private theorem real_local (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val)
    (A : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (hA : ∀ z : physicalChart,ContDiffAt ℝ ∞ A z.val) : Commute (multiply c hc) (localMultiplier A hA) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact (map_smul (A z) (c z : ℂ) (f z)).symm

private theorem local_matter (sharp : Bool) (m ell : ℕ) : Commute localAction (matterInsertion sharp m ell) := by
  have hM : Commute localAction matterAction := by
    unfold localAction matterAction
    apply Commute.sum_right
    intro i _
    apply Commute.sum_right
    intro b _
    exact real_local _ _ _ _
  have hX := local_full_insertion sharp m ell
  unfold matterInsertion bracket
  exact (hM.mul_right hX).sub_right (hX.mul_right hM)

private theorem matter_split (sharp : Bool) (m ell : ℕ) :
    matterHamiltonianCurrent sharp m ell=
      bracket kineticMinus (matterInsertion sharp m ell)+bracket matterAction (matterInsertion sharp m ell)+
      bracket electricSpatial (matterInsertion sharp m ell) := by
  have hl := (local_matter sharp m ell).eq
  unfold matterHamiltonianCurrent
  rw [source_split]
  unfold bracket
  linear_combination (norm := noncomm_ring) hl

private theorem matter_cubic (sharp : Bool) (m ell : ℕ) :
    cubic (matterHamiltonianCurrent sharp m ell)=
      (48 : ℂ) • electricMatterCurrent (SourceScalarDoubleCurrent.fullInsertion sharp m ell) := by
  let W := matterInsertion sharp m ell
  have hW : scaleDerivative W=(-1 : ℂ) • W := original_matter_current_coframe sharp m ell
  have hK := bracket_weight kineticMinus W (-3) (-1) kinetic_minus_scale hW
  have hM := bracket_weight matterAction W (-1) (-1) scale_matter hW
  have hE : scaleDerivative electricSpatial=(1 : ℂ) • electricSpatial := by
    simp only [electricSpatial,map_add,scale_electric,scale_spatial,one_smul]
  have hEW := bracket_weight electricSpatial W 1 (-1) hE hW
  have hcK := cubic_weight _ (-3+-1) hK
  have hcM := cubic_weight _ (-1+-1) hM
  have hcE := cubic_weight _ (1+-1) hEW
  norm_num at hcK hcM hcE
  rw [matter_split,map_add,map_add]
  dsimp only [W] at hcK hcM hcE
  rw [hcK,hcM,hcE,zero_add,zero_add,original_electric_matter_current,matterInsertion]

private theorem double_split (sharp : Bool) (m ell : ℕ) :
    bracket diagonalAction (bracket diagonalAction (SourceScalarDoubleCurrent.fullInsertion sharp m ell))=
      bracket diagonalAction (neutralCurrent sharp m ell)+matterHamiltonianCurrent sharp m ell := by
  unfold neutralCurrent firstHamiltonianCurrent matterHamiltonianCurrent bracket
  noncomm_ring

/-- The original Pc acts on the neutral H-current without any electric or magnetic force remainder. -/
theorem original_neutral_coframe_ward (sharp : Bool) (m ell : ℕ) :
    cubic (bracket diagonalAction (neutralCurrent sharp m ell))=
      (-96*(sourceTime 0 : ℂ)^2) •
        bracket SourceScalarRadialContact.scalarEulerAction (SourceScalarDoubleCurrent.fullInsertion sharp m ell) := by
  have hs := congrArg cubic (double_split sharp m ell)
  rw [map_add,matter_cubic,original_double_oscillator_current] at hs
  linear_combination (norm := module) -hs

def neutralScaleRemainder (sharp : Bool) (m ell : ℕ) : End :=
  cubic (bracket diagonalAction (neutralCurrent sharp m ell))-
    (48 : ℂ) • bracket diagonalAction (neutralCurrent sharp m ell)

private theorem actual_scale_remainder_split (sharp : Bool) (m ell : ℕ) :
    scaleDoubleRemainder sharp m ell=neutralScaleRemainder sharp m ell+
      (48 : ℂ) • electricMatterCurrent (SourceScalarDoubleCurrent.fullInsertion sharp m ell)-
      (48 : ℂ) • matterHamiltonianCurrent sharp m ell := by
  have hj : scaleDoubleRemainder sharp m ell=
      cubic (bracket diagonalAction (bracket diagonalAction (SourceScalarDoubleCurrent.fullInsertion sharp m ell)))-
      (48 : ℂ) • bracket diagonalAction (bracket diagonalAction (SourceScalarDoubleCurrent.fullInsertion sharp m ell)) := by
    simp only [scaleDoubleRemainder,cubic,LinearMap.add_apply,LinearMap.comp_apply,LinearMap.smul_apply,LinearMap.id_apply]
    module
  rw [hj,double_split,map_add,matter_cubic]
  unfold neutralScaleRemainder
  module

/-- The original raw force is its first H-current together with the genuine neutral coframe remainder. -/
def neutralForce (sharp : Bool) (m ell : ℕ) : End :=
  matterHamiltonianCurrent sharp m ell-
    (2*(sourceTime 0 : ℂ)^2) • (SourceMixedNativeReturn.fullAction sharp*cutoffEuler m ell)+
    (2*(sourceTime 0 : ℂ)^2) • (constantAction sharp vacuum*SourceMixedNativeReturn.thetaAction m ell)-
    (1/48 : ℂ) • neutralScaleRemainder sharp m ell

theorem original_neutral_force_return (sharp : Bool) (m ell : ℕ) : oscillatorForce sharp m ell=neutralForce sharp m ell := by
  unfold oscillatorForce neutralForce
  rw [actual_scale_remainder_split]
  module

/-- This is the complete original compressed force at the same F and seed, with all projection flux retained. -/
theorem actual_compressed_neutral_force (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) :
    compressedOscillatorForce sharp m ell F g=
      sourceRead F g (neutralForce sharp m ell)-doubleProjectionFlux sharp m ell F g := by
  rw [compressedOscillatorForce,original_neutral_force_return]

end LowEnergy.SourceInverseCoframeNeutralBudget
