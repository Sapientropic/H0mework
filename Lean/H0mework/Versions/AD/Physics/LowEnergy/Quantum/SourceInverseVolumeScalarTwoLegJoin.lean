import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceInverseVolumeNeutralScalarCurrent
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceInverseVolumeElectricMomentGram

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PositiveScalarWeakBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum SourceMixedNativeReturn
open SourceInverseNeutralScalarCurrent SourceScalarRadialContact SourceNativeCutoffContact SourceGammaNativeBudget
open SourceScalarDoubleCurrent SourceCoframeVolume SourceScalarPositiveBulkWard
open SourceInverseMagneticForceCancellation SourceScalarGaugeForce
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open SourceInverseElectricMomentGram FullYSourceResolventGraphSplice SourceResolventBandLimit MeasureTheory
open scoped InnerProductSpace ContDiff
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

private theorem full_pair (sharp : Bool) (f g : QuantumTest) :
    sourcePair f (fullAction sharp g)=sourcePair (fullAction (!sharp) f) g := by
  cases sharp
  · have h := congrArg (starRingEnd ℂ) (GaussFullHamiltonian.yukawa_pair g f)
    simpa only [sourcePair,inner_conj_symm,Bool.not_false] using! h.symm
  · exact GaussFullHamiltonian.yukawa_pair f g

private theorem real_full (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (sharp : Bool) :
    Commute (multiply c hc) (fullAction sharp) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  cases sharp
  · exact (map_smul (GaussYukawaCoefficient.sourceMap (GaussNativePotential.scalarField z))
      (c z : ℂ) (f z)).symm
  · exact (map_smul (GaussFullHamiltonian.adjointMap (GaussNativePotential.scalarField z))
      (c z : ℂ) (f z)).symm

private theorem full_adjoint (sharp : Bool) (v : Ambient) :
    GaussMomentumAdjoint.adjoint v*fullAction sharp-fullAction sharp*GaussMomentumAdjoint.adjoint v=
      (-Complex.I) • constantAction sharp v.1 := by
  apply LinearMap.ext
  intro g
  apply SourceCoframeVolume.pair_ext
  intro f
  have h := original_full_momentum (!sharp) v f
  have hh := congrArg (fun t : QuantumTest => sourcePair t g) h
  simp only [sourcePair,map_add,map_smul,inner_add_left,inner_smul_left,map_neg,Complex.conj_I,neg_neg] at hh
  change sourcePair f (GaussMomentumAdjoint.adjoint v (fullAction sharp g)-
    fullAction sharp (GaussMomentumAdjoint.adjoint v g))=sourcePair f ((-Complex.I) • constantAction sharp v.1 g)
  have hl : sourcePair f (GaussMomentumAdjoint.adjoint v (fullAction sharp g)-
      fullAction sharp (GaussMomentumAdjoint.adjoint v g))=
      sourcePair (fullAction (!sharp) (covariantMomentum v f)) g-
        sourcePair (covariantMomentum v (fullAction (!sharp) f)) g := by
    simp only [sourcePair,map_sub,inner_sub_right]
    change sourcePair f (GaussMomentumAdjoint.adjoint v (fullAction sharp g))-
      sourcePair f (fullAction sharp (GaussMomentumAdjoint.adjoint v g))=_
    rw [GaussNativeForm.adjoint_pair,full_pair,full_pair,GaussNativeForm.adjoint_pair]
    rfl
  rw [hl]
  simp only [sourcePair,map_smul,inner_smul_right]
  have hp := constant_pair sharp v.1 f g
  simp only [sourcePair] at hp
  rw [hp]
  linear_combination -hh

/-- The actual derivative of Y theta, including the local cutoff contact. -/
def coefficient (sharp : Bool) (a : ScalarIndex) (m ell : ℕ) : End :=
  constantAction sharp (scalarDirection a).1*SourceMixedNativeReturn.thetaAction m ell+
    Complex.I • (fullAction sharp*contactAction (scalarDirection a) m ell)

private theorem scalar_row_join {R : Type*} [Ring R] [Module ℂ R]
    [IsScalarTower ℂ R R] [SMulCommClass ℂ R R] (A P w Y Ya T C : R)
    (hAY : A*Y-Y*A=(-Complex.I) • Ya) (hPT : P*T=T*P+C)
    (hwY : Commute w Y) (hwT : Commute w T) :
    ((-Complex.I/2 : ℂ) • (A*w*Ya+Ya*w*P))*T+
      Y*((1/2 : ℂ) • (A*w*C+C*w*P))=
    (-Complex.I/2 : ℂ) •
      (A*w*(Ya*T+Complex.I • (Y*C))+(Ya*T+Complex.I • (Y*C))*w*P) := by
  have hYA : Y*A=A*Y+Complex.I • Ya := by
    linear_combination (norm := module) -hAY
  have hx := congrArg (fun x : R => Ya*w*x) hPT
  have hy := congrArg (fun x : R => x*w*C) hYA
  have hz := congrArg (fun x : R => A*x*C) hwY.eq
  have ht := congrArg (fun x : R => Ya*x*P) hwT.eq
  have hi : (-Complex.I/2 : ℂ)*Complex.I=(1/2 : ℂ) := by
    calc _=-(Complex.I*Complex.I)/2 := by ring
         _=_ := by rw [Complex.I_mul_I];ring
  simp only [add_mul,mul_add,smul_add,smul_mul_assoc,mul_smul_comm,smul_smul,hi,mul_assoc] at hx hy hz ht ⊢
  linear_combination (norm := module) (-Complex.I/2 : ℂ) • hx +
    (1/2 : ℂ) • hy - (1/2 : ℂ) • hz - (Complex.I/2 : ℂ) • ht

attribute [local irreducible] fullAction SourceMixedNativeReturn.thetaAction scalarCurrent
  scalarKinetic diagonalAction radialCurrent scalarContact coefficient constantAction
  covariantMomentum GaussMomentumAdjoint.adjoint multiply contactAction
/-- All moving product derivatives combine into bare native scalar momenta
and one local coefficient. The source radial current is kept in the join. -/
theorem original_scalar_two_leg_join (sharp : Bool) (m ell : ℕ) :
    scalarCurrent sharp*SourceMixedNativeReturn.thetaAction m ell+fullAction sharp*radialCurrent m ell=
      (-Complex.I/2 : ℂ) • ∑ a : ScalarIndex,
        (GaussMomentumAdjoint.adjoint (scalarDirection a)*multiply scalarWeight scalarWeight_smooth*
          coefficient sharp a m ell+
        coefficient sharp a m ell*multiply scalarWeight scalarWeight_smooth*covariantMomentum (scalarDirection a)) := by
  have hr : radialCurrent m ell=scalarContact m ell := by
    rw [radialCurrent]
    exact (full_radial_contact m ell).symm
  rw [hr,scalarCurrent,scalarContact]
  simp only [smul_mul_assoc,mul_smul_comm,Finset.sum_mul,Finset.mul_sum,Finset.smul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  have hPT : covariantMomentum (scalarDirection a)*SourceMixedNativeReturn.thetaAction m ell=
      SourceMixedNativeReturn.thetaAction m ell*covariantMomentum (scalarDirection a)+contactAction (scalarDirection a) m ell := by
    apply LinearMap.ext
    intro f
    simpa only [SourceNativeCutoffContact.theta_action_polynomial,SourceMixedNativeReturn.thetaAction,Module.End.mul_apply,LinearMap.add_apply]
      using native_core_contact (scalarDirection a) m ell f
  have hwT : Commute (multiply scalarWeight scalarWeight_smooth) (SourceMixedNativeReturn.thetaAction m ell) := by
    rw [SourceMixedNativeReturn.thetaAction,←SourceNativeCutoffContact.theta_action_polynomial]
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    simp only [Module.End.mul_apply,multiply_apply,SourceNativeCutoffContact.thetaAction,multiply_apply]
    exact smul_comm (scalarWeight z : ℂ) (SourceNativeCutoffContact.theta m ell z : ℂ) (f z)
  rw [coefficient]
  simpa only [smul_mul_assoc,mul_smul_comm] using scalar_row_join (GaussMomentumAdjoint.adjoint (scalarDirection a))
    (covariantMomentum (scalarDirection a)) (multiply scalarWeight scalarWeight_smooth)
    (fullAction sharp) (constantAction sharp (scalarDirection a).1)
    (SourceMixedNativeReturn.thetaAction m ell) (contactAction (scalarDirection a) m ell)
    (full_adjoint sharp (scalarDirection a)) hPT (real_full _ _ sharp) hwT

end LowEnergy.PositiveScalarWeakBudget
