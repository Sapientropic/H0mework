import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualScalarPhaseJet
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualExactSylvesterRawStorage

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualPhaseBulkSquare
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussNativeForm GaussNativeEnergy
open SourceScalarShiftedBulk SourceScalarVirialBulk SourceScalarInverseBulk
open SourcePhysicalKineticSquare SourceScalarPositiveBulkWard SourceHamiltonianScaleJet
open SourceInverseNoetherEnergy ActualScalarPhaseJet SourceDilationMomentum
open SourceScalarGaugeScale SourceCoframeVolumeCurrent
open SourceRetardedGraph
open SourceScalarInverseNativeEnergy
open Lean Meta Elab Term
open scoped InnerProductSpace
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

def phaseForce : End := phaseJet diagonalAction
def phaseHamiltonianSquare : End := phaseSecond (diagonalAction*diagonalAction)
attribute [local irreducible] phaseForce phaseHamiltonianSquare diagonalAction inverseVolumeAction sourceTime vacuumJetCoefficient

private theorem phase_coefficient_nonzero : (phaseCoefficient:ℂ)≠0 := by
  exact_mod_cast actual_phase_coefficient_positive.ne'

private theorem actual_phase_H0 : phaseSecond diagonalAction=(-(phaseCoefficient:ℂ)) • inverseVolumeAction := by
  simpa only [phaseCoefficient,Complex.ofReal_mul,Complex.ofReal_pow,neg_mul] using
    actual_source_inverse_volume_phase_jet

/-- The inverse-volume action is a source second jet of the full H0 square,
with its actual positive force square retained. -/
theorem actual_source_phase_square :
    phaseHamiltonianSquare=(-(phaseCoefficient:ℂ)) •
      (diagonalAction*inverseVolumeAction+inverseVolumeAction*diagonalAction)+
      (2:ℂ) • (phaseForce*phaseForce) := by
  unfold phaseHamiltonianSquare phaseForce
  rw [actual_phase_second_product,actual_phase_H0]
  simp only [smul_mul_assoc,mul_smul_comm,smul_add]
  module

theorem actual_inverse_symmetric_phase_balance :
    (2*(phaseCoefficient:ℂ)) • inverseSymmetricScale=
      -phaseHamiltonianSquare+(2:ℂ) • (phaseForce*phaseForce) := by
  rw [actual_source_phase_square]
  unfold inverseSymmetricScale
  simp only [smul_smul,neg_add_rev,neg_smul]
  module

theorem actual_inverse_symmetric_phase_source :
    inverseSymmetricScale=(-(2*(phaseCoefficient:ℂ))⁻¹) • phaseHamiltonianSquare+
      (phaseCoefficient:ℂ)⁻¹ • (phaseForce*phaseForce) := by
  have hc:=phase_coefficient_nonzero
  have h2:2*(phaseCoefficient:ℂ)≠0:=mul_ne_zero (by norm_num) hc
  calc
    inverseSymmetricScale=(2*(phaseCoefficient:ℂ))⁻¹ •
        ((2*(phaseCoefficient:ℂ)) • inverseSymmetricScale) := by
      rw [smul_smul,inv_mul_cancel₀ h2,one_smul]
    _=(2*(phaseCoefficient:ℂ))⁻¹ •
        (-phaseHamiltonianSquare+(2:ℂ) • (phaseForce*phaseForce)) := by
      rw [actual_inverse_symmetric_phase_balance]
    _=_ := by
      have he:(2*(phaseCoefficient:ℂ))⁻¹*2=(phaseCoefficient:ℂ)⁻¹ := by
        field_simp
      rw [smul_add,smul_neg,smul_smul,he,neg_smul]

private theorem ward_add(A B:End):inverseWeightedBulkJet (A+B)=
    inverseWeightedBulkJet A+inverseWeightedBulkJet B := by
  unfold inverseWeightedBulkJet InverseVolumeWardAlgebra.inverseWard
    InverseVolumeWardAlgebra.mixedPolynomial InverseVolumeWardAlgebra.affinePolynomial
    InverseVolumeWardAlgebra.inverseLocalPolynomial
  simp only [map_add,map_sub,map_smul,smul_add,smul_sub]
  module

private theorem ward_smul(c:ℂ)(A:End):inverseWeightedBulkJet (c • A)=c • inverseWeightedBulkJet A := by
  unfold inverseWeightedBulkJet InverseVolumeWardAlgebra.inverseWard
    InverseVolumeWardAlgebra.mixedPolynomial InverseVolumeWardAlgebra.affinePolynomial
    InverseVolumeWardAlgebra.inverseLocalPolynomial
  simp only [map_add,map_sub,map_smul,smul_add,smul_sub,smul_smul]
  module

/-- The actual positive bulk consumes the source H0-square representation;
neither a supplied U nor a replacement compression is used. -/
theorem actual_source_bulk_phase_square :
    bulkAction=(-(2*(phaseCoefficient:ℂ))⁻¹) •
      inverseWeightedBulkJet phaseHamiltonianSquare+
      (phaseCoefficient:ℂ)⁻¹ • inverseWeightedBulkJet (phaseForce*phaseForce) := by
  change inverseVolumeAction*positiveBulk=_
  rw [←original_inverse_bulk_symmetric_jet,actual_inverse_symmetric_phase_source,
    ward_add,ward_smul,ward_smul]

elab "paid_phase_force_source%" : term => do
  mkConstWithFreshMVarLevels (Name.str (Name.str (Name.str
    (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualScalarPhaseJet 0) "LowEnergy")
    "ActualScalarPhaseJet") "phase_hamiltonian_first")

private theorem phi_product(A B:End):deltaPhi (A*B)=deltaPhi A*B+A*deltaPhi B := by
  change phiEulerAction*(A*B)-(A*B)*phiEulerAction=
    (phiEulerAction*A-A*phiEulerAction)*B+A*(phiEulerAction*B-B*phiEulerAction)
  noncomm_ring

private theorem gauge_product(A B:End):deltaGauge (A*B)=deltaGauge A*B+A*deltaGauge B := by
  change SourceGaugeRadialPair.gaugeEulerAction*(A*B)-(A*B)*SourceGaugeRadialPair.gaugeEulerAction=
    (SourceGaugeRadialPair.gaugeEulerAction*A-A*SourceGaugeRadialPair.gaugeEulerAction)*B+
      A*(SourceGaugeRadialPair.gaugeEulerAction*B-B*SourceGaugeRadialPair.gaugeEulerAction)
  noncomm_ring

private theorem coframe_product(A B:End):scaleDerivative (A*B)=scaleDerivative A*B+A*scaleDerivative B := by
  change (3*Complex.I/2) • (dilation*(A*B)-(A*B)*dilation)=
    ((3*Complex.I/2) • (dilation*A-A*dilation))*B+
      A*((3*Complex.I/2) • (dilation*B-B*dilation))
  simp only [smul_mul_assoc,mul_smul_comm,←smul_add]
  congr 1
  noncomm_ring

private theorem vacuum_symmetric_phi : deltaPhi vacuumSymmetric= -vacuumSymmetric := by
  have hp(a:ScalarIndex):deltaPhi (covariantMomentum (scalarDirection a))= -covariantMomentum (scalarDirection a) :=
    original_scalar_momentum_phi _ rfl
  have ha(a:ScalarIndex):deltaPhi (GaussMomentumAdjoint.adjoint (scalarDirection a))=
      -GaussMomentumAdjoint.adjoint (scalarDirection a) := original_scalar_adjoint_phi _ rfl
  unfold vacuumSymmetric
  simp only [map_sum,map_smul,map_add,phi_product,ha,hp,inverse_phi,mul_zero,zero_mul,
    add_zero,zero_add,neg_mul,mul_neg,←neg_add,smul_neg,←Finset.sum_neg_distrib]

private theorem vacuum_symmetric_gauge : deltaGauge vacuumSymmetric=0 := by
  have hp(a:ScalarIndex):deltaGauge (covariantMomentum (scalarDirection a))=0 :=
    original_scalar_momentum_gauge _ rfl
  have ha(a:ScalarIndex):deltaGauge (GaussMomentumAdjoint.adjoint (scalarDirection a))=0 :=
    original_scalar_adjoint_gauge _ rfl
  unfold vacuumSymmetric
  simp only [map_sum,map_smul,map_add,gauge_product,ha,hp,inverse_gauge,mul_zero,zero_mul,
    add_zero,smul_zero,Finset.sum_const_zero]

private theorem vacuum_symmetric_coframe : scaleDerivative vacuumSymmetric=(-3:ℂ) • vacuumSymmetric := by
  have hp(a:ScalarIndex):scaleDerivative (covariantMomentum (scalarDirection a))=0 := by
    change (3*Complex.I/2) • (dilation*covariantMomentum (scalarDirection a)-
      covariantMomentum (scalarDirection a)*dilation)=0
    rw [native_momentum_current,smul_zero]
  have ha(a:ScalarIndex):scaleDerivative (GaussMomentumAdjoint.adjoint (scalarDirection a))=0 := by
    change (3*Complex.I/2) • (dilation*GaussMomentumAdjoint.adjoint (scalarDirection a)-
      GaussMomentumAdjoint.adjoint (scalarDirection a)*dilation)=0
    rw [native_adjoint_current,smul_zero]
  unfold vacuumSymmetric
  simp only [map_sum,map_smul,map_add,coframe_product,ha,hp,inverse_coframe,mul_zero,zero_mul,
    add_zero,zero_add,smul_mul_assoc,mul_smul_comm,←smul_add]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [smul_smul,smul_smul,mul_comm]

/-- All three force weights follow from the original seventy source momenta and U. -/
theorem actual_source_phase_force_weights :
    deltaPhi phaseForce= -phaseForce ∧ deltaGauge phaseForce=0 ∧
      scaleDerivative phaseForce=(-3:ℂ) • phaseForce := by
  have hf:phaseForce=((sourceTime 0:ℂ)^2/2) • vacuumSymmetric := by
    unfold phaseForce
    exact paid_phase_force_source%
  rw [hf]
  simp only [map_smul,vacuum_symmetric_phi,vacuum_symmetric_gauge,vacuum_symmetric_coframe,
    smul_neg,smul_zero,true_and]
  exact smul_comm _ _ _

/-- The inverse local polynomial cancels the force square's weight minus six;
the remaining true Ward coefficient is negative eight. -/
theorem actual_phase_force_square_ward :
    inverseWeightedBulkJet (phaseForce*phaseForce)=(-8:ℂ) • (phaseForce*phaseForce) := by
  obtain ⟨hp,hg,hc⟩:=actual_source_phase_force_weights
  have hpp:deltaPhi (phaseForce*phaseForce)=(-2:ℂ) • (phaseForce*phaseForce) := by
    rw [phi_product,hp]
    simp only [neg_mul,mul_neg]
    module
  have hgg:deltaGauge (phaseForce*phaseForce)=0 := by rw [gauge_product,hg,zero_mul,mul_zero,add_zero]
  have hcc:scaleDerivative (phaseForce*phaseForce)=(-6:ℂ) • (phaseForce*phaseForce) := by
    rw [coframe_product,hc]
    simp only [smul_mul_assoc,mul_smul_comm]
    module
  have hlocal:InverseVolumeWardAlgebra.inverseLocalPolynomial scaleDerivative (phaseForce*phaseForce)=0 := by
    unfold InverseVolumeWardAlgebra.inverseLocalPolynomial
    simp only [hcc,map_smul,smul_smul]
    module
  unfold inverseWeightedBulkJet InverseVolumeWardAlgebra.inverseWard
  rw [hlocal]
  have hp0:deltaPhi (0:End)=0 := by
    change phiEulerAction*(0:End)-(0:End)*phiEulerAction=0
    simp only [mul_zero,zero_mul,sub_self]
  have hg0:deltaGauge (0:End)=0 := by
    change SourceGaugeRadialPair.gaugeEulerAction*(0:End)-(0:End)*SourceGaugeRadialPair.gaugeEulerAction=0
    simp only [mul_zero,zero_mul,sub_self]
  have haff:InverseVolumeWardAlgebra.affinePolynomial deltaPhi (0:End)=0 := by
    unfold InverseVolumeWardAlgebra.affinePolynomial
    rw [hp0,hp0,smul_zero,smul_zero,sub_zero,add_zero]
  rw [haff,smul_zero,add_zero]
  unfold InverseVolumeWardAlgebra.mixedPolynomial
  have hrel:deltaPhi (phaseForce*phaseForce)-deltaGauge (phaseForce*phaseForce)=
      (-2:ℂ) • (phaseForce*phaseForce) := by rw [hpp,hgg,sub_zero]
  have hgr:deltaGauge (deltaPhi (phaseForce*phaseForce)-deltaGauge (phaseForce*phaseForce))=0 := by
    rw [hrel,map_smul,hgg,smul_zero]
  rw [hgr,hg0,smul_zero,hrel,smul_smul]
  module

theorem actual_source_bulk_phase_negative_square :
    bulkAction=(-(2*(phaseCoefficient:ℂ))⁻¹) •
      inverseWeightedBulkJet phaseHamiltonianSquare+
      (-8*(phaseCoefficient:ℂ)⁻¹) • (phaseForce*phaseForce) := by
  rw [actual_source_bulk_phase_square,actual_phase_force_square_ward,smul_smul]
  rw [mul_comm (phaseCoefficient:ℂ)⁻¹ (-8)]

private theorem phase_force_formula :
    phaseForce=Complex.I • (offsetAction*diagonalAction-diagonalAction*offsetAction) := by
  unfold phaseForce phaseJet phaseGenerator
  simp only [LinearMap.coe_mk,AddHom.coe_mk,smul_mul_assoc,mul_smul_comm,smul_sub]

theorem actual_phase_force_pair(f g:QuantumTest):
    sourcePair f (phaseForce g)=sourcePair (phaseForce f) g := by
  have hoff(f g:QuantumTest):sourcePair f (offsetAction g)=sourcePair (offsetAction f) g :=
    multiply_pair _ _ _ _
  rw [phase_force_formula]
  simp only [LinearMap.smul_apply,LinearMap.sub_apply,Module.End.mul_apply,sourcePair,map_smul,map_sub,
    inner_smul_right,inner_smul_left,inner_sub_right,inner_sub_left,starRingEnd_apply]
  change Complex.I*(sourcePair f (offsetAction (diagonalAction g))-
      sourcePair f (diagonalAction (offsetAction g)))=
    star Complex.I*(sourcePair (offsetAction (diagonalAction f)) g-
      sourcePair (diagonalAction (offsetAction f)) g)
  rw [hoff f (diagonalAction g),diagonalAction_pair (offsetAction f) g,
    diagonalAction_pair f (offsetAction g),hoff (diagonalAction f) g]
  simp only [Complex.star_def,Complex.conj_I]
  ring

/-- The positive force square is read on the original core, without a bounded extension. -/
theorem actual_phase_force_square_energy(f:QuantumTest):
    (sourcePair f ((phaseForce*phaseForce) f)).re=‖embed (phaseForce f)‖^2 := by
  change (sourcePair f (phaseForce (phaseForce f))).re=_
  rw [actual_phase_force_pair]
  exact inner_self_eq_norm_sq (𝕜:=ℂ) (embed (phaseForce f))

theorem actual_inverse_form_phase_square(f:QuantumTest):
    inverseForm f+(8/phaseCoefficient)*‖embed (phaseForce f)‖^2=
      (-(1/(2*phaseCoefficient)))*(sourcePair f (inverseWeightedBulkJet phaseHamiltonianSquare f)).re := by
  have h:=congrArg (fun A:End=>(sourcePair f (A f)).re) actual_source_bulk_phase_negative_square
  rw [original_bulk_energy] at h
  simp only [LinearMap.add_apply,LinearMap.smul_apply,sourcePair,map_add,map_smul,
    inner_add_right,inner_smul_right,Complex.add_re] at h
  have h2:-(2*(phaseCoefficient:ℂ))⁻¹=((-(1/(2*phaseCoefficient)):ℝ):ℂ) := by
    push_cast
    simp only [one_div]
  have h8:-8*(phaseCoefficient:ℂ)⁻¹=((-(8/phaseCoefficient):ℝ):ℂ) := by
    push_cast
    simp only [div_eq_mul_inv,neg_mul]
  rw [h2,h8] at h
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at h
  have hs:=actual_phase_force_square_energy f
  change (inner ℂ (embed f) (embed ((phaseForce*phaseForce) f))).re=‖embed (phaseForce f)‖^2 at hs
  rw [hs] at h
  change inverseForm f=(-(1/(2*phaseCoefficient)))*
    (sourcePair f (inverseWeightedBulkJet phaseHamiltonianSquare f)).re+
    (-(8/phaseCoefficient))*‖embed (phaseForce f)‖^2 at h
  linarith only [h]

theorem actual_inverse_form_phase_square_price(f:QuantumTest):
    inverseForm f≤(-(1/(2*phaseCoefficient)))*
      (sourcePair f (inverseWeightedBulkJet phaseHamiltonianSquare f)).re := by
  have h:=actual_inverse_form_phase_square f
  have hn:0≤(8/phaseCoefficient)*‖embed (phaseForce f)‖^2:=
    mul_nonneg (div_nonneg (by norm_num) actual_phase_coefficient_positive.le) (sq_nonneg _)
  linarith only [h,hn]

end LowEnergy.ActualPhaseBulkSquare
