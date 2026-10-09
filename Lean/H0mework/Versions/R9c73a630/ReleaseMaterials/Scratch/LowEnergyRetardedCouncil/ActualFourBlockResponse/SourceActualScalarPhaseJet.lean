import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceScalarShiftedBulk
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedCompressionShape
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualWeightedWardInputSplit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualScalarPhaseJet
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussDiagonalHistory
open GaussNativeEnergy GaussNativeForm GaussLiveMomentum GaussCoframeForm
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceScalarShiftedBulk SourceScalarOscillatorAbsorption SourceScalarPositiveBulkWard
open SourcePhysicalKineticSquare SourceCoframeVolume SourceScalarPairedTransport
open ActualMixedCompressionShape ActualMixedWindowGram ActualWeightedWardInputSplit
open GaussUnitaryHistory SourceDilationRemainder SourceClockYukawaCubicCurrent ActualMixedCovarianceTail
open SaturationMonoid.PhysicsCore StageNineDynamicBreakingVacuum StageNineEnrichedProofFreeSource
open FullYSourceResolventGraphSplice SourceResolventBandLimit
open Lean Meta Elab Term
open scoped BigOperators InnerProductSpace ContDiff
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
local instance labelFintype : Fintype NativeHistoryGrade.Label := Fintype.ofFinite _

elab "paid_offset_phase%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceScalarShiftedBulk 0) "LowEnergy") "SourceScalarShiftedBulk"
  let name:=Name.str ns field.getId.eraseMacroScopes.toString
  unless (←getEnv).contains name do throwError "Missing original offset-source proof"
  mkConstWithFreshMVarLevels name

/-- The actual vacuum direction fixes the phase; no free scalar direction is selected. -/
def phaseGenerator : End := Complex.I • offsetAction

/-- The phase is a literal original-core multiplier; support and all fermionic grades are preserved. -/
def phaseFlow(t:ℝ):End :=
  localMultiplier (fun z=>Complex.exp (Complex.I*(t:ℂ)*(offsetCoefficient z:ℂ)) •
    ContinuousLinearMap.id ℂ FockFiber) (fun z=>by
      have ho:ContDiffAt ℝ ∞ (fun w:SourceCoordinateSlice=>(offsetCoefficient w:ℂ)) z.val :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp z.val ((paid_offset_phase% offset_smooth).contDiffAt)
      have h:ContDiffAt ℝ ∞ (fun w:SourceCoordinateSlice=>Complex.I*(t:ℂ)*(offsetCoefficient w:ℂ)) z.val :=
        contDiffAt_const.mul ho
      exact h.cexp.smul contDiffAt_const)

theorem actual_phase_flow_apply(t:ℝ)(f:QuantumTest)(z:SourceCoordinateSlice):
    phaseFlow t f z=Complex.exp (Complex.I*(t:ℂ)*(offsetCoefficient z:ℂ)) • f z := rfl

theorem actual_phase_generator_apply(f:QuantumTest)(z:SourceCoordinateSlice):
    phaseGenerator f z=(Complex.I*(offsetCoefficient z:ℂ)) • f z := by
  simp only [phaseGenerator,LinearMap.smul_apply,smul_apply,offsetAction,multiply_apply,smul_smul]

def phaseJet : End →ₗ[ℂ] End where
  toFun A := phaseGenerator*A-A*phaseGenerator
  map_add' A B := by noncomm_ring
  map_smul' c A := by simp only [mul_smul_comm,smul_mul_assoc,smul_sub,RingHom.id_apply]

def phaseSecond : End →ₗ[ℂ] End := phaseJet.comp phaseJet

private theorem phase_mul (A B:End):phaseJet (A*B)=phaseJet A*B+A*phaseJet B := by
  simp only [phaseJet,LinearMap.coe_mk,AddHom.coe_mk]
  noncomm_ring

private theorem phase_one : phaseJet (1:End)=0 := by simp [phaseJet]

theorem actual_phase_second_product (A B:End):
    phaseSecond (A*B)=phaseSecond A*B+A*phaseSecond B+(2:ℂ) • (phaseJet A*phaseJet B) := by
  simp only [phaseSecond,LinearMap.comp_apply,phase_mul,map_add]
  module

private theorem phase_offset (A:End):
    phaseJet A=Complex.I • (offsetAction*A-A*offsetAction) := by
  simp only [phaseJet,phaseGenerator,LinearMap.coe_mk,AddHom.coe_mk,smul_mul_assoc,mul_smul_comm,smul_sub]

theorem actual_phase_inverse_volume : phaseJet inverseVolumeAction=0 := by
  rw [phase_offset]
  have h:Commute inverseVolumeAction offsetAction:=(paid_offset_phase% real_offset) _ _
  rw [h.eq,sub_self,smul_zero]

private theorem phase_hamiltonian_first :
    phaseJet diagonalAction=((sourceTime 0:ℂ)^2/2) • vacuumSymmetric := by
  have hs:diagonalAction=scalarKinetic+localAction+remainingHamiltonian := by
    unfold remainingHamiltonian scalarHamiltonian
    abel
  have hlocal:Commute localAction offsetAction:=(paid_offset_phase% real_offset) _ _
  have hremaining:=original_remaining_offset
  have hscalar:scalarKinetic*offsetAction-offsetAction*scalarKinetic=
    (Complex.I*(sourceTime 0:ℂ)^2/2) • vacuumSymmetric:=(paid_offset_phase% scalar_offset)
  rw [phase_offset,hs]
  have he:offsetAction*(scalarKinetic+localAction+remainingHamiltonian)-
    (scalarKinetic+localAction+remainingHamiltonian)*offsetAction=
      -(scalarKinetic*offsetAction-offsetAction*scalarKinetic) := by
    simp only [mul_add,add_mul,hlocal.eq,hremaining.eq]
    noncomm_ring
  rw [he,hscalar,smul_neg,smul_smul]
  ring_nf
  simp [Complex.I_sq]

private theorem phase_vacuum_symmetric :
    phaseJet vacuumSymmetric=(-2*(sourceTime 0:ℂ)*(‖vacuum‖^2:ℂ)) • inverseVolumeAction := by
  unfold vacuumSymmetric
  simp only [map_sum,map_smul,map_add,phase_mul,actual_phase_inverse_volume,mul_zero,zero_mul,add_zero,zero_add]
  have hp(a:ScalarIndex):phaseJet (covariantMomentum (scalarDirection a))=
      (-(sourceTime 0:ℂ)*(inner ℝ (scalarBasis a) vacuum:ℂ)) • (1:End) := by
    rw [phase_offset]
    have h:=original_offset_momentum (scalarDirection a)
    change _=(-Complex.I*(sourceTime 0:ℂ)*(inner ℝ (scalarBasis a) vacuum:ℂ)) • (1:End) at h
    rw [←neg_sub,h,smul_neg,smul_smul]
    ring_nf
    simp [Complex.I_sq]
  have ha(a:ScalarIndex):phaseJet (GaussMomentumAdjoint.adjoint (scalarDirection a))=
      (-(sourceTime 0:ℂ)*(inner ℝ (scalarBasis a) vacuum:ℂ)) • (1:End) := by
    rw [phase_offset]
    have h:GaussMomentumAdjoint.adjoint (scalarDirection a)*offsetAction-
      offsetAction*GaussMomentumAdjoint.adjoint (scalarDirection a)=
      (-Complex.I*(sourceTime 0:ℂ)*(inner ℝ (scalarBasis a) vacuum:ℂ)) • (1:End) := by
      simpa only [scalarDirection] using (paid_offset_phase% adjoint_offset) (scalarDirection a)
    rw [←neg_sub,h,smul_neg,smul_smul]
    ring_nf
    simp [Complex.I_sq]
  simp only [hp,ha,smul_mul_assoc,mul_smul_comm,one_mul,mul_one,←add_smul,smul_smul]
  rw [←Finset.sum_smul]
  have hsum:(∑a:ScalarIndex,(inner ℝ (scalarBasis a) vacuum)^2)=‖vacuum‖^2 := by
    calc
      _=∑a:ScalarIndex,(inner ℝ vacuum (scalarBasis a))^2 := by
        apply Finset.sum_congr rfl
        intro a _
        rw [real_inner_comm (scalarBasis a) vacuum]
      _=_ := scalarBasis.sum_sq_inner_left vacuum
  have hsumC:(∑a:ScalarIndex,(inner ℝ (scalarBasis a) vacuum:ℂ)^2)=(‖vacuum‖:ℂ)^2 := by
    exact_mod_cast hsum
  have he:(∑a:ScalarIndex,(inner ℝ (scalarBasis a) vacuum:ℂ)*
    (-(sourceTime 0:ℂ)*(inner ℝ (scalarBasis a) vacuum:ℂ)+
      -(sourceTime 0:ℂ)*(inner ℝ (scalarBasis a) vacuum:ℂ)))=
      -2*(sourceTime 0:ℂ)*(‖vacuum‖^2:ℂ) := by
    calc
      _=∑a:ScalarIndex,(-2*(sourceTime 0:ℂ))*((inner ℝ (scalarBasis a) vacuum:ℂ)^2) := by
        apply Finset.sum_congr rfl
        intro a _
        ring
      _=(-2*(sourceTime 0:ℂ))*(∑a:ScalarIndex,(inner ℝ (scalarBasis a) vacuum:ℂ)^2) := by
        rw [Finset.mul_sum]
      _=_ := by rw [hsumC]
  rw [he]

/-- The original linked-skew vacuum phase generates the inverse volume itself. -/
theorem actual_source_inverse_volume_phase_jet :
    phaseSecond diagonalAction=
      (-(sourceTime 0:ℂ)^3*(‖vacuum‖^2:ℂ)) • inverseVolumeAction := by
  change phaseJet (phaseJet diagonalAction)=_
  rw [phase_hamiltonian_first,map_smul,phase_vacuum_symmetric,smul_smul]
  congr 1
  ring

def phaseCoefficient : ℝ := (sourceTime 0)^3*‖vacuum‖^2

theorem actual_phase_coefficient_positive : 0<phaseCoefficient := by
  have hn:0<sourceTime 0 := by
    rw [source_time_generated]
    exact Stage9C.Material.SpinPair.lapse_pos
  have hv:vacuum≠0 := by
    intro h
    apply positive_sourceGeneratedVacuumBase_nonzero
    apply scalarCoordinateEquiv.injective
    simpa only [vacuum,sourceGeneratedVacuumCoordinates,map_zero] using h
  exact mul_pos (pow_pos hn _) (sq_pos_of_pos (norm_pos_iff.mpr hv))

/-- U is generated from the source phase jet with an internally paid nonzero coefficient. -/
theorem actual_source_inverse_volume_from_phase :
    inverseVolumeAction=(-(phaseCoefficient:ℂ))⁻¹ • phaseSecond diagonalAction := by
  have he:phaseSecond diagonalAction=(-(phaseCoefficient:ℂ)) • inverseVolumeAction := by
    simpa only [phaseCoefficient,Complex.ofReal_mul,Complex.ofReal_pow,neg_mul] using actual_source_inverse_volume_phase_jet
  have hc:(phaseCoefficient:ℂ)≠0 := by exact_mod_cast actual_phase_coefficient_positive.ne'
  rw [he,smul_smul,inv_mul_cancel₀ (neg_ne_zero.mpr hc),one_smul]

private theorem phase_grade_zero(g:NativeHistoryGrade.Label):phaseJet (GaussCoreLabel.project g)=0 := by
  rw [phase_offset]
  have hc:offsetAction*GaussCoreLabel.project g=GaussCoreLabel.project g*offsetAction := by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    simp only [Module.End.mul_apply,offsetAction,multiply_apply,GaussCoreLabel.project_apply,map_smul]
  rw [hc,sub_self,smul_zero]

def phaseCross (A B C:End):End :=
  phaseJet A*phaseJet B*C+phaseJet A*B*phaseJet C+A*phaseJet B*phaseJet C

private theorem phase_second_triple(A B C:End):
    phaseSecond (A*B*C)=phaseSecond A*B*C+A*phaseSecond B*C+A*B*phaseSecond C+
      (2:ℂ) • phaseCross A B C := by
  simp only [actual_phase_second_product,phase_mul,phaseCross,two_smul]
  noncomm_ring

private theorem phase_second_grade(g:NativeHistoryGrade.Label)(A:End):
    phaseSecond (GaussCoreLabel.project g*A*GaussCoreLabel.project g)=
      GaussCoreLabel.project g*phaseSecond A*GaussCoreLabel.project g := by
  rw [phase_second_triple]
  have hz:phaseSecond (GaussCoreLabel.project g)=0 := by
    change phaseJet (phaseJet (GaussCoreLabel.project g))=0
    rw [phase_grade_zero]
    simp only [phaseJet,LinearMap.coe_mk,AddHom.coe_mk,mul_zero,zero_mul,sub_self]
  simp only [hz,phase_grade_zero,phaseCross,zero_mul,mul_zero,zero_add,add_zero,smul_zero]

/-- Both raw-P second jets and every ordered phase cross are retained. -/
def wholePhaseShape(F:Index):End :=
  ∑g:NativeHistoryGrade.Label,GaussCoreLabel.project g*
    (phaseSecond (projectionCore F)*diagonalAction*projectionCore F+
      projectionCore F*diagonalAction*phaseSecond (projectionCore F)+
      (2:ℂ) • phaseCross (projectionCore F) diagonalAction (projectionCore F))*GaussCoreLabel.project g

theorem actual_raw_phase_compression_shape(F:Index):
    phaseSecond (compressionCore F)=coreCompression F (phaseSecond diagonalAction)+wholePhaseShape F := by
  rw [actual_compression_core_identity]
  simp only [coreCompression,map_sum]
  simp_rw [show ∀g:NativeHistoryGrade.Label,
    phaseSecond (GaussCoreLabel.project g*projectionCore F*diagonalAction*projectionCore F*GaussCoreLabel.project g)=
      GaussCoreLabel.project g*phaseSecond (projectionCore F*diagonalAction*projectionCore F)*GaussCoreLabel.project g
    from fun g=>by simpa only [mul_assoc] using phase_second_grade g (projectionCore F*diagonalAction*projectionCore F)]
  simp only [wholePhaseShape,phase_second_triple,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro g _
  noncomm_ring

theorem actual_source_inverse_volume_compression_phase(F:Index):
    phaseSecond (compressionCore F)=
      (-(sourceTime 0:ℂ)^3*(‖vacuum‖^2:ℂ)) • coreCompression F inverseVolumeAction+wholePhaseShape F := by
  rw [actual_raw_phase_compression_shape,actual_source_inverse_volume_phase_jet]
  simp only [coreCompression,mul_smul_comm,smul_mul_assoc,Finset.smul_sum]

theorem actual_source_inverse_volume_own_phase(F:Index):
    phaseSecond (defectAction F)=
      (-(sourceTime 0:ℂ)^3*(‖vacuum‖^2:ℂ)) •
        (inverseVolumeAction-coreCompression F inverseVolumeAction)-wholePhaseShape F := by
  unfold defectAction
  rw [map_sub,actual_source_inverse_volume_phase_jet,actual_source_inverse_volume_compression_phase]
  module

/-- The actual weighted covariance consumes the phase-generated U without a weighted-family premise. -/
theorem actual_weighted_covariance_phase_input(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0):
    phaseSecond (weightedCovariance m ell F z hz)=
      phaseSecond (coreCovariance m ell F z hz)*inverseVolumeAction+
      phaseSecond (resolventCore F (star z) (by simpa only [Complex.star_def,Complex.conj_im] using neg_ne_zero.mpr hz)*
        SourceNativeCutoffContact.thetaAction m ell*SourceNativeCutoffContact.thetaAction m ell*coframeFlux F z hz) := by
  rw [actual_weighted_covariance_input,map_add,actual_phase_second_product,actual_phase_inverse_volume]
  have hs:phaseSecond inverseVolumeAction=0 := by
    change phaseJet (phaseJet inverseVolumeAction)=0
    rw [actual_phase_inverse_volume]
    simp only [phaseJet,LinearMap.coe_mk,AddHom.coe_mk,mul_zero,zero_mul,sub_self]
  simp only [hs,mul_zero,smul_zero,add_zero]

/-- The existing original weighted source pair now reads U from the actual phase of H0. -/
theorem actual_weighted_pair_phase_source(m ell:ℕ)(p q:QuantumTest):
    ActualWeightedWardFrequencyReturn.weightedPair m ell p q=
      (-(phaseCoefficient:ℂ))⁻¹*sourcePair (SourceNativeCutoffContact.thetaAction m ell p)
        (phaseSecond diagonalAction (SourceNativeCutoffContact.thetaAction m ell q)) := by
  unfold ActualWeightedWardFrequencyReturn.weightedPair
  rw [actual_source_inverse_volume_from_phase]
  simp only [LinearMap.smul_apply,sourcePair,map_smul,inner_smul_right]

theorem actual_weighted_covariance_phase_source(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0):
    weightedCovariance m ell F z hz=
      (-(phaseCoefficient:ℂ))⁻¹ •
        (resolventCore F (star z) (by simpa only [Complex.star_def,Complex.conj_im] using neg_ne_zero.mpr hz)*
          SourceNativeCutoffContact.thetaAction m ell*phaseSecond diagonalAction*
          SourceNativeCutoffContact.thetaAction m ell*resolventCore F z hz) := by
  unfold weightedCovariance
  rw [actual_source_inverse_volume_from_phase]
  simp only [mul_smul_comm,smul_mul_assoc]

end LowEnergy.ActualScalarPhaseJet
