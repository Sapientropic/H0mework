import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualPhaseBulkSquare
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceDilationMultiplier

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualPhaseWardIntertwiner
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open SourceScalarShiftedBulk SourceScalarVirialBulk SourceScalarGaugeScale SourceScalarPositiveBulkWard
open SourceScalarInverseBulk SourcePhysicalKineticSquare SourceCoframeVolume SourceCoframeVolumeCurrent
open SourceHamiltonianScaleJet SourceDilationMultiplier SourceKineticScale
open ActualScalarPhaseJet ActualPhaseBulkSquare
open GaussHistoryHilbert SourceQuantumFockGauge SourceClockYukawaCubicCurrent
open GaussNativePotential
open Lean Meta Elab Term
open scoped InnerProductSpace ContDiff
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

elab "paid_phase_shift_virial%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceScalarVirialBulk 0) "LowEnergy") "SourceScalarVirialBulk"
  mkConstWithFreshMVarLevels (Name.str ns field.getId.eraseMacroScopes.toString)

elab "paid_phase_shift_offset%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceScalarShiftedBulk 0) "LowEnergy") "SourceScalarShiftedBulk"
  mkConstWithFreshMVarLevels (Name.str ns field.getId.eraseMacroScopes.toString)

def offsetBias : ℝ := sourceTime 0*(3+(3/4:ℝ)*‖vacuum‖^2)
attribute [local irreducible] offsetBias phaseGenerator

private theorem actual_linear_vacuum_offset :
    vacuumLinearAction=volumeAction*(offsetAction+(offsetBias:ℂ) • (1:End)) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  unfold vacuumLinearAction volumeAction offsetAction
  simp only [Module.End.mul_apply,LinearMap.add_apply,LinearMap.smul_apply,Module.End.one_apply,multiply_apply,
    add_apply,smul_apply]
  change ((sourceTime 0*volume z*inner ℝ vacuum (scalarField z):ℝ):ℂ) • f z=
    (volume z:ℂ) • ((offsetCoefficient z:ℂ) • f z+(offsetBias:ℂ) • f z)
  rw [←add_smul,smul_smul,←Complex.ofReal_add,←Complex.ofReal_mul]
  apply congrArg (fun a:ℝ=>(a:ℂ) • f z)
  simp only [scalarField,inner_add_right,real_inner_self_eq_norm_sq,offsetCoefficient,offsetBias,
    real_inner_comm vacuum (z.2.1:Scalar)]
  ring

private theorem phi_product(A B:End):deltaPhi (A*B)=deltaPhi A*B+A*deltaPhi B := by
  change phiEulerAction*(A*B)-(A*B)*phiEulerAction=
    (phiEulerAction*A-A*phiEulerAction)*B+A*(phiEulerAction*B-B*phiEulerAction)
  noncomm_ring

private theorem source_inverse_volume_left : inverseVolumeAction*volumeAction=(1:End) := by
  have hc:inverseVolumeAction*volumeAction=volumeAction*inverseVolumeAction := by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    exact smul_comm (reciprocalVolume z:ℂ) (volume z:ℂ) (f z)
  have hv:volumeAction*inverseVolumeAction=(1:End) := by
    apply LinearMap.ext
    intro f
    exact volume_inverse f
  exact hc.trans hv

/-- The constant is forced by the original full-vacuum affine scalar generator. -/
theorem actual_source_offset_phi : deltaPhi offsetAction=offsetAction+(offsetBias:ℂ) • (1:End) := by
  have hv:inverseVolumeAction*vacuumLinearAction=offsetAction+(offsetBias:ℂ) • (1:End) := by
    let B:End:=offsetAction+(offsetBias:ℂ) • (1:End)
    calc
      inverseVolumeAction*vacuumLinearAction=inverseVolumeAction*(volumeAction*B) :=
        congrArg (fun A:End=>inverseVolumeAction*A) actual_linear_vacuum_offset
      _=(inverseVolumeAction*volumeAction)*B :=
        by apply LinearMap.ext;intro f;rfl
      _=(1:End)*B := congrArg (fun A:End=>A*B) source_inverse_volume_left
      _=B := by apply LinearMap.ext;intro f;rfl
  have hp0:deltaPhi (1:End)=0 := by
    change phiEulerAction*1-1*phiEulerAction=0
    simp only [mul_one,one_mul,sub_self]
  have h:=congrArg deltaPhi hv
  rw [phi_product,inverse_phi,zero_mul,zero_add,(paid_phase_shift_virial% vacuum_linear_phi),
    map_add,map_smul,hp0,smul_zero,add_zero,hv] at h
  exact h.symm

theorem actual_source_offset_gauge : deltaGauge offsetAction=0 :=
  (paid_phase_shift_virial% gauge_real) offsetCoefficient
    (fun _=>(paid_phase_shift_offset% offset_smooth).contDiffAt) (fun _ _=>rfl)

theorem actual_source_offset_coframe : scaleDerivative offsetAction=0 := by
  have hc:SourceCoframeVolumeCurrent.dilation*offsetAction-
      offsetAction*SourceCoframeVolumeCurrent.dilation=0 := by
    have he(z:physicalChart):fderiv ℝ offsetCoefficient z.val (SourceCoframeVolume.euler z.val)=0 := by
      have h:=euler_of_scale offsetCoefficient 0 z
        ((paid_phase_shift_offset% offset_smooth).contDiffAt)
        (fun r _=>by simp only [SourceCoframeVolume.scale,offsetCoefficient,zpow_zero,one_mul])
      simpa only [Int.cast_zero,zero_mul] using h
    have h:=homogeneous_multiplier offsetCoefficient
      (fun _=>(paid_phase_shift_offset% offset_smooth).contDiffAt) 0
      (fun z=>by simpa only [zero_mul] using he z)
    simpa only [offsetAction,Complex.ofReal_zero,mul_zero,zero_smul] using h
  change (3*Complex.I/2) • (SourceCoframeVolumeCurrent.dilation*offsetAction-
    offsetAction*SourceCoframeVolumeCurrent.dilation)=0
  rw [hc,smul_zero]

theorem actual_source_phase_generator_weights :
    deltaPhi phaseGenerator=phaseGenerator+(Complex.I*(offsetBias:ℂ)) • (1:End) ∧
      deltaGauge phaseGenerator=0 ∧ scaleDerivative phaseGenerator=0 := by
  unfold phaseGenerator
  rw [map_smul,map_smul,map_smul,actual_source_offset_phi,actual_source_offset_gauge,
    actual_source_offset_coframe]
  simp only [smul_add,smul_smul,smul_zero,and_self]

private def comm {R:Type*}[Ring R](a b:R):R:=a*b-b*a
private theorem comm_exchange {R:Type*}[Ring R](a b x:R):
    comm a (comm b x)-comm b (comm a x)=comm (comm a b) x := by
  unfold comm
  noncomm_ring

theorem actual_source_phi_phase_first(A:End):
    deltaPhi (phaseJet A)=phaseJet (deltaPhi A)+phaseJet A := by
  have h:=comm_exchange phiEulerAction phaseGenerator A
  have hp:=actual_source_phase_generator_weights.1
  change phiEulerAction*phaseGenerator-phaseGenerator*phiEulerAction=
    phaseGenerator+(Complex.I*(offsetBias:ℂ)) • (1:End) at hp
  unfold comm at h
  rw [hp] at h
  change (phiEulerAction*(phaseGenerator*A-A*phaseGenerator)-
    (phaseGenerator*A-A*phaseGenerator)*phiEulerAction)-
      (phaseGenerator*(phiEulerAction*A-A*phiEulerAction)-
        (phiEulerAction*A-A*phiEulerAction)*phaseGenerator)=_ at h
  change phiEulerAction*(phaseGenerator*A-A*phaseGenerator)-
    (phaseGenerator*A-A*phaseGenerator)*phiEulerAction=
      (phaseGenerator*(phiEulerAction*A-A*phiEulerAction)-
        (phiEulerAction*A-A*phiEulerAction)*phaseGenerator)+(phaseGenerator*A-A*phaseGenerator)
  simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm,one_mul,mul_one] at h
  linear_combination (norm:=module) h

theorem actual_source_phi_phase_second(A:End):
    deltaPhi (phaseSecond A)=phaseSecond (deltaPhi A)+(2:ℂ) • phaseSecond A := by
  change deltaPhi (phaseJet (phaseJet A))=_
  rw [actual_source_phi_phase_first,actual_source_phi_phase_first,map_add]
  simp only [phaseSecond,LinearMap.comp_apply]
  module

theorem actual_source_gauge_phase_first(A:End):
    deltaGauge (phaseJet A)=phaseJet (deltaGauge A) := by
  have h:=comm_exchange SourceGaugeRadialPair.gaugeEulerAction phaseGenerator A
  have hp:=actual_source_phase_generator_weights.2.1
  change SourceGaugeRadialPair.gaugeEulerAction*phaseGenerator-
    phaseGenerator*SourceGaugeRadialPair.gaugeEulerAction=0 at hp
  unfold comm at h
  rw [hp,zero_mul,mul_zero,sub_self] at h
  exact sub_eq_zero.mp h

theorem actual_source_gauge_phase_second(A:End):
    deltaGauge (phaseSecond A)=phaseSecond (deltaGauge A) := by
  change deltaGauge (phaseJet (phaseJet A))=phaseJet (phaseJet (deltaGauge A))
  rw [actual_source_gauge_phase_first,actual_source_gauge_phase_first]

theorem actual_source_coframe_phase_first(A:End):
    scaleDerivative (phaseJet A)=phaseJet (scaleDerivative A) := by
  let K:End:=SourceGaugeCoframeJets.K
  have hp:=actual_source_phase_generator_weights.2.2
  rw [←SourceGaugeCoframeJets.K_commutator] at hp
  change K*phaseGenerator-phaseGenerator*K=0 at hp
  have h:=comm_exchange K phaseGenerator A
  unfold comm at h
  rw [hp,zero_mul,mul_zero,sub_self] at h
  rw [←SourceGaugeCoframeJets.K_commutator,←SourceGaugeCoframeJets.K_commutator]
  exact sub_eq_zero.mp h

theorem actual_source_coframe_phase_second(A:End):
    scaleDerivative (phaseSecond A)=phaseSecond (scaleDerivative A) := by
  change scaleDerivative (phaseJet (phaseJet A))=phaseJet (phaseJet (scaleDerivative A))
  rw [actual_source_coframe_phase_first,actual_source_coframe_phase_first]

/-- This is the source-forced weight shift in the polynomial, not a new physical generator. -/
def phiShiftTwo : End →ₗ[ℂ] End := deltaPhi+(2:ℂ) • LinearMap.id

private theorem phi_shift_apply(A:End):phiShiftTwo A=deltaPhi A+(2:ℂ) • A := rfl

private theorem source_phase_phi_shift(A:End):
    deltaPhi (phaseSecond A)=phaseSecond (phiShiftTwo A) := by
  rw [actual_source_phi_phase_second,phi_shift_apply,map_add,map_smul]

def shiftedInverseWard(A:End):End :=
  InverseVolumeWardAlgebra.inverseWard phiShiftTwo deltaGauge scaleDerivative
    (vacuumJetCoefficient:ℂ) A

/-- The entire mixed, affine and coframe polynomial crosses the actual source phase.
All three coframe derivatives and the true vacuum coefficient remain in one word. -/
theorem actual_source_inverse_ward_phase_shift(A:End):
    inverseWeightedBulkJet (phaseSecond A)=phaseSecond (shiftedInverseWard A) := by
  unfold inverseWeightedBulkJet shiftedInverseWard InverseVolumeWardAlgebra.inverseWard
    InverseVolumeWardAlgebra.mixedPolynomial InverseVolumeWardAlgebra.affinePolynomial
    InverseVolumeWardAlgebra.inverseLocalPolynomial
  simp only [map_add,map_sub,map_smul,smul_add,smul_sub]
  simp only [source_phase_phi_shift,actual_source_gauge_phase_second,
    actual_source_coframe_phase_second]

attribute [local irreducible] inverseWeightedBulkJet shiftedInverseWard phaseHamiltonianSquare phaseForce phaseSecond

/-- The original positive inverse form is now a phase-second return of an
unweighted source H0 square, with its real force square still retained. -/
theorem actual_inverse_form_shifted_source_square(f:QuantumTest):
    SourceScalarInverseNativeEnergy.inverseForm f+
      (8/phaseCoefficient)*‖embed (phaseForce f)‖^2=
      (-(1/(2*phaseCoefficient)))*(sourcePair f
        (phaseSecond (shiftedInverseWard (GaussDiagonalHistory.diagonalAction*
          GaussDiagonalHistory.diagonalAction)) f)).re := by
  have h:=actual_inverse_form_phase_square f
  have he:inverseWeightedBulkJet phaseHamiltonianSquare=
      phaseSecond (shiftedInverseWard (GaussDiagonalHistory.diagonalAction*
        GaussDiagonalHistory.diagonalAction)) := by
    unfold phaseHamiltonianSquare
    exact actual_source_inverse_ward_phase_shift _
  rw [he] at h
  exact h

end LowEnergy.ActualPhaseWardIntertwiner
