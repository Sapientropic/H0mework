import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiSecondPressure
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceScalarAffineMixedJets
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualCausalBulkBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ActualMixedResolventWard
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open SourceScalarPairedTransport SourceClockYukawaCubicCurrent SourceScalarPositiveBulkWard
open SourceScalarVirialBulk SourceScalarGaugeScale SourceClockPhiSecondBulk
open SourceResolventBandLimit FullYSourceResolventGraphSplice
open scoped InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] compressionCore resolventCore defectAction

private def comm {R : Type*} [Ring R] (a b : R) : R := a*b-b*a

private theorem comm_mul {R : Type*} [Ring R] (d a b : R) :
    comm d (a*b)=comm d a*b+a*comm d b := by unfold comm; noncomm_ring

private theorem inverse_comm {R : Type*} [Ring R] (a r d : R)
    (hl : r*a=1) (hr : a*r=1) : comm d r= -r*comm d a*r := by
  have he : r*comm d a*r=r*d*(a*r)-(r*a)*d*r := by unfold comm; noncomm_ring
  rw [hr,hl,mul_one,one_mul] at he
  simp only [neg_mul]
  rw [he]
  unfold comm
  abel

private theorem inverse_mixed {R : Type*} [Ring R] (a r d e : R)
    (hl : r*a=1) (hr : a*r=1) :
    comm d (comm e r)=
      r*comm d a*r*comm e a*r+r*comm e a*r*comm d a*r-r*comm d (comm e a)*r := by
  rw [inverse_comm a r e hl hr]
  have hn (x : R) : comm d (-x)= -comm d x := by unfold comm; noncomm_ring
  rw [neg_mul,neg_mul,hn,comm_mul,comm_mul,inverse_comm a r d hl hr]
  noncomm_ring

private theorem inverse_second {R : Type*} [Ring R] (a r d e : R)
    (hl : r*a=1) (hr : a*r=1) :
    comm e r-comm d (comm e r)=
      -r*(comm e a-comm d (comm e a))*r-
        r*comm d a*r*comm e a*r-r*comm e a*r*comm d a*r := by
  rw [inverse_mixed a r d e hl hr,inverse_comm a r e hl hr]
  noncomm_ring

private theorem core_embed (F : Index) (z : ℂ) (hz : z.im≠0) (f : QuantumTest) :
    embed (resolventCore F z hz f)=finiteResolvent F z (embed f) := by
  unfold resolventCore state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem compression_embed (F : Index) (f : QuantumTest) :
    embed (compressionCore F f)=GaussGradedCompression.compression F (embed f) := by
  unfold compressionCore
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem actual_inverse (F : Index) (z : ℂ) (hz : z.im≠0) :
    resolventCore F z hz*(compressionCore F-z • (1:End))=1 ∧
    (compressionCore F-z • (1:End))*resolventCore F z hz=1 := by
  constructor
  · apply LinearMap.ext
    intro f
    apply embed_injective
    simp only [Module.End.mul_apply,LinearMap.sub_apply,LinearMap.smul_apply,
      Module.End.one_apply,core_embed,map_sub,map_smul,compression_embed]
    simpa only [mul_apply_eq_comp,sub_apply,
      smul_apply,one_apply_eq_self,map_sub,map_smul,finiteResolvent] using
      congrArg (fun A : H →L[ℂ] H => A (embed f))
      (resolvent_left _ (GaussGradedCompression.compression_selfAdjoint F) z hz)
  · apply LinearMap.ext
    intro f
    apply embed_injective
    simp only [Module.End.mul_apply,LinearMap.sub_apply,LinearMap.smul_apply,
      Module.End.one_apply,core_embed,map_sub,map_smul,compression_embed]
    exact congrArg (fun A : H →L[ℂ] H => A (embed f))
      (resolvent_right _ (GaussGradedCompression.compression_selfAdjoint F) z hz)

private theorem gauge_comm (A : End) : deltaGauge A=comm Gauge A :=
  (SourceGaugeScaleTransport.generator_commutator A).symm
private theorem difference_comm (A : End) : deltaPhi A-deltaGauge A=comm (Phi-Gauge) A := by
  rw [←SourceScalarAffineScaleTransport.generator_commutator,←SourceGaugeScaleTransport.generator_commutator]
  unfold comm
  noncomm_ring
private theorem second_comm (A : End) :
    secondJet A=comm (Phi-Gauge) A-comm Gauge (comm (Phi-Gauge) A) := by
  change (deltaPhi A-deltaGauge A)-deltaGauge (deltaPhi A-deltaGauge A)=_
  rw [difference_comm,gauge_comm]

private theorem comm_spectral (d A : End) (z : ℂ) : comm d (A-z • (1:End))=comm d A := by
  unfold comm
  simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,mul_one,one_mul]
  abel

/-- The actual two source variations differentiate the full original inverse. Both mixed
resolvent orders survive, including the original escape-space action. -/
theorem actual_mixed_inverse (F : Index) (z : ℂ) (hz : z.im≠0) :
    let R:=resolventCore F z hz
    let C:=compressionCore F
    secondJet R= -R*secondJet C*R-
      R*deltaGauge C*R*(deltaPhi C-deltaGauge C)*R-
      R*(deltaPhi C-deltaGauge C)*R*deltaGauge C*R := by
  dsimp only
  rw [second_comm,second_comm,difference_comm,gauge_comm]
  have h:=inverse_second (compressionCore F-z • (1:End)) (resolventCore F z hz)
    Gauge (Phi-Gauge) (actual_inverse F z hz).1 (actual_inverse F z hz).2
  simpa only [comm_spectral] using h

/-- The original positive mixed bulk is returned through its own resolvent, with the
complete second OwnDefect and both ordered cross terms still in the same expression. -/
theorem actual_source_bulk_return (F : Index) (z : ℂ) (hz : z.im≠0) :
    let R:=resolventCore F z hz
    let C:=compressionCore F
    R*secondBulk*R=
      -secondJet R-R*deltaGauge C*R*(deltaPhi C-deltaGauge C)*R-
      R*(deltaPhi C-deltaGauge C)*R*deltaGauge C*R+
      R*secondJet (defectAction F)*R+(1/2:ℂ) • (R*vacuumConstantAction*R) := by
  dsimp only
  rw [←actual_second_compression_source F]
  have h:=actual_mixed_inverse F z hz
  dsimp only at h
  simp only [mul_add,add_mul,mul_smul_comm,smul_mul_assoc]
  linear_combination (norm := noncomm_ring) h

end LowEnergy.ActualMixedResolventWard
