import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualCoframeVectorReturn
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeBulk
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiSecondBulk
import Lean.Elab.Term

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ActualInverseCurrentCoframeReturn
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open SourceMixedNativeReturn SourceGaugeCoframeJets SourceGaugeCoframeWard
open SourcePhysicalKineticSquare SourceCoframeVolumeCurrent SourceScalarVirialBulk SourceScalarGaugeScale
open SourceClockPhiSecondBulk SourceCoframeVolume
open SourceScalarInverseBulk SourceJointScaleBudget SourceEscapeCurrent SourceMinimalGraphParticular
open FullYSourceResolventGraphSplice SourceScalarPairedTransport SourceResolventBandLimit
open ActualCoframeVectorReturn Lean Meta Elab Term
open scoped InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H

elab "paid_coframe_inverse%" field:ident : term => do
  let ns := Name.str (Name.str (Name.num `_private.H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeCoframeNeutralSplice 0) "LowEnergy") "SourceInverseCoframeNeutralSplice"
  let n := Name.str ns field.getId.toString
  unless (←getEnv).contains n do throwError "Missing original source coframe proof"
  mkConstWithFreshMVarLevels n

elab "paid_coframe_vector%" field:ident : term => do
  let ns := Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualCoframeVectorReturn 0) "LowEnergy") "ActualCoframeVectorReturn"
  let n := Name.str ns field.getId.toString
  unless (←getEnv).contains n do throwError "Missing original vector orbit proof"
  mkConstWithFreshMVarLevels n

elab "paid_inverse_bulk%" field:ident : term => do
  let ns := Name.str (Name.str (Name.num `_private.H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeBulk 0) "LowEnergy") "SourceScalarInverseBulk"
  let n := Name.str ns field.getId.toString
  unless (←getEnv).contains n do throwError "Missing original inverse-volume source proof"
  mkConstWithFreshMVarLevels n

attribute [local irreducible] diagonalAction inverseVolumeAction compressionCore sourceRead finiteResolvent
  sandwichJet readOrbitJet inverseCross

def hamiltonianCurrent : End := diagonalAction*inverseVolumeAction-inverseVolumeAction*diagonalAction

def compressedCurrent (F : Index) : End :=
  compressionCore F*inverseVolumeAction-inverseVolumeAction*compressionCore F

def ownCurrent (F : Index) : End :=
  defectAction F*inverseVolumeAction-inverseVolumeAction*defectAction F

/-- Both H inverse/input corrections and the entire own-projection current remain coherent. -/
def completeReturn (F : Index) (seed : diagonal.domain) (z : ℂ) : Op :=
  inverseCross F seed z hamiltonianCurrent 1 0+
    finiteResolvent F z*inputFlux F seed hamiltonianCurrent 1 0*finiteResolvent F z-
    (sandwichJet F seed z (ownCurrent F) 1 0 0 0+
      (6:ℂ) • (finiteResolvent F z*sourceRead F seed (ownCurrent F)*finiteResolvent F z))

private theorem hamiltonian_return (F : Index) (seed : diagonal.domain) (z : ℂ) (hz : z.im≠0) :
    sandwichJet F seed z hamiltonianCurrent 1 0 0 0+
      (6:ℂ) • (finiteResolvent F z*sourceRead F seed hamiltonianCurrent*finiteResolvent F z)=
    inverseCross F seed z hamiltonianCurrent 1 0+
      finiteResolvent F z*inputFlux F seed hamiltonianCurrent 1 0*finiteResolvent F z := by
  have hi := (paid_coframe_inverse% inverse_cross_small) F seed z hz hamiltonianCurrent 1 (by omega)
  have hw : SourceHamiltonianScaleJet.scaleDerivative hamiltonianCurrent=(-6:ℂ) • hamiltonianCurrent :=
    original_inverse_volume_current_weight
  have hf : inputFlux F seed hamiltonianCurrent 1 0=
      readOrbitJet F seed hamiltonianCurrent 1 0 0 0-
        sourceRead F seed (SourceHamiltonianScaleJet.scaleDerivative hamiltonianCurrent) := by
    simp only [inputFlux,coreJet,pow_zero,pow_one,Module.End.one_apply]
  rw [hw,map_smul] at hf
  have hr:=congrArg (fun A:Op=>finiteResolvent F z*A*finiteResolvent F z) hf
  simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc] at hr
  linear_combination (norm := module) -hi-hr

/-- Source weight −6 eliminates the bare H current; no CF/H replacement is made. -/
theorem actual_compressed_inverse_current_return (F : Index) (seed : diagonal.domain)
    (z : ℂ) (hz : z.im≠0) :
    sandwichJet F seed z (compressedCurrent F) 1 0 0 0+
      (6:ℂ) • (finiteResolvent F z*sourceRead F seed (compressedCurrent F)*finiteResolvent F z)=
        completeReturn F seed z := by
  have hs : compressedCurrent F=hamiltonianCurrent-ownCurrent F := by
    unfold compressedCurrent hamiltonianCurrent ownCurrent defectAction
    noncomm_ring
  have h1 := (paid_coframe_inverse% sandwich_sub) F seed z hamiltonianCurrent (ownCurrent F) 1 0
  rw [←hs] at h1
  have h0:=congrArg (fun A:End=>finiteResolvent F z*sourceRead F seed A*finiteResolvent F z) hs
  simp only [map_sub,mul_sub,sub_mul] at h0
  have hH:=hamiltonian_return F seed z hz
  unfold completeReturn
  linear_combination (norm := module) h1+(6:ℂ) • h0+hH

attribute [local irreducible] hamiltonianCurrent compressedCurrent ownCurrent completeReturn

/-- The source-specific coframe gain applies to the actual [CF,U] word. -/
theorem actual_compressed_inverse_current_price (F : Index) (seed : diagonal.domain)
    (z : ℂ) (hz : z.im≠0) :
    6*‖finiteResolvent F z*sourceRead F seed (compressedCurrent F)*finiteResolvent F z‖≤
      ‖completeReturn F seed z‖ := by
  have h:=actual_sandwich_shift_price F seed z hz (compressedCurrent F) 6
  exact h.trans_eq (congrArg norm (actual_compressed_inverse_current_return F seed z hz))

/-- The bounded read returns precisely the same original compressed inverse-volume current. -/
theorem actual_compressed_inverse_current_vector (F : Index) (g : QuantumTest)
    (z : ℂ) (hz : z.im≠0) :
    (finiteResolvent F z*sourceRead F (coreEquiv g) (compressedCurrent F)*finiteResolvent F z) (embed g)=
      finiteResolvent F z (embed (compressedCurrent F
        (coreEquiv.symm (sourceCore F z hz (coreEquiv g))))) := by
  have h:=source_read_resolvent F (coreEquiv g) (compressedCurrent F) z hz
  change finiteResolvent F z (sourceRead F (coreEquiv g) (compressedCurrent F)
    (finiteResolvent F z (embed g)))=_
  exact congrArg (finiteResolvent F z) h

/-- The original inverse-volume H-current has no scalar-affine source derivative. -/
theorem actual_hamiltonian_current_phi : deltaPhi hamiltonianCurrent=0 := by
  unfold hamiltonianCurrent
  exact InverseVolumeWardAlgebra.inverse_current_invariant deltaPhi
    (paid_inverse_bulk% phi_product) diagonalAction volumeAction inverseVolumeAction
    (paid_inverse_bulk% volume_right) (paid_inverse_bulk% volume_left)
    inverse_phi (paid_inverse_bulk% current_phi)

/-- Gauge invariance is paid by the original volume current, including the actual kinetic action. -/
theorem actual_hamiltonian_current_gauge : deltaGauge hamiltonianCurrent=0 := by
  unfold hamiltonianCurrent
  exact InverseVolumeWardAlgebra.inverse_current_invariant deltaGauge
    (paid_inverse_bulk% gauge_product) diagonalAction volumeAction inverseVolumeAction
    (paid_inverse_bulk% volume_right) (paid_inverse_bulk% volume_left)
    inverse_gauge (paid_inverse_bulk% current_gauge)

/-- Only the middle native H-current disappears; surrounding resolvent derivatives are unchanged. -/
theorem actual_hamiltonian_current_second : secondJet hamiltonianCurrent=0 := by
  simp only [secondJet,LinearMap.comp_apply,LinearMap.sub_apply,
    actual_hamiltonian_current_phi,actual_hamiltonian_current_gauge,sub_self,map_zero]

/-- The entire mixed derivative of the compressed middle current is exactly its own-defect return. -/
theorem actual_compressed_current_second (F : Index) :
    secondJet (compressedCurrent F)= -secondJet (ownCurrent F) := by
  have hs : compressedCurrent F=hamiltonianCurrent-ownCurrent F := by
    unfold compressedCurrent hamiltonianCurrent ownCurrent defectAction
    noncomm_ring
  rw [hs,map_sub,actual_hamiltonian_current_second,zero_sub]

private theorem hamiltonian_product (A B : End) :
    secondJet (A*hamiltonianCurrent*B)=
      secondJet A*hamiltonianCurrent*B+A*hamiltonianCurrent*secondJet B-
      deltaGauge A*hamiltonianCurrent*(deltaPhi B-deltaGauge B)-
      (deltaPhi A-deltaGauge A)*hamiltonianCurrent*deltaGauge B := by
  simp only [secondJet,LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.id_apply,
    (paid_inverse_bulk% phi_product),(paid_inverse_bulk% gauge_product),map_add,map_sub,
    actual_hamiltonian_current_phi,actual_hamiltonian_current_gauge,
    mul_zero,add_zero]
  noncomm_ring

/-- The full returned word keeps its four ordered outer derivatives and the whole OwnDefect. -/
theorem actual_mixed_inverse_current_product (F : Index) (A B : End) :
    secondJet (A*compressedCurrent F*B)=
      secondJet A*hamiltonianCurrent*B+A*hamiltonianCurrent*secondJet B-
      deltaGauge A*hamiltonianCurrent*(deltaPhi B-deltaGauge B)-
      (deltaPhi A-deltaGauge A)*hamiltonianCurrent*deltaGauge B-
      secondJet (A*ownCurrent F*B) := by
  have hs : compressedCurrent F=hamiltonianCurrent-ownCurrent F := by
    unfold compressedCurrent hamiltonianCurrent ownCurrent defectAction
    noncomm_ring
  rw [hs,mul_sub,sub_mul,map_sub,hamiltonian_product]

end LowEnergy.ActualInverseCurrentCoframeReturn
