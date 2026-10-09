import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiLocalClockReturn
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.FirstCurrentWholeVariance
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussLiveMomentum GaussNativeForm GaussNativeEnergy
open GaussNativePotential GaussDiagonalHistory GaussCoframeForm GaussMatterCore GaussQuantumMultiplier GaussFockWeights
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceCoframeVolume SourceCoframeCovariantSquare SourceCoframeCovariantAction FirstCurrentPayerNext
open SourceClockPhiCoframeForwardCore ClockPhiHeatCorrectedCovarianceSource ClockPhiConservativeHeatSource
open SourceClockPhiActualCovarianceStep SourceClockPhiCoframeForwardPair
open scoped ContDiff
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := LinearOrder.toDecidableEq
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] GaussQuantumMultiplier.quantized GaussCoframeSpin.full
private abbrev numberMatrix : Matrix Mode Mode ℂ := Matrix.diagonal (fun _=>1)

def localHamiltonianField(z:SourceCoordinateSlice):FockFiber→L[ℂ]FockFiber:=
  ((potential z+volumePotential z:ℝ):ℂ) • (1:FockFiber→L[ℂ]FockFiber)+
  (∑i:Fin 3,∑b:Fin 3,quantized (localMatrix i b z))+
  (∑a:Fin 7,((residualWeight a*inverseVolume z:ℝ):ℂ) •
    (quantized (GaussCoframeSpin.full a)*quantized (GaussCoframeSpin.full a)))+
  (numberCoefficient z:ℂ) • quantized numberMatrix
private theorem localHamiltonian_smooth(z:physicalChart):ContDiffAt ℝ ∞ localHamiltonianField z.val:=by
  have hp:ContDiffAt ℝ ∞ (fun x=>(potential x+volumePotential x:ℝ)) z.val:=
    (potential_smooth z).add (volumePotential_smooth z)
  have hpc:ContDiffAt ℝ ∞ (fun x=>((potential x+volumePotential x:ℝ):ℂ)) z.val:=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z.val hp
  have hs(a:Fin 7):ContDiffAt ℝ ∞ (fun x=>((residualWeight a*inverseVolume x:ℝ):ℂ)) z.val:=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z.val (contDiffAt_const.mul (inverseVolume_smooth z))
  have hn:ContDiffAt ℝ ∞ (fun x=>(numberCoefficient x:ℂ)) z.val:=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z.val (numberCoefficient_smooth z)
  exact (((hpc.smul contDiffAt_const).add (ContDiffAt.sum (fun i _=>ContDiffAt.sum (fun b _=>local_smooth i b z)))).add
    (ContDiffAt.sum (fun a _=>(hs a).smul contDiffAt_const))).add (hn.smul contDiffAt_const)
private theorem localHamiltonian_number(z:SourceCoordinateSlice)(c:ℕ→ℂ):Commute (weight c) (localHamiltonianField z):=by
  unfold localHamiltonianField
  apply Commute.add_right
  · apply Commute.add_right
    · apply Commute.add_right
      · exact (Commute.one_right _).smul_right _
      · exact Commute.sum_right Finset.univ _ _ (fun i _=>Commute.sum_right Finset.univ _ _ (fun b _=>weight_commute c _))
    · exact Commute.sum_right Finset.univ _ _ (fun a _=>((weight_commute c _).mul_right (weight_commute c _)).smul_right _)
  · exact (weight_commute c _).smul_right _

/-- The zero-order field is assembled from the literal potential, all matter matrices,
seven signed currents and Number shift of the original Hamiltonian. -/
theorem actual_H0_local_split:
    diagonalAction=scalarKinetic+gaugeKinetic+SourceCoframeCovariantAction.covariantKinetic+
      localMultiplier localHamiltonianField localHamiltonian_smooth:=by
  rw [diagonalAction,nativeAction,original_coframe_covariant]
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  simp only[LinearMap.add_apply]
  change scalarKinetic f z+gaugeKinetic f z+(potential z:ℂ) • f z+
    (SourceCoframeCovariantAction.covariantKinetic f z+
      (∑a:Fin 7,(residualWeight a:ℂ) •
        quantized (GaussCoframeSpin.full a) ((inverseVolume z:ℂ) • (quantized (GaussCoframeSpin.full a) (f z))))+
      (1/2:ℂ) • (quantized numberMatrix ((numberCoefficient z:ℂ) • f z)+
        (numberCoefficient z:ℂ) • quantized numberMatrix (f z))+(volumePotential z:ℂ) • f z)+
    (∑i:Fin 3,∑b:Fin 3,quantized (localMatrix i b z) (f z))=
    scalarKinetic f z+gaugeKinetic f z+SourceCoframeCovariantAction.covariantKinetic f z+localHamiltonianField z (f z)
  simp only[localHamiltonianField,add_apply,sum_apply,
    smul_apply,mul_apply_eq_comp,one_apply_eq_self,
    map_smul]
  simp only[Complex.ofReal_add,Complex.ofReal_mul,smul_smul]
  module

def returnedLocalHamiltonian(t:ℝ)(ht:0<t)(ξ η:ℝ):End:=
  returnedLocalAction t ht ξ η localHamiltonianField localHamiltonian_smooth

def returnedHamiltonian(t:ℝ)(ht:0<t)(ξ η:ℝ):End:=
  returnedScalarKinetic t ht ξ η+returnedGaugeKinetic t ht ξ η+
    returnedCoframeKinetic t ht ξ η+returnedLocalHamiltonian t ht ξ η

/-- The full H0 acts on the actual K_s state through one generated returned second-order
source: native rows, all 36 covariant rows, original matter, signed spin and Number all remain. -/
theorem actual_corrected_H0_point_return(t:ℝ)(ht:0<t)(ξ η:ℝ):
    diagonalAction*correctedCompleteCore t ht ξ η=
      correctedCompleteCore t ht ξ η*returnedHamiltonian t ht ξ η:=by
  have hN:=actual_corrected_native_second_order t ht ξ η
  have hC:=actual_corrected_coframe_second_order t ht ξ η
  have hL:=actual_corrected_local_action t ht ξ η localHamiltonianField localHamiltonian_smooth localHamiltonian_number
  rw [actual_H0_local_split]
  simp only[add_mul,hN.1,hN.2,hC,hL,returnedHamiltonian,returnedLocalHamiltonian,mul_add]

private theorem complete_pair(t:ℝ)(ht:0<t)(ξ η:ℝ)(f g:QuantumTest):
    sourcePair (correctedCompleteCore t ht ξ η f) (correctedCompleteCore t ht ξ η g)=
      sourcePair (sourceGain (Real.sqrt t) f) (sourceGain (Real.sqrt t) g):=by
  change sourcePair (sourceForwardCore t ht.le (correctedProfileCore t ht ξ η (sourceGain (Real.sqrt t) f)))
    (sourceForwardCore t ht.le (correctedProfileCore t ht ξ η (sourceGain (Real.sqrt t) g)))=_
  rw [actual_forward_core_pair]
  exact clockProfileAction_pair _ _ _ _ _ _

/-- The actual full H0² pairing is returned before Gaussian integration; its ordered two
Hamiltonian legs are obtained from their original actions rather than from Q(H0)'s name. -/
theorem actual_corrected_H0_square_pair(t:ℝ)(ht:0<t)(ξ η:ℝ)(f g:QuantumTest):
    sourcePair (diagonalAction (correctedCompleteCore t ht ξ η f))
      (diagonalAction (correctedCompleteCore t ht ξ η g))=
    sourcePair (sourceGain (Real.sqrt t) (returnedHamiltonian t ht ξ η f))
      (sourceGain (Real.sqrt t) (returnedHamiltonian t ht ξ η g)):=by
  have hf:=LinearMap.congr_fun (actual_corrected_H0_point_return t ht ξ η) f
  have hg:=LinearMap.congr_fun (actual_corrected_H0_point_return t ht ξ η) g
  change diagonalAction (correctedCompleteCore t ht ξ η f)=correctedCompleteCore t ht ξ η (returnedHamiltonian t ht ξ η f) at hf
  change diagonalAction (correctedCompleteCore t ht ξ η g)=correctedCompleteCore t ht ξ η (returnedHamiltonian t ht ξ η g) at hg
  rw [hf,hg,complete_pair]
end LowEnergy.FirstCurrentWholeVariance
