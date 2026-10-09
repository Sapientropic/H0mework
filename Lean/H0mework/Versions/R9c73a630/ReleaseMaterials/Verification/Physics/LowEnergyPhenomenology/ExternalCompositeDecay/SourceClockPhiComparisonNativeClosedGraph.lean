import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiMatchedDiffusionSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatNativeClosedGraph
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiComparisonNativeClosedGraph
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourcePhysicalKineticSquare
open SourceClockPhiCombinedScalePressure SourceClockPhiNativeMatchedSource
open SourceClockPhiMatchedDiffusionSource SourceClockPhiHeatNativeClosedGraph SourceCoframeDilation
open SourceCoframeVolumeCurrent SymmetricGraphClosure
open scoped Topology InnerProductSpace
private abbrev Op:=QuantumTest →ₗ[ℂ] QuantumTest
private abbrev U:Op:=inverseVolumeAction
private abbrev D:Op:=combinedGenerator
private abbrev Dc:Op:=dilation

private theorem inverse_dilation:Dc*U-U*Dc=(2*Complex.I) • U:=by
  have h:=congrArg (fun A:Op=>(-2*Complex.I/3) • A) SourceScalarInverseBulk.inverse_coframe
  change (-2*Complex.I/3) • ((3*Complex.I/2) • (Dc*U-U*Dc))=(-2*Complex.I/3) • ((-3:ℂ) • U) at h
  simp only [smul_smul] at h
  have hi:(-2*Complex.I/3)*(3*Complex.I/2)=1:=by
    calc _= -(Complex.I*Complex.I):=by ring
         _=_:=by rw [Complex.I_mul_I];ring
  rw [hi,one_smul] at h
  convert! h using 1
  congr 1
  ring

private theorem U_pair(f g:QuantumTest):sourcePair (U f) g=sourcePair f (U g):=
  (multiply_pair _ _ f g).symm
private theorem UD_pair(f g:QuantumTest):sourcePair ((U*D) f) g= -sourcePair f ((U*D) g):=by
  have h:=actual_UD_formal_pair (coreEquiv f) (coreEquiv g)
  change inner ℂ (embed (weightedGenerator (coreEquiv.symm (coreEquiv f)))) (embed g)=
    inner ℂ (embed f) (embed ((-weightedGenerator) (coreEquiv.symm (coreEquiv g)))) at h
  rw [coreEquiv.symm_apply_apply,coreEquiv.symm_apply_apply] at h
  change sourcePair ((U*D) f) g=sourcePair f (-((U*D) g)) at h
  simpa only [sourcePair,map_neg,inner_neg_right] using h
private theorem DcU_pair(f g:QuantumTest):sourcePair ((Dc*U) f) g=sourcePair f ((U*Dc) g):=by
  change sourcePair (Dc (U f)) g=sourcePair f (U (Dc g))
  rw [←dilation_pair,U_pair]

private theorem B3_pair(f g:QuantumTest):sourcePair (driftClock f) g= -sourcePair f (driftClock g):=by
  have hc:U*Dc=Dc*U-(2*Complex.I) • U:=by
    linear_combination (norm:=module) -inverse_dilation
  simp only [driftClock,matchedColumn,LinearMap.add_apply,LinearMap.smul_apply]
  simp only [sourcePair,map_add,inner_add_left,inner_add_right,map_smul,inner_smul_left,inner_smul_right]
  change sourcePair ((U*D) f) g+(starRingEnd ℂ (3*Complex.I))*sourcePair ((Dc*U) f) g+
    (starRingEnd ℂ (3:ℂ))*sourcePair (U f) g=
    -(sourcePair f ((U*D) g)+(3*Complex.I)*sourcePair f ((Dc*U) g)+(3:ℂ)*sourcePair f (U g))
  rw [UD_pair,DcU_pair,U_pair,hc]
  simp only [LinearMap.sub_apply,LinearMap.smul_apply,sourcePair,map_sub,map_smul,
    inner_sub_right,inner_smul_right,map_mul,map_ofNat,Complex.conj_I]
  linear_combination (norm:=ring) (6*inner ℂ (embed f) (embed (U g))) * Complex.I_mul_I

theorem actual_B3_formal_pair:
    FormalAdjointPair (realize driftClock) (realize (-driftClock)):=by
  intro f g
  obtain ⟨f,rfl⟩:=coreEquiv.surjective f
  obtain ⟨g,rfl⟩:=coreEquiv.surjective g
  change inner ℂ (embed (driftClock (coreEquiv.symm (coreEquiv f)))) (embed g)=
    inner ℂ (embed f) (embed ((-driftClock) (coreEquiv.symm (coreEquiv g))))
  rw [coreEquiv.symm_apply_apply,coreEquiv.symm_apply_apply]
  have h:=B3_pair f g
  simpa only [LinearMap.neg_apply,sourcePair,map_neg,inner_neg_right] using h

theorem actual_B3_closed_graph_singlevalued {x y z:H}
    (hy:(x,y)∈closedGraph (realize driftClock))
    (hz:(x,z)∈closedGraph (realize driftClock)):y=z:=
  closed_graph_single_valued _ _ (realize_dense _) actual_B3_formal_pair hy hz
end LowEnergy.SourceClockPhiComparisonNativeClosedGraph
