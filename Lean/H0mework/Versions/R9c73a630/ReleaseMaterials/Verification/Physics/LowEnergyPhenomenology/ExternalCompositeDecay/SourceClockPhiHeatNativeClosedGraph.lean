import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiMatchedNoiseCore
import H0mework.Physics.LowEnergy.Quantum.SymmetricGraphClosure
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiHeatNativeClosedGraph
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourcePhysicalKineticSquare
open SourceClockPhiCombinedScalePressure ClockPhiMatchedNoiseCore SymmetricGraphClosure
open scoped Topology InnerProductSpace
private abbrev Op:=QuantumTest →ₗ[ℂ] QuantumTest

def weightedGenerator : Op := inverseVolumeAction*combinedGenerator
private theorem source_U_pair (f g : QuantumTest) :
    sourcePair (inverseVolumeAction f) g=sourcePair f (inverseVolumeAction g) :=
  (multiply_pair _ _ f g).symm
private theorem source_A_pair (f g : QuantumTest) :
    sourcePair (combinedConjugate f) g= -sourcePair f (combinedConjugate g) := by
  have h:=noiseGenerator_pair 1 0 f g
  simp only [noiseGenerator,Complex.ofReal_one,one_smul,Complex.ofReal_zero,zero_smul,add_zero] at h
  have hh:=congrArg Neg.neg h
  simpa only [neg_neg] using hh.symm
private theorem source_UD_pair (f g : QuantumTest) :
    sourcePair (weightedGenerator f) g= -sourcePair f (weightedGenerator g) := by
  have h:=noiseGenerator_pair 0 1 f g
  simp only [noiseGenerator,Complex.ofReal_zero,zero_smul,Complex.ofReal_one,one_smul,zero_add] at h
  change sourcePair f (weightedGenerator g)= -sourcePair (weightedGenerator f) g at h
  have hh:=congrArg Neg.neg h
  simpa only [neg_neg] using hh.symm
private theorem realize_source_pair (L R : Op)
    (h:∀f g : QuantumTest,sourcePair (L f) g=sourcePair f (R g)) :
    FormalAdjointPair (realize L) (realize R) := by
  intro f g
  obtain ⟨f,rfl⟩:=coreEquiv.surjective f
  obtain ⟨g,rfl⟩:=coreEquiv.surjective g
  change inner ℂ (embed (L (coreEquiv.symm (coreEquiv f)))) (embed g)=
    inner ℂ (embed f) (embed (R (coreEquiv.symm (coreEquiv g))))
  rw [coreEquiv.symm_apply_apply,coreEquiv.symm_apply_apply]
  exact h f g

theorem actual_U_formal_pair :
    FormalAdjointPair (realize inverseVolumeAction) (realize inverseVolumeAction) :=
  realize_source_pair _ _ source_U_pair

theorem actual_A_formal_pair :
    FormalAdjointPair (realize combinedConjugate) (realize (-combinedConjugate)) := by
  apply realize_source_pair
  intro f g
  rw [source_A_pair]
  change -sourcePair f (combinedConjugate g)=sourcePair f (-(combinedConjugate g))
  simp only [sourcePair,map_neg,inner_neg_right]

theorem actual_UD_formal_pair :
    FormalAdjointPair (realize weightedGenerator) (realize (-weightedGenerator)) := by
  apply realize_source_pair
  intro f g
  rw [source_UD_pair]
  change -sourcePair f (weightedGenerator g)=sourcePair f (-(weightedGenerator g))
  simp only [sourcePair,map_neg,inner_neg_right]

theorem actual_U_closed_graph_singlevalued {x y z : H}
    (hy:(x,y)∈closedGraph (realize inverseVolumeAction))
    (hz:(x,z)∈closedGraph (realize inverseVolumeAction)) : y=z :=
  closed_graph_single_valued _ _ (realize_dense _) actual_U_formal_pair hy hz

theorem actual_A_closed_graph_singlevalued {x y z : H}
    (hy:(x,y)∈closedGraph (realize combinedConjugate))
    (hz:(x,z)∈closedGraph (realize combinedConjugate)) : y=z :=
  closed_graph_single_valued _ _ (realize_dense _) actual_A_formal_pair hy hz

theorem actual_UD_closed_graph_singlevalued {x y z : H}
    (hy:(x,y)∈closedGraph (realize weightedGenerator))
    (hz:(x,z)∈closedGraph (realize weightedGenerator)) : y=z :=
  closed_graph_single_valued _ _ (realize_dense _) actual_UD_formal_pair hy hz
end LowEnergy.SourceClockPhiHeatNativeClosedGraph
