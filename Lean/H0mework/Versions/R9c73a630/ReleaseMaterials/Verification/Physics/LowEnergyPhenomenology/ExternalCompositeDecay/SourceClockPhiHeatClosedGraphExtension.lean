import H0mework.Physics.LowEnergy.Quantum.SymmetricGraphClosure
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiMatchedNoiseCore
import Mathlib.Analysis.Normed.Operator.Extend
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiHeatClosedGraphExtension
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open Set
open scoped Topology
private abbrev Op:=QuantumTest →ₗ[ℂ] QuantumTest

def boundedOutput (B : QuantumTest →ₗ[ℂ] H) : H →L[ℂ] H :=
  B.extendOfNorm embed

theorem bounded_output_on_core (B : QuantumTest →ₗ[ℂ] H) (C : ℝ)
    (hB:∀f : QuantumTest,‖B f‖≤C*‖embed f‖) (f : QuantumTest) :
    boundedOutput B (embed f)=B f :=
  LinearMap.extendOfNorm_eq SourceCoframeScaleTransport.embed_dense ⟨C,hB⟩ f

theorem bounded_output_norm (B : QuantumTest →ₗ[ℂ] H) (C : ℝ)
    (hB:∀f : QuantumTest,‖B f‖≤C*‖embed f‖) (v : H) :
    ‖boundedOutput B v‖≤C*‖v‖ :=
  LinearMap.norm_extendOfNorm_apply_le SourceCoframeScaleTransport.embed_dense C hB v

/-- Only the source-bounded output is extended; membership remains in the original graph closure. -/
theorem actual_closed_graph_dense_extension (L : Op) (T : H →L[ℂ] H)
    (B : QuantumTest →ₗ[ℂ] H) (C : ℝ)
    (hB:∀f : QuantumTest,‖B f‖≤C*‖embed f‖)
    (hgraph:∀f : QuantumTest,(T (embed f),B f)∈SymmetricGraphClosure.closedGraph (realize L))
    (v : H) :
    (T v,boundedOutput B v)∈SymmetricGraphClosure.closedGraph (realize L) ∧
      ‖boundedOutput B v‖≤C*‖v‖ := by
  refine ⟨?_,bounded_output_norm B C hB v⟩
  apply SourceCoframeScaleTransport.embed_dense.induction_on
    (p:=fun w : H=>(T w,boundedOutput B w)∈SymmetricGraphClosure.closedGraph (realize L)) v
  · exact (realize L).graph.isClosed_topologicalClosure.preimage
      (T.continuous.prodMk (boundedOutput B).continuous)
  · intro f
    rw [bounded_output_on_core B C hB f]
    exact hgraph f
end LowEnergy.SourceClockPhiHeatClosedGraphExtension
