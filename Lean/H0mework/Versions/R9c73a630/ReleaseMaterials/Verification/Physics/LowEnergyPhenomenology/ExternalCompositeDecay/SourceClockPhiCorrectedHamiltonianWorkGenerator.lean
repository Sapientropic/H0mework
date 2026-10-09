import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCorrectedHamiltonianWorkEvolution
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiWholeSignedWorkIntegrable
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCorrectedCovarianceWeakJet
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ClockPhiCorrectedHamiltonianWorkGenerator
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert
open ClockPhiHeatCorrectedCovarianceSource ClockPhiCorrectedWorkComposition
open ClockPhiCorrectedHamiltonianWorkEvolution MeasureTheory Filter
open scoped Topology
private abbrev Pair:=ℝ×ℝ
private abbrev Quad:=Pair×Pair
private abbrev γ:=ProbabilityTheory.gaussianReal 0 1
private abbrev γ2:=γ.prod γ

def correctedHamiltonianPair(t:ℝ)(ht:0<t)(f g:QuantumTest):ℂ :=
  ∫x:Pair,sourcePair (correctedCompleteCore t ht x.1 x.2 f)
    (GaussDiagonalHistory.diagonalAction (correctedCompleteCore t ht x.1 x.2 g)) ∂γ2

def correctedHamiltonianWork(t:ℝ)(ht:0<t)(f g:QuantumTest):ℂ :=
  correctedHamiltonianPair t ht f g-sourcePair f (GaussDiagonalHistory.diagonalAction g)

theorem actual_corrected_hamiltonian_finite_work_increment(s t:ℝ)(hs:0<s)(ht:0<t)(f g:QuantumTest):
    Integrable (fun x:Pair=>correctedHamiltonianWork s hs
      (correctedCompleteCore t ht x.1 x.2 f) (correctedCompleteCore t ht x.1 x.2 g)) γ2 ∧
    correctedHamiltonianPair (s+t) (add_pos hs ht) f g-correctedHamiltonianPair t ht f g=
      ∫x:Pair,correctedHamiltonianWork s hs
        (correctedCompleteCore t ht x.1 x.2 f) (correctedCompleteCore t ht x.1 x.2 g) ∂γ2 := by
  let P:Quad→ℂ:=fun x=>sourcePair
    (correctedCompleteCore s hs x.2.1 x.2.2 (correctedCompleteCore t ht x.1.1 x.1.2 f))
    (GaussDiagonalHistory.diagonalAction
      (correctedCompleteCore s hs x.2.1 x.2.2 (correctedCompleteCore t ht x.1.1 x.1.2 g)))
  have he(x:Quad)(p:QuantumTest):
      correctedCompleteCore s hs x.2.1 x.2.2 (correctedCompleteCore t ht x.1.1 x.1.2 p)=
        composedCompleteCore s t hs ht x p:=
    LinearMap.congr_fun (actual_corrected_complete_composition s t hs ht x) p
  have h:=actual_composed_hamiltonian_gaussian s t hs ht f g
  have hP:Integrable P (γ2.prod γ2):=by
    simpa only [P,he] using h.1
  have hI:(∫x:Quad,P x ∂γ2.prod γ2)=correctedHamiltonianPair (s+t) (add_pos hs ht) f g:=by
    simpa only [P,he,correctedHamiltonianPair] using h.2.2
  have hO:Integrable (fun x:Pair=>correctedHamiltonianPair s hs
      (correctedCompleteCore t ht x.1 x.2 f) (correctedCompleteCore t ht x.1 x.2 g)) γ2:=
    hP.integral_prod_left
  have hT:=ClockPhiHeatCorrectedHamiltonianSource.actual_corrected_hamiltonian_gaussian t ht f g
  refine ⟨hO.sub hT.1,?_⟩
  change _=(∫x:Pair,correctedHamiltonianPair s hs
    (correctedCompleteCore t ht x.1 x.2 f) (correctedCompleteCore t ht x.1 x.2 g)-
    sourcePair (correctedCompleteCore t ht x.1 x.2 f)
      (GaussDiagonalHistory.diagonalAction (correctedCompleteCore t ht x.1 x.2 g)) ∂γ2)
  rw [integral_sub hO hT.1]
  change _=(∫x:Pair,∫y:Pair,P (x,y) ∂γ2 ∂γ2)-correctedHamiltonianPair t ht f g
  rw [←integral_prod P hP,hI]

end LowEnergy.ClockPhiCorrectedHamiltonianWorkGenerator
