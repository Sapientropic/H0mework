import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualCandidateSupportPolynomial
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000
noncomputable section
namespace LowEnergy.ActualCandidateBra
open SaturationMonoid.PhysicsCore
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open ActualCandidateVertexEntries ActualCandidateQuarticGram ActualMotherCAR SourceCoframeSpinNormalOrder
open scoped BigOperators InnerProductSpace

def bra (dual : Bool) : FockFiber :=
  triple (supportMode dual (0,0)) (supportMode dual (1,1)) (supportMode dual (2,2))

private theorem support_delta (dual : Bool) (i j : Support) :
    delta (supportMode dual i) (supportMode dual j) =
      ActualCandidateSupportPolynomial.supportDelta i j := by
  have hinj : Function.Injective (supportMode dual) := by
    intro i j h
    have hn := (MixedSpectatorCandidate.modeEmbedding dual).injective h
    exact Prod.ext (congrArg (fun v : MixedSpectatorCandidate.NamedMode => v.1) hn)
      (congrArg (fun v : MixedSpectatorCandidate.NamedMode => v.2.1) hn)
  simp only [delta, ActualCandidateSupportPolynomial.supportDelta, hinj.eq_iff]

private theorem support_triple (dual : Bool) (A B : Matrix Mode Mode ℂ)
    (a b c i j k : Support) :
    normalTripleFinite A B (supportMode dual a) (supportMode dual b) (supportMode dual c)
      (supportMode dual i) (supportMode dual j) (supportMode dual k) =
    ActualCandidateSupportPolynomial.normalTriple
      (fun i j => A (supportMode dual i) (supportMode dual j))
      (fun i j => B (supportMode dual i) (supportMode dual j)) a b c i j k := by
  simp only [normalTripleFinite, ActualCandidateQuarticGram.pairColumns,
    ActualCandidateSupportPolynomial.normalTriple, ActualCandidateSupportPolynomial.pairColumns,
    support_delta]

def polynomial (A B : Matrix Support Support ℂ) : ℂ :=
  ∑u : Fin 2,∑q : Fin 6,candidateCoefficient u q *
    ActualCandidateSupportPolynomial.normalTriple A B (0,0) (1,1) (2,2)
      (ActualCandidateSupportPolynomial.supportColumn u q 0)
      (ActualCandidateSupportPolynomial.supportColumn u q 1)
      (ActualCandidateSupportPolynomial.supportColumn u q 2)

/-- This fixed bra reads the same actual full504 candidate through the
original normalFiber, before any source coefficients are evaluated. -/
theorem actual_bra_normal (dual : Bool) (A B : Matrix Mode Mode ℂ) :
    inner ℂ (bra dual) (normalFiber A B (MixedSpectatorCandidate.candidate dual)) =
      polynomial (fun i j => A (supportMode dual i) (supportMode dual j))
        (fun i j => B (supportMode dual i) (supportMode dual j)) := by
  rw [actual_candidate_sum]
  simp only [map_sum, map_smul, inner_sum, inner_smul_right, bra,
    actual_normal_triple_finite, actual_candidate_support, support_triple,
    polynomial, ActualCandidateSupportPolynomial.supportColumn]

def tensor (A B : Matrix Support Support ℂ) : ℂ :=
  (1/3) * A (0,0) (0,0) * B (1,1) (1,1)
  + (-1/3) * A (0,0) (0,1) * B (1,1) (1,0)
  + (1/3) * A (0,0) (1,0) * B (1,1) (0,1)
  + (-1/3) * A (0,0) (1,1) * B (1,1) (0,0)
  + (1/3) * A (0,0) (0,0) * B (2,2) (2,2)
  + (-1/3) * A (0,0) (0,2) * B (2,2) (2,0)
  + (1/3) * A (0,0) (2,0) * B (2,2) (0,2)
  + (-1/3) * A (0,0) (2,2) * B (2,2) (0,0)
  + (-1/3) * A (1,1) (0,0) * B (0,0) (1,1)
  + (1/3) * A (1,1) (0,1) * B (0,0) (1,0)
  + (-1/3) * A (1,1) (1,0) * B (0,0) (0,1)
  + (1/3) * A (1,1) (1,1) * B (0,0) (0,0)
  + (-2/3) * A (1,1) (0,1) * B (2,2) (3,2)
  + (2/3) * A (1,1) (0,2) * B (2,2) (3,1)
  + (1/3) * A (1,1) (1,1) * B (2,2) (2,2)
  + (-1/3) * A (1,1) (1,2) * B (2,2) (2,1)
  + (1/3) * A (1,1) (2,1) * B (2,2) (1,2)
  + (-1/3) * A (1,1) (2,2) * B (2,2) (1,1)
  + (-2/3) * A (1,1) (3,1) * B (2,2) (0,2)
  + (2/3) * A (1,1) (3,2) * B (2,2) (0,1)
  + (-1/3) * A (2,2) (0,0) * B (0,0) (2,2)
  + (1/3) * A (2,2) (0,2) * B (0,0) (2,0)
  + (-1/3) * A (2,2) (2,0) * B (0,0) (0,2)
  + (1/3) * A (2,2) (2,2) * B (0,0) (0,0)
  + (2/3) * A (2,2) (0,1) * B (1,1) (3,2)
  + (-2/3) * A (2,2) (0,2) * B (1,1) (3,1)
  + (-1/3) * A (2,2) (1,1) * B (1,1) (2,2)
  + (1/3) * A (2,2) (1,2) * B (1,1) (2,1)
  + (-1/3) * A (2,2) (2,1) * B (1,1) (1,2)
  + (1/3) * A (2,2) (2,2) * B (1,1) (1,1)
  + (2/3) * A (2,2) (3,1) * B (1,1) (0,2)
  + (-2/3) * A (2,2) (3,2) * B (1,1) (0,1)

theorem actual_bra_tensor (A B : Matrix Support Support ℂ) :
    polynomial A B = tensor A B := by
  norm_num [polynomial, ActualCandidateSupportPolynomial.normalTriple,
    ActualCandidateSupportPolynomial.pairColumns, ActualCandidateSupportPolynomial.supportColumn,
    candidateCoefficient, NamedMatterWedgeQt.colorPerm, NamedMatterWedgeQt.colorSign,
    ActualCandidateSupportPolynomial.supportDelta, Fin.sum_univ_succ, tensor,
    Prod.mk.injEq, starRingEnd_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  simp +decide
  ring

end LowEnergy.ActualCandidateBra
