import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualCandidateVertexEntries

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
noncomputable section
namespace LowEnergy.ActualCandidateSupportPolynomial
open SaturationMonoid.PhysicsCore
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open ActualCandidateVertexEntries ActualCandidateQuarticGram ActualMotherCAR
open scoped BigOperators

private theorem support_injective (dual : Bool) : Function.Injective (supportMode dual) := by
  intro i j h
  have hn := (MixedSpectatorCandidate.modeEmbedding dual).injective h
  exact Prod.ext (congrArg (fun v : MixedSpectatorCandidate.NamedMode => v.1) hn)
    (congrArg (fun v : MixedSpectatorCandidate.NamedMode => v.2.1) hn)

def supportDelta (i j : Support) : ℂ := if i = j then 1 else 0

private theorem support_delta (dual : Bool) (i j : Support) :
    delta (supportMode dual i) (supportMode dual j) = supportDelta i j := by
  simp only [delta, supportDelta, (support_injective dual).eq_iff]

def supportColumn (t : Fin 2) (p : Fin 6) (slot : Fin 3) : Support :=
  (((![![0,1,2],![0,0,3]] t) slot), NamedMatterWedgeQt.colorPerm p slot)

def pairColumns (A B : Matrix Support Support ℂ) (a b c i j k : Support) : ℂ :=
  B a i*A b j*supportDelta c k - B a i*A c j*supportDelta b k -
  B b i*A a j*supportDelta c k + B c i*A a j*supportDelta b k +
  B b i*A c j*supportDelta a k - B c i*A b j*supportDelta a k

def normalTriple (A B : Matrix Support Support ℂ) (a b c i j k : Support) : ℂ :=
  pairColumns A B a b c i j k - pairColumns A B a b c i k j -
  pairColumns A B a b c j i k + pairColumns A B a b c j k i +
  pairColumns A B a b c k i j - pairColumns A B a b c k j i

def polynomial (A B : Matrix Support Support ℂ) : ℂ :=
  ∑u : Fin 2,∑q : Fin 6,∑t : Fin 2,∑p : Fin 6,
    candidateCoefficient u q * star (candidateCoefficient t p) *
      normalTriple A B (supportColumn t p 0) (supportColumn t p 1) (supportColumn t p 2)
        (supportColumn u q 0) (supportColumn u q 1) (supportColumn u q 2)

/-- Restrict only the matrix entries surviving the literal three-particle CAR
contraction; no intermediate one-body product is compressed. -/
theorem actual_support_polynomial (dual : Bool) (A B : Matrix Mode Mode ℂ) :
    candidateNormalFinite dual A B =
      polynomial (fun i j => A (supportMode dual i) (supportMode dual j))
        (fun i j => B (supportMode dual i) (supportMode dual j)) := by
  simp only [candidateNormalFinite, actual_candidate_support, polynomial, supportColumn,
    normalTripleFinite, ActualCandidateQuarticGram.pairColumns, normalTriple, pairColumns,
    support_delta]

end LowEnergy.ActualCandidateSupportPolynomial
