import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualCandidateQuarticGram

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.ActualCandidateQuarticGram
open SaturationMonoid.PhysicsCore
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge ActualMotherCAR
open SourceCoframeSpinNormalOrder
open scoped BigOperators InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := SourceRealScalarFock.branchOrder.toDecidableEq

def pairColumns (A B : Matrix Mode Mode ℂ) (a b c i j k : Mode) : ℂ :=
  B a i*A b j*delta c k - B a i*A c j*delta b k -
  B b i*A a j*delta c k + B c i*A a j*delta b k +
  B b i*A c j*delta a k - B c i*A b j*delta a k

private theorem actual_pair_columns (A B : Matrix Mode Mode ℂ) (a b c i j k : Mode) :
    (∑r : Mode,∑s : Mode,B r i*A s j*tripleGram a b c r s k) =
      pairColumns A B a b c i j k := by
  classical
  simp [tripleGram, delta, pairColumns, mul_sub, mul_add,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

private theorem gram_swap (a b c r s k : Mode) :
    tripleGram a b c r k s = -tripleGram a b c r s k := by
  simp only [tripleGram]
  ring

private theorem gram_swap_first (a b c r s k : Mode) :
    tripleGram a b c s r k = -tripleGram a b c r s k := by
  simp only [tripleGram]
  ring

private theorem gram_cycle (a b c r s k : Mode) :
    tripleGram a b c k r s = tripleGram a b c r s k := by
  simp only [tripleGram]
  ring

/-- The full mother-Mode sums are eliminated by the original CAR deltas.
Only the six input/bra mode coordinates occur in this degree-two polynomial. -/
def normalTripleFinite (A B : Matrix Mode Mode ℂ) (a b c i j k : Mode) : ℂ :=
  pairColumns A B a b c i j k - pairColumns A B a b c i k j -
  pairColumns A B a b c j i k + pairColumns A B a b c j k i +
  pairColumns A B a b c k i j - pairColumns A B a b c k j i

theorem actual_normal_triple_finite (A B : Matrix Mode Mode ℂ) (a b c i j k : Mode) :
    inner ℂ (triple a b c) (normalFiber A B (triple i j k)) =
      normalTripleFinite A B a b c i j k := by
  rw [actual_normal_triple_pair]
  unfold twoColumnPair normalTripleFinite
  have h2 : (∑r : Mode,∑s : Mode,B r i*A s k*tripleGram a b c r j s) =
      -pairColumns A B a b c i k j := by
    rw [←actual_pair_columns A B a b c i k j]
    simp only [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    rw [gram_swap a b c r s j]
    ring
  have h3 : (∑r : Mode,∑s : Mode,B r j*A s i*tripleGram a b c s r k) =
      -pairColumns A B a b c j i k := by
    rw [←actual_pair_columns A B a b c j i k]
    simp only [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    rw [gram_swap_first a b c r s k]
    ring
  have h4 : (∑r : Mode,∑s : Mode,B r j*A s k*tripleGram a b c i r s) =
      pairColumns A B a b c j k i := by
    rw [←actual_pair_columns A B a b c j k i]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    rw [gram_cycle a b c r s i]
  have h5 : (∑r : Mode,∑s : Mode,B r k*A s i*tripleGram a b c s j r) =
      pairColumns A B a b c k i j := by
    rw [←actual_pair_columns A B a b c k i j]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    rw [←gram_cycle a b c s j r]
  have h6 : (∑r : Mode,∑s : Mode,B r k*A s j*tripleGram a b c i s r) =
      -pairColumns A B a b c k j i := by
    rw [←actual_pair_columns A B a b c k j i]
    simp only [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    rw [gram_cycle a b c s r i, gram_swap_first a b c r s i]
    ring
  rw [actual_pair_columns, h2, h3, h4, h5, h6]
  ring

def candidateMode (dual : Bool) (t : Fin 2) (p : Fin 6) (slot : Fin 3) : Mode :=
  MixedSpectatorCandidate.rootMode dual
    ((![![0,1,2],![0,0,3]] t) slot, NamedMatterWedgeQt.colorPerm p slot,
      if slot = 2 then 1 else 0)

def candidateCoefficient (t : Fin 2) (p : Fin 6) : ℂ :=
  (if t = 0 then (1/3 : ℂ) else -1/3) * NamedMatterWedgeQt.colorSign p

private theorem named_triple (dual : Bool) (i j k : MixedSpectatorCandidate.NamedMode) :
    MixedSpectatorCandidate.orderedTriple dual i j k =
      triple (MixedSpectatorCandidate.rootMode dual i)
        (MixedSpectatorCandidate.rootMode dual j) (MixedSpectatorCandidate.rootMode dual k) := rfl

theorem actual_candidate_sum (dual : Bool) :
    MixedSpectatorCandidate.candidate dual =
      ∑t : Fin 2,∑p : Fin 6,candidateCoefficient t p •
        triple (candidateMode dual t p 0) (candidateMode dual t p 1) (candidateMode dual t p 2) := by
  simp [Fin.sum_univ_two, MixedSpectatorCandidate.candidate, MixedSpectatorCandidate.epsilon,
    candidateCoefficient, candidateMode, named_triple, smul_sub, Finset.smul_sum, smul_smul]
  simp only [neg_div, one_div, neg_mul, neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg]

/-- The literal mixed-spectator candidate generates its own finite two-body
matrix polynomial, without an occupation-space enumeration or a Gram premise. -/
def candidateNormalFinite (dual : Bool) (A B : Matrix Mode Mode ℂ) : ℂ :=
  ∑u : Fin 2,∑q : Fin 6,∑t : Fin 2,∑p : Fin 6,
    candidateCoefficient u q * star (candidateCoefficient t p) *
      normalTripleFinite A B
        (candidateMode dual t p 0) (candidateMode dual t p 1) (candidateMode dual t p 2)
        (candidateMode dual u q 0) (candidateMode dual u q 1) (candidateMode dual u q 2)

theorem actual_candidate_normal_finite (dual : Bool) (A B : Matrix Mode Mode ℂ) :
    inner ℂ (MixedSpectatorCandidate.candidate dual)
      (normalFiber A B (MixedSpectatorCandidate.candidate dual)) =
        candidateNormalFinite dual A B := by
  rw [actual_candidate_sum]
  simp only [candidateNormalFinite, map_sum, map_smul, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, actual_normal_triple_finite, starRingEnd_apply,
    Finset.mul_sum, mul_assoc]

end LowEnergy.ActualCandidateQuarticGram
