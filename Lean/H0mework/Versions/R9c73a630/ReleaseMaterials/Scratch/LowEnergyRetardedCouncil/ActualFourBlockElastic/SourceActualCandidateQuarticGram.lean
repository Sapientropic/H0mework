import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.NamedColorQtNext.Charge.ActualMotherTripleGram
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCoframeSpinNormalOrder
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.NamedColorQtNext.Charge.MixedSpectatorCandidate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.ActualCandidateQuarticGram
open SaturationMonoid.PhysicsCore
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open ActualMotherCAR GaussQuantumMultiplier SourceCoframeSpinNormalOrder
open scoped BigOperators InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := SourceRealScalarFock.branchOrder.toDecidableEq

private theorem composition_column (A B : Matrix Mode Mode ℂ) (j : Mode)
    (v : Mode → FockFiber) :
    (∑r : Mode,∑s : Mode,(B r j * A s r) • v s) =
      ∑s : Mode,(A*B) s j • v s := by
  rw [Finset.sum_comm]
  simp only [Matrix.mul_apply, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro r _
  rw [mul_comm]

/-- Only the six replacements of two distinct particle columns survive
the actual CAR subtraction; same-column composition is removed exactly. -/
def twoColumn (A B : Matrix Mode Mode ℂ) (i j k : Mode) : FockFiber :=
  (∑r : Mode,∑s : Mode,(B r i*A s j) • triple r s k) +
  (∑r : Mode,∑s : Mode,(B r i*A s k) • triple r j s) +
  (∑r : Mode,∑s : Mode,(B r j*A s i) • triple s r k) +
  (∑r : Mode,∑s : Mode,(B r j*A s k) • triple i r s) +
  (∑r : Mode,∑s : Mode,(B r k*A s i) • triple s j r) +
  (∑r : Mode,∑s : Mode,(B r k*A s j) • triple i s r)

theorem actual_normal_triple (A B : Matrix Mode Mode ℂ) (i j k : Mode) :
    normalFiber A B (triple i j k) = twoColumn A B i j k := by
  have h := congrArg (fun T : FockFiber →L[ℂ] FockFiber => T (triple i j k))
    (original_fiber_normal_order A B)
  simp only [mul_apply_eq_comp, _root_.add_apply] at h
  rw [actual_quantized_triple B] at h
  simp only [map_add, map_sum, map_smul] at h
  simp_rw [actual_quantized_triple] at h
  simp only [smul_add, Finset.smul_sum, Finset.sum_add_distrib, smul_smul] at h
  rw [composition_column A B i (fun r => triple r j k),
    composition_column A B j (fun r => triple i r k),
    composition_column A B k (fun r => triple i j r)] at h
  dsimp only [twoColumn]
  linear_combination (norm := module) -h

def twoColumnPair (A B : Matrix Mode Mode ℂ) (a b c i j k : Mode) : ℂ :=
  (∑r : Mode,∑s : Mode,B r i*A s j*tripleGram a b c r s k) +
  (∑r : Mode,∑s : Mode,B r i*A s k*tripleGram a b c r j s) +
  (∑r : Mode,∑s : Mode,B r j*A s i*tripleGram a b c s r k) +
  (∑r : Mode,∑s : Mode,B r j*A s k*tripleGram a b c i r s) +
  (∑r : Mode,∑s : Mode,B r k*A s i*tripleGram a b c s j r) +
  (∑r : Mode,∑s : Mode,B r k*A s j*tripleGram a b c i s r)

theorem actual_normal_triple_pair (A B : Matrix Mode Mode ℂ) (a b c i j k : Mode) :
    inner ℂ (triple a b c) (normalFiber A B (triple i j k)) =
      twoColumnPair A B a b c i j k := by
  rw [actual_normal_triple]
  simp only [twoColumn, twoColumnPair, inner_add_right, inner_sum, inner_smul_right,
    actual_ordered_triple_pair]

end LowEnergy.ActualCandidateQuarticGram
