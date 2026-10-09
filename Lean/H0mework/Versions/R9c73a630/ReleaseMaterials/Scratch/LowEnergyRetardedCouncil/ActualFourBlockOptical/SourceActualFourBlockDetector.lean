import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.MixedSpectatorFourBlockSource
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualFourBlockDetector
open SaturationMonoid.PhysicsCore
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge GaussCoreDifferential
open SourceQuantumGaugeSliceCoordinates SourceQuantumScalarChart
open GaussFockWeights GaussFockPair GaussCoreHilbert ActualFourBlockSource
open QuantizationCheck.Fermion
open MeasureTheory
open scoped BigOperators InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := SourceRealScalarFock.branchOrder.toDecidableEq

private theorem normal_number (A B : Matrix Mode Mode ℂ) :
    SourceFockRaising.total * LowEnergy.Fermion.normalProduct A B =
      LowEnergy.Fermion.normalProduct A B * SourceFockRaising.total := by
  exact LowEnergy.Fermion.occupationCharge_normalProduct (fun _ => 1) A B
    (by intros; simp) (by intros; simp)

/-- The actual four source departments conserve particle number before
any source-weight or detector is installed. -/
theorem actual_block_number (p : Kinematics) (b : Fin 4) :
    SourceFockRaising.total * block p b = block p b * SourceFockRaising.total := by
  fin_cases b
  · change SourceFockRaising.total * MixedSpectatorContactExchange.actualContactTree (MixedSpectatorPairedSourceFrame.worldTransfer p.x p.k) p.pLeft p.pRight =
      MixedSpectatorContactExchange.actualContactTree (MixedSpectatorPairedSourceFrame.worldTransfer p.x p.k) p.pLeft p.pRight * SourceFockRaising.total
    simp only [MixedSpectatorContactExchange.actualContactTree,
      Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, normal_number]
  · change SourceFockRaising.total * MixedSpectatorCanonical79Exchange.actualCanonicalTree p.x p.k p.pLeft p.pRight p.canonicalRegular =
      MixedSpectatorCanonical79Exchange.actualCanonicalTree p.x p.k p.pLeft p.pRight p.canonicalRegular * SourceFockRaising.total
    simp only [MixedSpectatorCanonical79Exchange.actualCanonicalTree,
      Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, normal_number]
  · change SourceFockRaising.total * MixedSpectatorDual24Exchange.actualDualTree p.x p.k p.pLeft p.pRight p.dualRegular =
      MixedSpectatorDual24Exchange.actualDualTree p.x p.k p.pLeft p.pRight p.dualRegular * SourceFockRaising.total
    simp only [MixedSpectatorDual24Exchange.actualDualTree,
      Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, normal_number]
  · change SourceFockRaising.total * MixedSpectatorScalar61Exchange.actualScalar61Tree ⟨MixedSpectatorPairedSourceFrame.worldTransfer p.x p.k,p.scalarRegular⟩ =
      MixedSpectatorScalar61Exchange.actualScalar61Tree ⟨MixedSpectatorPairedSourceFrame.worldTransfer p.x p.k,p.scalarRegular⟩ * SourceFockRaising.total
    simp only [MixedSpectatorScalar61Exchange.actualScalar61Tree,
      Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, normal_number]

def coherentFiber (p : Kinematics) : FockFiber →L[ℂ] FockFiber := ∑b : Fin 4, blockFiber p b

theorem actual_coherent_fiber_point (p : Kinematics) (f : QuantumTest)
    (z : SourceCoordinateSlice) : coherentSource p f z = coherentFiber p (f z) := by
  simp only [coherentSource, coherentFiber, LinearMap.sum_apply, sum_apply]
  rfl

theorem actual_coherent_number (p : Kinematics) :
    Commute fiberNumber (coherentFiber p) := by
  show fiberNumber * coherentFiber p = coherentFiber p * fiberNumber
  simp only [coherentFiber, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  apply ContinuousLinearMap.ext
  intro ψ
  apply fiberCoordinates.injective
  change SourceFockRaising.total (block p b (fiberCoordinates ψ)) =
    block p b (SourceFockRaising.total (fiberCoordinates ψ))
  exact LinearMap.congr_fun (actual_block_number p b) (fiberCoordinates ψ)

private theorem number_weight_commute (T : FockFiber →L[ℂ] FockFiber)
    (hT : Commute fiberNumber T) (c : ℕ → ℂ) : Commute (weight c) T := by
  classical
  have entry (output input : Occupation) (different : output.card ≠ input.card) :
      T (EuclideanSpace.single input 1) output = 0 := by
    have hn : fiberNumber (EuclideanSpace.single input 1) =
        (input.card : ℂ) • EuclideanSpace.single input 1 := by
      ext word
      rw [fiberNumber_apply]
      by_cases h : word = input
      · subst word; simp
      · simp [EuclideanSpace.single, h]
    have h := congrArg (fun S : FockFiber →L[ℂ] FockFiber =>
      S (EuclideanSpace.single input 1) output) hT.eq
    change fiberNumber (T (EuclideanSpace.single input 1)) output =
      T (fiberNumber (EuclideanSpace.single input 1)) output at h
    rw [fiberNumber_apply, hn, map_smul] at h
    simp only [PiLp.smul_apply, smul_eq_mul] at h
    have hz : ((output.card : ℂ) - (input.card : ℂ)) *
        T (EuclideanSpace.single input 1) output = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (by exact_mod_cast different))
  show weight c * T = T * weight c
  apply ContinuousLinearMap.ext
  intro ψ
  have expansion : ψ = ∑word : Occupation, ψ word • EuclideanSpace.single word 1 := by
    apply PiLp.ext
    intro word
    simp [WithLp.ofLp_sum, Finset.sum_apply, EuclideanSpace.single, Pi.single_apply]
  have single (input : Occupation) : weight c (T (EuclideanSpace.single input 1)) =
      T (weight c (EuclideanSpace.single input 1)) := by
    have hw : weight c (EuclideanSpace.single input 1) =
        c input.card • EuclideanSpace.single input 1 := by
      apply PiLp.ext
      intro word
      rw [weight_apply]
      by_cases h : word = input
      · subst word; simp
      · simp [EuclideanSpace.single, h]
    rw [hw, map_smul]
    apply PiLp.ext
    intro output
    rw [weight_apply]
    by_cases h : output.card = input.card
    · rw [h]; rfl
    · simp only [PiLp.smul_apply, smul_eq_mul, entry output input h, mul_zero]
  change weight c (T ψ) = T (weight c ψ)
  rw [expansion, map_sum, map_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro word _
  rw [map_smul, map_smul, map_smul, map_smul, single]

theorem actual_coherent_weight (p : Kinematics) (c : ℕ → ℂ) :
    Commute (weight c) (coherentFiber p) :=
  number_weight_commute _ (actual_coherent_number p) c

attribute [local irreducible] coherentFiber coherentSource blockFiber block

private theorem number_pair (f g : FockFiber) :
    inner ℂ (fiberNumber f) g = inner ℂ f (fiberNumber g) := by
  simp only [PiLp.inner_apply, fiberNumber_apply, RCLike.inner_apply, map_mul, map_natCast]
  apply Finset.sum_congr rfl
  intro word _
  ring

theorem actual_adjoint_number (p : Kinematics) :
    Commute fiberNumber (coherentFiber p).adjoint := by
  show fiberNumber * (coherentFiber p).adjoint = (coherentFiber p).adjoint * fiberNumber
  apply ContinuousLinearMap.ext
  intro ψ
  apply ext_inner_left ℂ
  intro φ
  change inner ℂ φ (fiberNumber ((coherentFiber p).adjoint ψ)) =
    inner ℂ φ ((coherentFiber p).adjoint (fiberNumber ψ))
  rw [←number_pair, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.adjoint_inner_right, ←number_pair]
  have h := congrArg (fun T : FockFiber →L[ℂ] FockFiber => T φ)
    (actual_coherent_number p).eq
  exact congrArg (fun v : FockFiber => inner ℂ v ψ) h.symm

theorem actual_detector_number (p : Kinematics) :
    Commute fiberNumber ((coherentFiber p).adjoint * coherentFiber p) :=
  (actual_adjoint_number p).mul_right (actual_coherent_number p)

/-- The ordinary adjoint of the actual full occupation operator is also its
physical source adjoint: particle-number preservation pays the density weight. -/
def adjointSource (p : Kinematics) : QuantumTest →ₗ[ℂ] QuantumTest :=
  localMultiplier (fun _ => (coherentFiber p).adjoint) (fun _ => contDiffAt_const)

theorem actual_source_adjoint (p : Kinematics) (f g : QuantumTest) :
    sourcePair f (adjointSource p g) = sourcePair (coherentSource p f) g := by
  rw [sourcePair_integral, sourcePair_integral]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  change inner ℂ (weight (fun N => GaussDensityCore.complexDensity N z) (f z))
    ((coherentFiber p).adjoint (g z)) =
      inner ℂ (weight (fun N => GaussDensityCore.complexDensity N z)
        (coherentSource p f z)) (g z)
  rw [ContinuousLinearMap.adjoint_inner_right, actual_coherent_fiber_point]
  have h := congrArg (fun T : FockFiber →L[ℂ] FockFiber => T (f z))
    (actual_coherent_weight p (fun N => GaussDensityCore.complexDensity N z)).eq
  exact congrArg (fun v : FockFiber => inner ℂ v (g z)) h.symm

def detector (p : Kinematics) : QuantumTest →ₗ[ℂ] QuantumTest :=
  adjointSource p * coherentSource p

theorem actual_detector_pair (p : Kinematics) (f g : QuantumTest) :
    sourcePair f (detector p g) = sourcePair (coherentSource p f) (coherentSource p g) :=
  actual_source_adjoint p f (coherentSource p g)

theorem actual_detector_hermitian (p : Kinematics) (f g : QuantumTest) :
    sourcePair f (detector p g) = sourcePair (detector p f) g := by
  rw [actual_detector_pair]
  have h := congrArg (starRingEnd ℂ) (actual_detector_pair p g f)
  simpa only [sourcePair, inner_conj_symm] using h.symm

theorem actual_detector_intensity (p : Kinematics) (f : QuantumTest) :
    sourcePair f (detector p f) = (‖embed (coherentSource p f)‖^2 : ℂ) := by
  rw [actual_detector_pair, sourcePair, inner_self_eq_norm_sq_to_K]
  norm_cast

end LowEnergy.ActualFourBlockDetector
