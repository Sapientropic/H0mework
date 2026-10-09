import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Producer.SourceGeneratedPointerFeedback
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.EffectGap

set_option autoImplicit false
set_option maxRecDepth 16384

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.FullGammaCross

open Measurement Propagation.Producer
open Renewal.Direction.Blocks.EnergyFrame
open scoped Matrix MatrixOrder ComplexOrder
noncomputable section
attribute [local irreducible] Current.loadPulse Current.pulse Live.State.joint
  sourceTarget receivedState firstState

private theorem boundedEffect_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) : (boundedEffect A).PosDef := by
  have hgap := bounded_effect_gap A hA
  have hrest : (boundedEffect A - effectGap A • (1 : Matrix ι ι ℂ)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hgap)
  have hfloor : (effectGap A • (1 : Matrix ι ι ℂ)).PosDef :=
    Matrix.PosDef.smul Matrix.PosDef.one (effect_gap_positive A)
  have hsum := hfloor.add_posSemidef hrest
  convert hsum using 1
  abel

private theorem sourceEffect_posDef : sourceEffect.PosDef := by
  let A := Measurement.sourceOutputObservable Load.Source.loadTotalHamiltonian
  have hA : A.IsHermitian :=
    Measurement.sourceOutputObservable_hermitian _ Load.Source.loadTotalHamiltonian_hermitian
  have hmain : (Measurement.sourceMeasurementEffect Load.Source.loadTotalHamiltonian).PosDef :=
    boundedEffect_posDef A hA
  change (Incidence.bodyObservable (Measurement.sourceMeasurementEffect Load.Source.loadTotalHamiltonian)).PosDef
  unfold Incidence.bodyObservable
  exact (hmain.kronecker Matrix.PosDef.one).submatrix Incidence.bodyReservoir.injective

private theorem sourceComplement_posDef : (1 - sourceEffect).PosDef := by
  let A := Measurement.sourceOutputObservable Load.Source.loadTotalHamiltonian
  have hA : A.IsHermitian :=
    Measurement.sourceOutputObservable_hermitian _ Load.Source.loadTotalHamiltonian_hermitian
  have hmain : (1 - Measurement.sourceMeasurementEffect Load.Source.loadTotalHamiltonian).PosDef := by
    rw [Measurement.sourceMeasurementEffect, boundedEffect_complement]
    exact boundedEffect_posDef (-A) hA.neg
  rw [sourceEffect, bodyObservable_complement]
  unfold Incidence.bodyObservable
  exact (hmain.kronecker Matrix.PosDef.one).submatrix Incidence.bodyReservoir.injective

private theorem received_nonzero : received.joint ≠ 0 := by
  intro h
  have ht := received.normalized
  rw [h, Matrix.trace_zero] at ht
  norm_num at ht

theorem source_cross_nonzero :
    effectRoot sourceEffect * received.joint * complementRoot sourceEffect ≠ 0 := by
  have hR : IsUnit (effectRoot sourceEffect) := by
    rw [← isUnit_mul_self_iff, effectRoot_square _ sourceEffect_lawful.1]
    exact sourceEffect_posDef.isUnit
  have hS : IsUnit (complementRoot sourceEffect) := by
    rw [← isUnit_mul_self_iff, complementRoot_square _ sourceEffect_lawful.2]
    exact sourceComplement_posDef.isUnit
  intro hz
  have hleft : received.joint * complementRoot sourceEffect = 0 := by
    apply hR.mul_right_inj.mp
    rw [Matrix.mul_assoc] at hz
    simpa only [Matrix.mul_zero] using hz
  have hright : received.joint = 0 := by
    apply hS.mul_left_inj.mp
    rw [Matrix.zero_mul]
    exact hleft
  exact received_nonzero hright

theorem instrumentJoint_cross_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Matrix ι ι ℂ) (hE : E.PosSemidef) (hC : (1 - E).PosSemidef)
    (rho : Matrix ι ι ℂ) :
    (instrumentJoint E hE hC rho).toBlocks₁₂ =
      effectRoot E * rho * complementRoot E := by
  rw [instrumentJoint, Quantum.conjugation_apply]
  change ((dilationMatrix E) * prepared rho *
    star (dilationMatrix E)).toBlocks₁₂ = _
  rw [Matrix.star_eq_conjTranspose]
  simpa only [Matrix.toBlocks_fromBlocks₁₂] using congrArg Matrix.toBlocks₁₂
    (dilation_prepared_blocks E rho)

theorem sourceTarget_cross_eq :
    sourceTarget.submatrix Sum.inl Sum.inr =
      effectRoot sourceEffect * received.joint * complementRoot sourceEffect := by
  rw [sourceTarget]
  exact instrumentJoint_cross_eq sourceEffect sourceEffect_lawful.1
    sourceEffect_lawful.2 received.joint

theorem received_cross_eq :
    receivedState.joint.submatrix Sum.inl Sum.inr =
      effectRoot sourceEffect * received.joint * complementRoot sourceEffect := by
  rw [receivedState_joint, sourceTarget_cross_eq]

theorem received_cross_nonzero :
    receivedState.joint.submatrix Sum.inl Sum.inr ≠ 0 := by
  rw [received_cross_eq]
  exact source_cross_nonzero

theorem blocks12_eq_submatrix {ι κ : Type*}
    (M : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) :
    M.toBlocks₁₂ = M.submatrix Sum.inl Sum.inr := by
  ext i j
  rfl

theorem respondNext_cross_nonzero (current : Live.State)
    (hcurrent : current.joint.submatrix Sum.inl Sum.inr ≠ 0) :
    (respondNext current).joint.submatrix Sum.inl Sum.inr ≠ 0 := by
  let U := Current.loadPulse (nativeClockStep : ℝ)
  let V := freePhase (nativeClockStep : ℝ) • Current.pulse (nativeClockStep : ℝ)
  have hU : IsUnit (U : Current.FullJoint) := Unitary.isUnit_coe
  have hV : IsUnit (star (V : Current.FullJoint)) := Unitary.isUnit_coe.star
  have hproduct : (U : Current.FullJoint) *
      (current.joint.submatrix Sum.inl Sum.inr) * star (V : Current.FullJoint) ≠ 0 := by
    intro hz
    have hleft : current.joint.submatrix Sum.inl Sum.inr * star (V : Current.FullJoint) = 0 := by
      apply hU.mul_right_inj.mp
      rw [Matrix.mul_assoc] at hz
      simpa only [Matrix.mul_zero] using hz
    have hright : current.joint.submatrix Sum.inl Sum.inr = 0 := by
      apply hV.mul_left_inj.mp
      rw [Matrix.zero_mul]
      exact hleft
    exact hcurrent hright
  have htransport : (respondNext current).joint.submatrix Sum.inl Sum.inr =
      (U : Current.FullJoint) * (current.joint.submatrix Sum.inl Sum.inr) *
        star (V : Current.FullJoint) := by
    simpa only [blocks12_eq_submatrix, U, V, Unitary.coe_smul] using respondNext_cross current
  rw [htransport]
  exact hproduct

theorem first_cross_nonzero : firstState.joint.submatrix Sum.inl Sum.inr ≠ 0 := by
  rw [firstState]
  exact respondNext_cross_nonzero receivedState received_cross_nonzero

def diagonalBlocksOnly {ι : Type*} [Fintype ι]
    (joint : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  Matrix.fromBlocks joint.toBlocks₁₁ 0 0 joint.toBlocks₂₂

theorem diagonalBlocksOnly_ne_of_cross_nonzero {ι : Type*} [Fintype ι]
    (joint : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)
    (cross : joint.submatrix Sum.inl Sum.inr ≠ 0) :
    diagonalBlocksOnly joint ≠ joint := by
  intro same
  have h := congrArg (fun M : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ =>
    M.submatrix Sum.inl Sum.inr) same
  have hzero : (diagonalBlocksOnly joint).submatrix Sum.inl Sum.inr = 0 := by
    change (Matrix.fromBlocks joint.toBlocks₁₁ 0 0 joint.toBlocks₂₂).toBlocks₁₂ = 0
    simp
  have zero : joint.submatrix Sum.inl Sum.inr = 0 := by
    exact h.symm.trans hzero
  exact cross zero

theorem received_diagonal_blocks_incomplete :
    diagonalBlocksOnly receivedState.joint ≠ receivedState.joint :=
  diagonalBlocksOnly_ne_of_cross_nonzero receivedState.joint received_cross_nonzero

theorem first_diagonal_blocks_incomplete :
    diagonalBlocksOnly firstState.joint ≠ firstState.joint :=
  diagonalBlocksOnly_ne_of_cross_nonzero firstState.joint first_cross_nonzero

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.FullGammaCross
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
