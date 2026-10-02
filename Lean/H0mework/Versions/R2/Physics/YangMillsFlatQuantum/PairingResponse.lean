import H0mework.Versions.R2.Physics.YangMillsFlatQuantum.PairingCoordinates
import H0mework.Versions.R2.Physics.YangMillsFlatQuantum.PairingDual
import H0mework.Quantum.Kernel.Gram
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! The original quantum response reads the complete mother Gram pairing.
The independent dual is compensated once, after the whole adjoint product;
no intermediate occupied projection is inserted. -/

set_option autoImplicit false
open scoped InnerProductSpace ComplexOrder

namespace SaturationMonoid.PhysicsCore.YangMills.FullPairing

open DiracExteriorMatterAction ProofFreeRicherAnholonomicSource
open Stage9C.Material.SpinPair Stage9DEF

noncomputable section

abbrev Mother := Module.End ℂ DiracExteriorMatterCarrier

def operator (action : Mother) : Hilbert →L[ℂ] Hilbert :=
  (naturalCoordinates.toLinearMap.comp
    (action.comp naturalCoordinates.symm.toLinearMap)).toContinuousLinearMap

def fromOperator (action : Hilbert →L[ℂ] Hilbert) : Mother :=
  naturalCoordinates.symm.toLinearMap.comp (action.toLinearMap.comp naturalCoordinates.toLinearMap)

theorem operator_coordinates (action : Mother) (matter : DiracExteriorMatterCarrier) :
    operator action (naturalCoordinates matter) = naturalCoordinates (action matter) := by
  simp [operator]

theorem coordinates_fromOperator (action : Hilbert →L[ℂ] Hilbert)
    (matter : DiracExteriorMatterCarrier) :
    naturalCoordinates (fromOperator action matter) = action (naturalCoordinates matter) := by
  simp [fromOperator]

def pairedMother (first second : Mother) : Mother :=
  flipMatter.comp (fromOperator ((operator first).adjoint.comp (operator second)))

theorem dual_gram (point : BasePoint) (first second : Mother) :
    actual.conjugateMatter point (pairedMother first second (actual.matter point)) =
      4 * (spinScale : ℂ) * inner ℂ
        (operator first (prepared point)) (operator second (prepared point)) := by
  change actual.conjugateMatter point
    (flipMatter (fromOperator _ (actual.matter point))) = _
  rw [dual_flip, ← inner_embed, coordinates_fromOperator, actual_eq_twice_prepared,
    map_smul, inner_smul_right]
  change 2 * (spinScale : ℂ) * (2 * inner ℂ (prepared point)
    ((operator first).adjoint (operator second (prepared point)))) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  ring

theorem source_gram (point : BasePoint) (first second : Mother) :
    State.vectorEvaluation (Stage10.Runtime.tick.answer point)
        (Compatibility.responseMatrix (pairedMother first second)) =
      inner ℂ (operator first (prepared point)) (operator second (prepared point)) := by
  have generated := Stage10.Recovery.stageOneThroughTenClosure.final.stageNine.quantumClosure.sourceResponse
    point (pairedMother first second)
  rw [dual_gram, Runtime.firstQuantumTick_answer, Runtime.fieldAt_eq_vector] at generated
  rw [Stage10.Runtime.tick_vector]
  exact mul_left_cancel₀ (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0)
    (Complex.ofReal_ne_zero.mpr spinScale_pos.ne')) generated.symm

theorem source_positive (point : BasePoint) (action : Mother) :
    0 ≤ (State.vectorEvaluation (Stage10.Runtime.tick.answer point)
      (Compatibility.responseMatrix (pairedMother action action))).re := by
  rw [source_gram]
  exact inner_self_nonneg (𝕜 := ℂ)

theorem source_gram_positive {I : Type*} (point : BasePoint) (actions : I → Mother) :
    Matrix.PosSemidef (fun first second => State.vectorEvaluation (Stage10.Runtime.tick.answer point)
      (Compatibility.responseMatrix (pairedMother (actions first) (actions second)))) := by
  simp_rw [source_gram]
  exact SaturationMonoid.Quantum.Kernel.gram_posSemidef (fun i => operator (actions i) (prepared point))

end
end SaturationMonoid.PhysicsCore.YangMills.FullPairing
