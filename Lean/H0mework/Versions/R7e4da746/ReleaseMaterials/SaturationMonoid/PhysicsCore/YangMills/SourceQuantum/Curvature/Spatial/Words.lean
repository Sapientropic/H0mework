import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.PhysicsCore.YangMills.SourceQuantum.Curvature.Spatial.Field
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.PhysicsCore.YangMills.SourceQuantum.CommonCarrier

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped InnerProductSpace ComplexOrder

namespace SaturationMonoid.PhysicsCore.YangMills.NativeCurvature.Spatial
noncomputable section
open FullPairing NativeSource Stage9DEF
local instance : InnerProductSpace ℂ Hilbert := inferInstance
local instance : InnerProductSpace ℂ CommonCarrier.Space := inferInstance

structure Label where
  variation : Variation.Input
  amplitude : ℝ
  polynomial : Polynomial
  test : Terminal.Test

def operator (l : Label) : Hilbert →L[ℂ] Hilbert :=
  field l.variation l.amplitude l.polynomial l.test

def word (w : List Label) : Hilbert →L[ℂ] Hilbert := (w.map operator).prod

def mother (w : List Label) : Mother := fromOperator (word w)

def action (w : List Label) : CommonCarrier.Space →L[ℂ] CommonCarrier.Space :=
  CommonCarrier.action (mother w)

theorem action_readback (w : List Label) (v : CommonCarrier.Space) :
    CommonCarrier.realization (action w v) = word w (CommonCarrier.realization v) := by
  rw [action, CommonCarrier.action_readback, mother, operator_fromOperator]

def gram (p : ProofFreeRicherAnholonomicSource.BasePoint) (w z : List Label) : ℂ :=
  State.vectorEvaluation (Stage10.Runtime.tick.answer p)
    (Compatibility.responseMatrix (pairedMother (mother w) (mother z)))

theorem gram_value (p : ProofFreeRicherAnholonomicSource.BasePoint) (w z : List Label) :
    gram p w z = inner ℂ (word w (prepared p)) (word z (prepared p)) := by
  rw [gram, source_gram, mother, mother, operator_fromOperator, operator_fromOperator]

theorem original_carrier_gram (p : ProofFreeRicherAnholonomicSource.BasePoint) (w z : List Label) :
    inner ℂ (action w (CommonCarrier.preparation p))
      (action z (CommonCarrier.preparation p)) = gram p w z :=
  CommonCarrier.source_pairing p (mother w) (mother z)

theorem gram_positive {I : Type*} (p : ProofFreeRicherAnholonomicSource.BasePoint)
    (words : I → List Label) : Matrix.PosSemidef (fun i j => gram p (words i) (words j)) := by
  simp_rw [gram_value]
  exact SaturationMonoid.Quantum.Kernel.gram_posSemidef (fun i => word (words i) (prepared p))

end
end SaturationMonoid.PhysicsCore.YangMills.NativeCurvature.Spatial
