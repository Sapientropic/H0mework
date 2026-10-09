import H0mework.Versions.R9c73a630.Chemistry.LAlanineRuntime.Facade

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.ContinuousRuntime

def bandFaceAt (i : Fin 22) : ContinuousBandFace :=
  ![.component .material, .component .certificate,
    .inherited (.component .material), .inherited (.component .certificate),
    .inherited (.inherited (.component .material)), .inherited (.inherited (.component .certificate)),
    .inherited (.inherited (.inherited (.component .material))),
    .inherited (.inherited (.inherited (.component .certificate))),
    .inherited (.inherited (.inherited (.inherited (.component .material)))),
    .inherited (.inherited (.inherited (.inherited (.component .certificate)))),
    .inherited (.inherited (.inherited (.inherited (.inherited .physical)))),
    .inherited (.inherited (.inherited (.inherited (.inherited .history)))),
    .inherited (.inherited (.inherited (.inherited (.inherited .clock)))),
    .inherited (.inherited (.inherited (.inherited (.inherited .held)))),
    .inherited (.inherited (.inherited (.inherited (.inherited .realization)))),
    .inherited (.inherited (.inherited (.inherited (.inherited .generator)))),
    .inherited (.inherited (.inherited (.inherited (.inherited .gradient)))),
    .inherited (.inherited (.inherited (.inherited (.inherited .residual)))),
    .inherited (.inherited (.inherited (.inherited (.inherited .mode)))),
    .inherited (.inherited (.inherited (.inherited (.inherited .firstReentry)))),
    .inherited (.inherited (.inherited (.inherited (.inherited .readiness)))),
    .inherited (.inherited (.inherited (.inherited (.inherited .wholeLedger))))] i

def bandFaceIndex : ContinuousBandFace → Fin 22
  | .component .material => 0
  | .component .certificate => 1
  | .inherited (.component .material) => 2
  | .inherited (.component .certificate) => 3
  | .inherited (.inherited (.component .material)) => 4
  | .inherited (.inherited (.component .certificate)) => 5
  | .inherited (.inherited (.inherited (.component .material))) => 6
  | .inherited (.inherited (.inherited (.component .certificate))) => 7
  | .inherited (.inherited (.inherited (.inherited (.component .material)))) => 8
  | .inherited (.inherited (.inherited (.inherited (.component .certificate)))) => 9
  | .inherited (.inherited (.inherited (.inherited (.inherited .physical)))) => 10
  | .inherited (.inherited (.inherited (.inherited (.inherited .history)))) => 11
  | .inherited (.inherited (.inherited (.inherited (.inherited .clock)))) => 12
  | .inherited (.inherited (.inherited (.inherited (.inherited .held)))) => 13
  | .inherited (.inherited (.inherited (.inherited (.inherited .realization)))) => 14
  | .inherited (.inherited (.inherited (.inherited (.inherited .generator)))) => 15
  | .inherited (.inherited (.inherited (.inherited (.inherited .gradient)))) => 16
  | .inherited (.inherited (.inherited (.inherited (.inherited .residual)))) => 17
  | .inherited (.inherited (.inherited (.inherited (.inherited .mode)))) => 18
  | .inherited (.inherited (.inherited (.inherited (.inherited .firstReentry)))) => 19
  | .inherited (.inherited (.inherited (.inherited (.inherited .readiness)))) => 20
  | .inherited (.inherited (.inherited (.inherited (.inherited .wholeLedger)))) => 21

theorem bandFace_index_at : ∀ i : Fin 22, bandFaceIndex (bandFaceAt i) = i := by decide +kernel

theorem bandFace_at_index (face : ContinuousBandFace) : bandFaceAt (bandFaceIndex face) = face := by
  rcases face with face | face
  · cases face <;> rfl
  · rcases face with face | face
    · cases face <;> rfl
    · rcases face with face | face
      · cases face <;> rfl
      · rcases face with face | face
        · cases face <;> rfl
        · rcases face with face | face
          · cases face <;> rfl
          · cases face <;> rfl

def bandFaceEquiv : ContinuousBandFace ≃ Fin 22 where
  toFun := bandFaceIndex
  invFun := bandFaceAt
  left_inv := bandFace_at_index
  right_inv := bandFace_index_at

end LAlanine40K2025.BasinRefinement.ContinuousRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
