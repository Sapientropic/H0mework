import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Producer.SourceGeneratedPointerFeedback
import H0mework.Chemistry.LAlanineEntropy.SpectralEntropy

/-! One independently fixed observable frame reads the complete joint of the original feedback action. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Born

open Propagation.Producer
open scoped Matrix ComplexOrder ENNReal

noncomputable section

def frame (observable : Current.FullJoint) (hermitian : observable.IsHermitian) :
    Matrix.unitaryGroup PointerIndex ℂ :=
  blockUnitary (star hermitian.eigenvectorUnitary) (star hermitian.eigenvectorUnitary)

def jointRead (observable : Current.FullJoint) (hermitian : observable.IsHermitian)
    (current : Live.State) : PointerJoint :=
  Quantum.conjugation (frame observable hermitian) current.joint

theorem jointRead_positive (observable : Current.FullJoint) (hermitian : observable.IsHermitian)
    (current : Live.State) : (jointRead observable hermitian current).PosSemidef :=
  Quantum.conjugation_posSemidef _ _ current.positive

theorem jointRead_normalized (observable : Current.FullJoint) (hermitian : observable.IsHermitian)
    (current : Live.State) : (jointRead observable hermitian current).trace = 1 :=
  (Quantum.conjugation_trace _ _).trans current.normalized

def distribution (observable : Current.FullJoint) (hermitian : observable.IsHermitian)
    (current : Live.State) : PMF PointerIndex :=
  Quantum.diagonalPMF (jointRead observable hermitian current)
    (jointRead_positive observable hermitian current) (jointRead_normalized observable hermitian current)

def pointer : PointerIndex → Fin 2 := Sum.elim (fun _ => 0) (fun _ => 1)

def outcome (observable : Current.FullJoint) (hermitian : observable.IsHermitian) : PointerIndex → ℝ :=
  Sum.elim hermitian.eigenvalues hermitian.eigenvalues

theorem distribution_toReal (observable : Current.FullJoint) (hermitian : observable.IsHermitian)
    (current : Live.State) (index : PointerIndex) :
    (distribution observable hermitian current index).toReal =
      (jointRead observable hermitian current index index).re :=
  Quantum.diagonalPMF_toReal _ _ _ index

theorem actual_response_read (observable : Current.FullJoint) (hermitian : observable.IsHermitian) :
    jointRead observable hermitian firstState = Quantum.conjugation (frame observable hermitian)
      (Quantum.conjugation (feedbackPulse (nativeClockStep : ℝ)) receivedState.joint) :=
  congrArg (Quantum.conjugation (frame observable hermitian)) (respondNext_joint receivedState)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Born
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
