import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Information.Born.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Information.Born.MarginalRaw

/-! The joint Born output retains the original pointer weights through the same observable frame. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Born

noncomputable section

variable (observable : Current.FullJoint) (hermitian : observable.IsHermitian) (current : Live.State)

theorem pointer_zero_mass : ((distribution observable hermitian current).map pointer) 0 =
    ∑ index : Current.FullIndex, distribution observable hermitian current (Sum.inl index) := by
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_sum_type]
  simp [pointer]

theorem pointer_one_mass : ((distribution observable hermitian current).map pointer) 1 =
    ∑ index : Current.FullIndex, distribution observable hermitian current (Sum.inr index) := by
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_sum_type]
  simp [pointer]

theorem pointer_zero_read : (((distribution observable hermitian current).map pointer) 0).toReal =
    zeroRead current.joint :=
  (diagonal_pointer_zero (jointRead observable hermitian current)
    (jointRead_positive observable hermitian current) (jointRead_normalized observable hermitian current)).trans
      (blockUnitary_preserves_zeroRead (star hermitian.eigenvectorUnitary)
        (star hermitian.eigenvectorUnitary) current.joint)

theorem pointer_one_read : (((distribution observable hermitian current).map pointer) 1).toReal =
    oneRead current.joint :=
  (diagonal_pointer_one (jointRead observable hermitian current)
    (jointRead_positive observable hermitian current) (jointRead_normalized observable hermitian current)).trans
      (blockUnitary_preserves_oneRead (star hermitian.eigenvectorUnitary)
        (star hermitian.eigenvectorUnitary) current.joint)

theorem actual_pointer_zero : (((distribution observable hermitian firstState).map pointer) 0).toReal =
    zeroRead receivedState.joint :=
  (pointer_zero_read observable hermitian firstState).trans (respondNext_zero receivedState)

theorem actual_pointer_one : (((distribution observable hermitian firstState).map pointer) 1).toReal =
    oneRead receivedState.joint :=
  (pointer_one_read observable hermitian firstState).trans (respondNext_one receivedState)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Born
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
