import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandCertified.InitialField
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandSource.Restriction
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTubeWhole.MatrixAllFields

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandSource

open SourceGaussianModel SourceSignedEvaluator IntervalParameterMap
noncomputable section

/-- Exactly the paid old cell and the new source-initial rectangle in both time directions. -/
abbrev CertifiedCall := TrueTubeSource.Call ⊕ Direction
def certifiedCall : CertifiedCall → FullBandCall
  | .inl c => cell16Call c
  | .inr d => initialCallAt 0 d 0

theorem certifiedCall_injective : Function.Injective certifiedCall := by
  intro a b same
  cases a <;> cases b
  · congr 1
    apply Fin.ext
    have h := congrArg Fin.val same
    dsimp [certifiedCall, cell16Call] at h
    omega
  · have h := congrArg Fin.val same
    dsimp [certifiedCall, cell16Call, initialCallAt, callAt, rowAt] at h
    omega
  · have h := congrArg Fin.val same
    dsimp [certifiedCall, cell16Call, initialCallAt, callAt, rowAt] at h
    omega
  · congr 1
    apply Fin.ext
    have h := congrArg Fin.val same
    dsimp [certifiedCall, initialCallAt, callAt, rowAt] at h
    omega

set_option maxRecDepth 16384 in
theorem newInitial_box (d : Direction) : callBox (initialCallAt 0 d 0) = callBox 0 := by
  fin_cases d <;> rfl

set_option maxRecDepth 16384 in
theorem newInitial_report (d : Direction) :
    recordedCallField (initialCallAt 0 d 0) = recordedCallField 0 := by
  fin_cases d <;> rfl

theorem certified_actual_field (c : CertifiedCall) (x : Point)
    (inside : InRectangle (callBox (certifiedCall c)) x) :
    FieldHolds (recordedCallField (certifiedCall c)) x := by
  cases c with
  | inl old =>
      change FieldHolds (recordedCallField (cell16Call old)) x
      rw [cell16_recordedCallField]
      apply TrueTubeWholeMatrix.all_actual_call_fields old x
      simpa only [certifiedCall, cell16_callBox] using inside
  | inr direction =>
      change FieldHolds (recordedCallField (initialCallAt 0 direction 0)) x
      rw [newInitial_report]
      apply WholeBandCache.Call0.actual_field x
      simpa only [certifiedCall, newInitial_box] using inside

end
end LAlanine40K2025.BasinRefinement.WholeBandSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
