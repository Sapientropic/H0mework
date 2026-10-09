import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualNullNativeTable

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNullNative
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumOriginalGreenFeedback
open ActualEMDressedSchur
open scoped Matrix BigOperators
attribute [local irreducible] originalChange

/-- The original row map is a bilinear transpose at the opposite Fourier covector. -/
theorem original_null_cokernel (p : Fin 4→ℂ) (f : Fin 289→ℂ) (n : Fin 9) :
    sourceCokernel p f n=∑row : Fin 289,originalNullColumn (-p) n row*f row := rfl

/-- The primitive column and the previously generated nine-dimensional lift are the same source column. -/
theorem original_null_lift_single (p : Fin 4→ℂ) (n : Fin 9) :
    sourceNullLift p (Pi.single n 1)=originalNullColumn p n := by
  change originalChange p*ᵥ
    ((fun i : Fin 289=>fun j : Fin 9=>if nullColumnIndex j=i then (1:ℂ) else 0)*ᵥ(Pi.single n 1))=_
  rw [Matrix.mulVec_single_one]
  have column : (fun i : Fin 289=>if nullColumnIndex n=i then (1:ℂ) else 0)=Pi.single (nullColumnIndex n) 1 := by
    funext i
    simp only [Pi.single_apply,eq_comm]
  change originalChange p*ᵥ(fun i : Fin 289=>if nullColumnIndex n=i then (1:ℂ) else 0)=_
  rw [column,Matrix.mulVec_single_one]
  rfl

end LowEnergy.GaussComposite.ActualDressedNullNative
