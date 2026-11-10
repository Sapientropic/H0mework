import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.PhysicsCore.YangMills.SourceQuantum.Curvature.Spatial.Seed
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.PhysicsCore.YangMills.Continuum.Spacetime.Strong.Spatial.Time

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped InnerProductSpace BoundedContinuousFunction

namespace SaturationMonoid.PhysicsCore.YangMills.NativeCurvature.Spatial
noncomputable section
open FullPairing Spacetime NativeSource

def field (η : Variation.Input) (t : ℝ) (P : Polynomial) :
    Terminal.Test →L[ℂ] (Hilbert →L[ℂ] Hilbert) :=
  SpatialFields.field NativeSource.time time_continuous (seed η t P)

theorem field_integral (η : Variation.Input) (t : ℝ) (P : Polynomial)
    (f : Terminal.Test) (v : Hilbert) :
    field η t P f v = ∫ p, f p • StrongFields.kernel NativeSource.time
      (Variation.value η t (atPoint (SpatialFields.spatialPoint p) P)) p v := by
  rw [field, SpatialFields.field_integral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun p => by
    simp only [SpatialFields.kernel, seed_readback])

theorem field_time (η : Variation.Input) (t s : ℝ) (P : Polynomial)
    (f : Terminal.Test) (v : Hilbert) :
    NativeSource.time (Multiplicative.ofAdd s) (field η t P f v) =
      field η t P (Terminal.translateTest (Terminal.timeLine s) f)
        (NativeSource.time (Multiplicative.ofAdd s) v) :=
  SpatialFields.field_time NativeSource.time time_continuous (seed η t P) s f v

theorem field_derivative (η : Variation.Input) (t : ℝ) (P : Polynomial) (f : Terminal.Test) :
    HasDerivAt (Quantum.Generator.Commutator.conjugation NativeSource.time (field η t P f))
      (field η t P (Terminal.testDerivative 0 f)) 0 :=
  SpatialFields.field_derivative NativeSource.time time_continuous (seed η t P) f

def domainAction (η : Variation.Input) (t : ℝ) (P : Polynomial) (f : Terminal.Test)
    (v : Quantum.Generator.domain NativeSource.time) : Quantum.Generator.domain NativeSource.time :=
  Quantum.Generator.Commutator.domainAction NativeSource.time (field η t P f)
    (field η t P (Terminal.testDerivative 0 f)) (field_derivative η t P f) v

theorem domainAction_value (η : Variation.Input) (t : ℝ) (P : Polynomial)
    (f : Terminal.Test) (v : Quantum.Generator.domain NativeSource.time) :
    (domainAction η t P f v).val = field η t P f v.val := rfl



end
end SaturationMonoid.PhysicsCore.YangMills.NativeCurvature.Spatial
