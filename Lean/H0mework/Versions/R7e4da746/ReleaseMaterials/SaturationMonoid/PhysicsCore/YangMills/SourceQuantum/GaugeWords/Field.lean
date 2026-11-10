import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.PhysicsCore.YangMills.SourceQuantum.Curvature
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.PhysicsCore.YangMills.Continuum.Spacetime.Strong.Cyclic.Carrier

/-! The original U curvature evaluator and physical time generate actual spacetime Schwartz-smeared source fields. -/

set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped InnerProductSpace LinearPMap

namespace SaturationMonoid.PhysicsCore.YangMills.NativeSource.GaugeWords
noncomputable section
open Stage9C.Material.SpinPair Stage9DEF FullPairing Spacetime.StrongFields

abbrev Polynomial := Flat.Quantum.History.Polynomial
abbrev Label := Cyclic.Label Polynomial

def seed (P : Polynomial) : Hilbert →L[ℂ] Hilbert :=
  FullPairing.operator (NativeCurvature.quantumEvaluate actual P)

def field (P : Polynomial) : Terminal.Test →L[ℂ] (Hilbert →L[ℂ] Hilbert) :=
  Spacetime.StrongFields.field NativeSource.time NativeSource.time_continuous (seed P)

theorem field_integral (P : Polynomial) (f : Terminal.Test) (v : Hilbert) :
    field P f v = ∫ p, f p • Spacetime.StrongFields.kernel NativeSource.time (seed P) p v :=
  Spacetime.StrongFields.field_integral NativeSource.time NativeSource.time_continuous (seed P) f v


theorem cubic_seed (p : ProofFreeRicherAnholonomicSource.BasePoint) :
    seed (NativeCurvature.curvatureCubic p) normalizedFeature = NativeReadout.excitation p := by
  rw [seed, NativeCurvature.quantumEvaluate_cubic]
  exact NativeCurvature.dualAction_composite_feature p

def phase (t : ℝ) : ℂ := Quantum.Generator.energyPhase (-frequency) (-t)

theorem source_orbit (t : ℝ) : NativeSource.time (Multiplicative.ofAdd t) normalizedFeature =
    phase t • normalizedFeature :=
  sub_eq_zero.mp (norm_eq_zero.mp (normalizedFeature_phase_error t))

end
end SaturationMonoid.PhysicsCore.YangMills.NativeSource.GaugeWords
