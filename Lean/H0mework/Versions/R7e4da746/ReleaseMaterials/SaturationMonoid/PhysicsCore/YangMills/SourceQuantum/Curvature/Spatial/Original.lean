import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.PhysicsCore.YangMills.SourceQuantum.Curvature.Spatial.Words

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped InnerProductSpace BoundedContinuousFunction

namespace SaturationMonoid.PhysicsCore.YangMills.NativeCurvature.Spatial
noncomputable section
open FullPairing Spacetime Stage9C.Material.SpinPair

theorem original_point (P : Polynomial) (p : ProofFreeRicherAnholonomicSource.BasePoint) :
    NativeSource.GaugeWords.seed (atPoint p P) = NativeSource.GaugeWords.seed (atPoint 0 P) := by
  have same : (Variation.representation.comp (quantumEvaluate actual)).comp (atPoint p) =
      (Variation.representation.comp (quantumEvaluate actual)).comp (atPoint 0) := by
    apply FreeAlgebra.hom_ext
    funext r
    simp only [Function.comp_apply, AlgHom.comp_apply, atPoint, FreeAlgebra.lift_ι_apply]
    exact original_generator p r
  exact congrArg (fun F => F P) same

theorem field_original (η : Variation.Input) (P : Polynomial) (f : Terminal.Test) :
    field η 0 P f = NativeSource.GaugeWords.field (atPoint 0 P) f := by
  apply ContinuousLinearMap.ext
  intro v
  rw [field_integral, NativeSource.GaugeWords.field_integral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun p => by
    dsimp only
    rw [Variation.value_original, original_point])

theorem field_unit (η : Variation.Input) (t : ℝ) (f : Terminal.Test) (v : Hilbert) :
    field η t 1 f v = (∫ p, f p) • v := by
  rw [field, SpatialFields.field_integral]
  have one (p : Terminal.Spacetime) : SpatialFields.kernel NativeSource.time (seed η t 1) p = 1 := by
    unfold SpatialFields.kernel
    rw [map_one]
    change Quantum.Generator.Commutator.conjugation NativeSource.time 1 (-p 0) = 1
    exact map_one _
  simp only [one, one_apply_eq_self]
  exact integral_smul_const _ _

def domainWord :
    List Label → Quantum.Generator.domain NativeSource.time → Quantum.Generator.domain NativeSource.time
  | [], v => v
  | l :: w, v => domainAction l.variation l.amplitude l.polynomial l.test (domainWord w v)

theorem domainWord_value (w : List Label) (v : Quantum.Generator.domain NativeSource.time) :
    (domainWord w v).val = word w v.val := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [domainWord, domainAction_value, ih]
    rfl

end
end SaturationMonoid.PhysicsCore.YangMills.NativeCurvature.Spatial
