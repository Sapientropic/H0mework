import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.DivisorJointSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.FiniteLogCountingSource
import H0mework.Arithmetic.BurnolCarrier.ConstantGapFace
import H0mework.Versions.R7e4da746.Arithmetic.MellinTateSource.Isometry
import H0mework.Versions.R7e4da746.Arithmetic.MellinTateSource.L2Raw

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalGamma.Source.JointLogConductor
open Complex Filter FourierTransform MeasureTheory Set
open scoped InnerProductSpace Topology
open OriginalGamma.Source.FiniteLogCounting OriginalGamma.Source.DivisorJoint
noncomputable section

private def tateIsometry : BurnolL2 →ₗᵢ[ℂ] BurnolL2 where
  toLinearMap := burnolTateReciprocalL2.toLinearMap
  norm_map' := burnolTateReciprocalValue_norm

theorem original_tate_pairing (left right : BurnolL2) :
    inner ℂ (burnolTateReciprocalL2 left) right =
      inner ℂ left (burnolTateReciprocalL2 right) := by
  have isometric := tateIsometry.inner_map_map left (burnolTateReciprocalL2 right)
  change inner ℂ (burnolTateReciprocalL2 left)
      (burnolTateReciprocalL2 (burnolTateReciprocalL2 right)) = _ at isometric
  rw [burnolTateReciprocalL2_involutive] at isometric
  exact isometric

theorem original_tate_log_raw (raw : ℝ → ℂ) (x : ℝ) :
    (Real.log |x| : ℂ) * burnolTateReciprocalRaw raw x =
      -burnolTateReciprocalRaw (fun y => (Real.log |y| : ℂ) * raw y) x := by
  simp only [burnolTateReciprocalRaw, abs_inv, Real.log_inv, Complex.ofReal_neg]
  ring

theorem original_tate_log_domain (value logValue : BurnolL2)
    (source : LogPair value logValue) :
    LogPair (burnolTateReciprocalL2 value) (-burnolTateReciprocalL2 logValue) := by
  have pulled := burnolTateReciprocalRaw_ae_congr (Lp.memLp logValue)
    ((Lp.memLp logValue).ae_eq source) source
  filter_upwards [Lp.coeFn_neg (burnolTateReciprocalL2 logValue),
    burnolTateReciprocalL2_coeFn logValue, burnolTateReciprocalL2_coeFn value, pulled]
    with x negative logarithm actual transported
  rw [negative]
  change -(burnolTateReciprocalL2 logValue : ℝ → ℂ) x = _
  rw [logarithm, transported, actual, original_tate_log_raw]

def jointAdjointTest (test : SchwartzMap ℝ ℂ) : BurnolL2 :=
  burnolTateReciprocalL2 ((𝓕⁻ test).toLp 2 volume)

def jointAdjointLog (test : SchwartzMap ℝ ℂ) : BurnolL2 :=
  -burnolTateReciprocalL2 (logSchwartzL2 (𝓕⁻ test))

def wholeConductorTest (test : SchwartzMap ℝ ℂ) : BurnolL2 :=
  logSchwartzL2 test + fourierL2 (logSchwartzL2 (𝓕⁻ test))

theorem original_joint_adjoint_log_domain (test : SchwartzMap ℝ ℂ) :
    LogPair (jointAdjointTest test) (jointAdjointLog test) :=
  original_tate_log_domain _ _ (original_log_schwartz_domain (𝓕⁻ test))

theorem original_joint_adjoint_pairing (test : SchwartzMap ℝ ℂ) (value : BurnolL2) :
    inner ℂ (jointAdjointTest test) value = inner ℂ (test.toLp 2 volume) (joint value) := by
  unfold jointAdjointTest
  rw [original_tate_pairing, joint_apply]
  change inner ℂ ((𝓕⁻ test).toLp 2 volume) (burnolTateReciprocalL2 value) =
    inner ℂ (test.toLp 2 volume) (𝓕 (burnolTateReciprocalL2 value))
  have fourier := Lp.inner_fourier_eq ((𝓕⁻ test).toLp 2 volume) (burnolTateReciprocalL2 value)
  simpa only [← SchwartzMap.toLp_fourierInv_eq, fourier_fourierInv_eq] using fourier.symm

def weakJointLogRead (test : SchwartzMap ℝ ℂ) (value : BurnolL2) : ℂ :=
  inner ℂ (logSchwartzL2 test) (joint value) - inner ℂ (jointAdjointLog test) value

/-- Both sides of the original J action generate the whole conductor cotest; no log domain of the acted value is inserted. -/
theorem original_whole_joint_log_conductor (test : SchwartzMap ℝ ℂ) (value : BurnolL2) :
    weakJointLogRead test value = inner ℂ (wholeConductorTest test) (joint value) := by
  have fourier := Lp.inner_fourier_eq (logSchwartzL2 (𝓕⁻ test)) (burnolTateReciprocalL2 value)
  unfold weakJointLogRead jointAdjointLog wholeConductorTest
  rw [inner_neg_left, sub_neg_eq_add, inner_add_left, original_tate_pairing]
  change _ = _ + inner ℂ (fourierL2 (logSchwartzL2 (𝓕⁻ test)))
    (fourierL2 (burnolTateReciprocalL2 value))
  exact congrArg (fun z : ℂ => inner ℂ (logSchwartzL2 test) (joint value) + z) fourier.symm

end
end OriginalGamma.Source.JointLogConductor
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
