import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.InducedQuantum.Noise
import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.LightCausal.Development
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! The actual theta causal channel acts on the entire centered CAR matrix.
Its two-point output is then returned through the same source state. -/
set_option autoImplicit false
open scoped Matrix Matrix.Norms.L2Operator
namespace SaturationMonoid.PhysicsCore.LowEnergy.InducedQuantum
open QuantizationCheck.Fermion Fermion FullQuantum.StateGreen LightCausal
open MeasureTheory Set Filter Topology
noncomputable section
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

abbrev WordMatrix (ι : Type*) := Matrix (Finset ι) (Finset ι) ℂ

def inducedMatrix (momentum : Fin 3 → ℝ) (source : ℝ → WordMatrix ι) (time : ℝ) : WordMatrix ι :=
  metricDevelopment momentum source time

def inducedVelocity (momentum : Fin 3 → ℝ) (source : ℝ → WordMatrix ι) (time : ℝ) : WordMatrix ι :=
  metricVelocity momentum source time

def inducedWord (momentum : Fin 3 → ℝ) (source : ℝ → WordMatrix ι) (time : ℝ) : Module.End ℂ (Fock ι) :=
  Matrix.toLin' (inducedMatrix momentum source time)

def inducedTwoPoint (w : ι → ℂ) (momentum : Fin 3 → ℝ) (source : ℝ → WordMatrix ι) (t s : ℝ) : ℂ :=
  read w (dagger (inducedWord momentum source t)*inducedWord momentum source s)

theorem induced_gram (w : ι → ℂ) (momentum : Fin 3 → ℝ) (source : ℝ → WordMatrix ι) (t s : ℝ) :
    inducedTwoPoint w momentum source t s=
      pairing (inducedWord momentum source t (oneParticle w)) (inducedWord momentum source s (oneParticle w)) :=
  dagger_pair_left _ _ _

theorem induced_positive (w : ι → ℂ) (momentum : Fin 3 → ℝ) (source : ℝ → WordMatrix ι) (t : ℝ) :
    0 ≤ (inducedTwoPoint w momentum source t t).re := by
  rw [induced_gram]
  exact pairing_self_positive _

theorem induced_initial (momentum : Fin 3 → ℝ) (source : ℝ → WordMatrix ι) :
    inducedMatrix momentum source 0=0 ∧ inducedVelocity momentum source 0=0 :=
  metricDevelopment_initial _ _

theorem induced_derivative (momentum : Fin 3 → ℝ) (source : ℝ → WordMatrix ι)
    (continuousSource : Continuous source) (time : ℝ) :
    HasDerivAt (inducedMatrix momentum source) (inducedVelocity momentum source time) time :=
  metricDevelopment_derivative _ _ continuousSource _

theorem induced_forced_equation (momentum : Fin 3 → ℝ) (source : ℝ → WordMatrix ι)
    (continuousSource : Continuous source) (time : ℝ) :
    HasDerivAt (inducedVelocity momentum source)
      (((thetaRate momentum : ℂ)^2) • inducedMatrix momentum source time-
        (2*metricResidue momentum*(thetaRate momentum : ℂ)) • source time) time :=
  metricVelocity_derivative _ _ continuousSource _

def waveRead (w : ι → ℂ) : WordMatrix ι →L[ℂ] Fock ι :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M*ᵥoneParticle w
      map_add' := fun _ _ => Matrix.add_mulVec _ _ _
      map_smul' := fun _ _ => Matrix.smul_mulVec _ _ _ }

theorem induced_wave_derivative (w : ι → ℂ) (momentum : Fin 3 → ℝ) (source : ℝ → WordMatrix ι)
    (continuousSource : Continuous source) (time : ℝ) :
    HasDerivAt (fun t => inducedWord momentum source t (oneParticle w))
      (inducedVelocity momentum source time*ᵥoneParticle w) time := by
  exact ((waveRead w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt time
    (induced_derivative _ _ continuousSource _)

theorem induced_wave_acceleration (w : ι → ℂ) (momentum : Fin 3 → ℝ) (source : ℝ → WordMatrix ι)
    (continuousSource : Continuous source) :
    HasDerivAt (fun t => inducedVelocity momentum source t*ᵥoneParticle w)
      (-(2*metricResidue momentum*(thetaRate momentum : ℂ)) • (source 0*ᵥoneParticle w)) 0 := by
  have generated := ((waveRead w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (induced_forced_equation momentum source continuousSource 0)
  change HasDerivAt (fun t => inducedVelocity momentum source t*ᵥoneParticle w)
    ((((thetaRate momentum : ℂ)^2) • inducedMatrix momentum source 0-
      (2*metricResidue momentum*(thetaRate momentum : ℂ)) • source 0)*ᵥoneParticle w) 0 at generated
  simpa only [(induced_initial momentum source).1,smul_zero,zero_sub,
    Matrix.neg_mulVec,Matrix.smul_mulVec,neg_smul] using generated


attribute [local instance] Fermion.fullIndexOrder
open ProofFreeRicherAnholonomicSource YangMills.FullPairing

theorem induced_source (point : BasePoint) (momentum : Fin 3 → ℝ) (source : ℝ → WordMatrix Quantum.Index) (t s : ℝ) :
    Stage9DEF.State.vectorEvaluation (Stage10.Runtime.tick.answer point)
      (Stage9DEF.Compatibility.responseMatrix (pairedMother 1 (sourceWordMother
        (dagger (inducedWord momentum source t)*inducedWord momentum source s))))=
      inducedTwoPoint (preparedVector point) momentum source t s := source_word_readback _ _

end
end SaturationMonoid.PhysicsCore.LowEnergy.InducedQuantum
