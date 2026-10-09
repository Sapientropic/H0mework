import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedSignalCausal

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedSignal
open SaturationMonoid.PhysicsCore StageNineHolonomicField ProofFreeRicherAnholonomicSource
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift
open PreparationVacuumCurrentSignalOperator PreparationVacuumCurrentSignalRealization
open SourcePropagationMotherEulerKernel SourcePropagationMotherResidualDirections
open SourcePropagationNativeActionHessian
open ActualDressedFullCoulomb ActualDressedNoether
open Filter Set MeasureTheory
open scoped Matrix BigOperators Topology Interval
attribute [local irreducible] dressedSignalQuadrature dressedSignalNonlinear nativeHessian

private theorem complex_phase_linear {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [NormedAddCommGroup G] [NormedSpace ℂ G]
    [NormedSpace ℝ G] [IsScalarTower ℝ ℂ G] (A : E→L[ℝ]G)
    (phase : ∀x,A (Complex.I • x)=Complex.I • A x) (c : ℂ) (x : E) : A (c • x)=c • A x := by
  have real_smul (r : ℝ) (y : E) : A ((r:ℂ) • y)=(r:ℂ) • A y := by
    change A (algebraMap ℝ ℂ r • y)=algebraMap ℝ ℂ r • A y
    simp only [IsScalarTower.algebraMap_smul,map_smul]
  rw [←Complex.re_add_im c]
  simp only [add_smul,map_add,mul_smul,real_smul,phase]

private def complexPhaseOperator {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [NormedAddCommGroup G] [NormedSpace ℂ G]
    [NormedSpace ℝ G] [IsScalarTower ℝ ℂ G] (A : E→L[ℝ]G)
    (phase : ∀x,A (Complex.I • x)=Complex.I • A x) : E→L[ℂ]G where
  toFun := A
  map_add' := A.map_add
  map_smul' := complex_phase_linear A phase
  cont := A.continuous

def dressedSignalComplexOperator (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (t : ℝ) : SignalAmplitude→L[ℂ] (Fin 289→ℂ) :=
  complexPhaseOperator (dressedSignalQuadrature event transfer p t)
    (dressed_signal_quadrature_phase event transfer p t)

theorem dressed_signal_complex_original (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (t : ℝ) (a : SignalAmplitude) :
    dressedSignalComplexOperator event transfer p t a=dressedSignalQuadrature event transfer p t a := rfl

def dressedSignalMatrix (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (t : ℝ) : Matrix (Fin 289) (Fin 289) ℂ :=
  fun i j=>dressedSignalComplexOperator event transfer p t (Pi.single j 1) i

private theorem complex_operator_matrix {m n : ℕ} (A : (Fin n→ℂ)→L[ℂ](Fin m→ℂ)) (a : Fin n→ℂ) :
    A a=(fun i j=>A (Pi.single j 1) i)*ᵥa := by
  classical
  have decomposition : a=∑j : Fin n,a j • Pi.single j (1:ℂ) := by
    ext i
    simp only [Finset.sum_apply,Pi.smul_apply,Pi.single_apply,smul_eq_mul,
      mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  have generated:=congrArg A decomposition
  funext i
  simpa only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
    Matrix.mulVec,dotProduct,mul_comm] using congrFun generated i

/-- This tensor contains every original Noether row and every actual field direction. -/
theorem dressed_signal_matrix_actual (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (t : ℝ) (a : SignalAmplitude) :
    dressedSignalQuadrature event transfer p t a=dressedSignalMatrix event transfer p t*ᵥa :=
  complex_operator_matrix (dressedSignalComplexOperator event transfer p t) a

/-- The actual nonlinear full mother residual and the actual preparation use one amplitude. -/
def dressedSignalRawEuler (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (a : SignalAmplitude) (r t : ℝ) (i : Fin 289) : ℂ :=
  Complex.ofReal (actualMotherEulerRead (fun point=>r • sourceRealSignal p a point)
    (nativeTimePoint t) (Pi.single i 1))+
  Complex.I*Complex.ofReal (actualMotherEulerRead
    (fun point=>r • sourceRealSignal p (sourceQuadrature a) point) (nativeTimePoint t) (Pi.single i 1))-
    dressedSignalNonlinear event transfer p a r t i

private theorem raw_fourier_euler_generated (p : Fin 4→ℂ) (a : SignalAmplitude)
    (t : ℝ) (i : Fin 289) :
    HasDerivAt (fun r : ℝ=>Complex.ofReal (actualMotherEulerRead
      (fun point=>r • sourceRealSignal p a point) (nativeTimePoint t) (Pi.single i 1)))
      (Complex.ofReal ((nativeFourierHessian nativeHessian p*ᵥsourceSignalAmplitude p a (nativeTimePoint t)) i).re) 0 := by
  have original:=sourceRealSignal_originalEuler p a (nativeTimePoint t) i
  have raw:=original.congr_of_eventuallyEq
    (nativeHolonomicEuler_raw_near (sourceRealSignal p a) (nativeTimePoint t) (sourceRealSignal_smooth p a) i).symm
  exact Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 raw

/-- The complete tensor is the derivative of the original coupled residual, not a stock beta coefficient. -/
theorem dressed_signal_raw_euler_generated (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (a : SignalAmplitude) (t : ℝ) (future : 0 ≤ t)
    (inside : t<dressedSignalDuration event transfer p a) (i : Fin 289) :
    HasDerivAt (fun r=>dressedSignalRawEuler event transfer p a r t i)
      ((nativeFourierHessian nativeHessian p*ᵥsourceSignalAmplitude p a (nativeTimePoint t)) i-
        (dressedSignalMatrix event transfer p t*ᵥa) i) 0 := by
  have left:=raw_fourier_euler_generated p a t i
  have right:=raw_fourier_euler_generated p (sourceQuadrature a) t i
  have quantum:=dressed_signal_nonlinear_generated event transfer p a t future inside i
  have generated:=(left.add (right.const_mul Complex.I)).sub quantum
  apply generated.congr_deriv
  rw [←dressed_signal_matrix_actual]
  have fourier:=sourceEuler_quadrature p a (nativeTimePoint t) i
  rw [sourceRealSignal_secondJet,sourceRealEuler_Fourier,
    sourceRealSignal_secondJet,sourceRealEuler_Fourier] at fourier
  exact congrArg (fun z : ℂ=>z-dressedSignalQuadrature event transfer p t a i) fourier

end LowEnergy.GaussComposite.ActualDressedSignal
