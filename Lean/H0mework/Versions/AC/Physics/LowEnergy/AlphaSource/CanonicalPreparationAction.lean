import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationMomentum
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.GaussFullHamiltonian

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.CanonicalPreparationMomentum
open SaturationMonoid.PhysicsCore
open SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open GaussCoreHilbert GaussDensityCore GaussHistoryHilbert
open CanonicalPreparationCore CanonicalPreparationCreation GaussComposite.SourceGraph
open scoped ContDiff Distributions
attribute [local instance] SourceRealScalarFock.branchOrder

private def fiberSection (v : FockFiber) : ScalarTest →ₗ[ℂ] GaussCoreDifferential.QuantumTest :=
  (TestFunction.postcompCLM ((ContinuousLinearMap.id ℂ ℂ).smulRight v)).toLinearMap

private theorem section_component (v : FockFiber) (f : ScalarTest) (word : Occupation) :
    component word (fiberSection v f)=v word • f := by
  apply DFunLike.ext
  intro z
  change f z*v word=v word*f z
  ring

private theorem section_derivative (v : FockFiber) (D : SourceCoordinateSlice) (f : ScalarTest) :
    GaussCoframeCore.derivative D (fiberSection v f)=fiberSection v (GaussDensityCore.derivative D f) := by
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  have h := GaussCoframeCore.component_derivative D (fiberSection v f) word
  rw [section_component,map_smul] at h
  have out := congrArg (fun t : ScalarTest => t z) h
  change GaussCoframeCore.derivative D (fiberSection v f) z word=
    GaussDensityCore.derivative D f z*v word
  exact out.trans (mul_comm _ _)

private theorem section_transpose (N : ℕ) (v : FockFiber)
    (concentrated : ∀ word : Occupation, word.card≠N → v word=0)
    (D : SourceCoordinateSlice) (f : ScalarTest) :
    GaussCoframeCore.transpose D (fiberSection v f)=fiberSection v (weightedTranspose N D f) := by
  apply embed_injective
  rw [GaussCoframeCore.transpose_embed]
  apply PiLp.ext
  intro word
  change scalarLp word.card (weightedTranspose word.card D (component word (fiberSection v f)))=
    scalarLp word.card (component word (fiberSection v (weightedTranspose N D f)))
  rw [section_component,section_component,map_smul,scalarLp_smul,scalarLp_smul]
  by_cases h : word.card=N
  · rw [h]
  · rw [concentrated word h]
    simp

def coframeCoefficient (i j : Fin 6) : ScalarTest →ₗ[ℂ] ScalarTest :=
  GaussDensityCore.multiply (fun z => (GaussCoframeKinetic.coefficient i j z : ℂ))
    (fun z => Complex.ofRealCLM.contDiff.contDiffAt.comp z.val
      (GaussCoframeKinetic.coefficient_smooth i j z))

def coframeTerm (N : ℕ) (i j : Fin 6) : ScalarTest →ₗ[ℂ] ScalarTest :=
  (weightedTranspose N (GaussCoframeCore.coframeDirection i)).comp
    ((coframeCoefficient i j).comp (GaussDensityCore.derivative (GaussCoframeCore.coframeDirection j)))

def coframeKinetic (N : ℕ) : ScalarTest →ₗ[ℂ] ScalarTest :=
  ∑ i : Fin 6, ∑ j : Fin 6, coframeTerm N i j

private theorem section_coefficient (v : FockFiber) (i j : Fin 6) (f : ScalarTest) :
    GaussNativeForm.multiply (GaussCoframeKinetic.coefficient i j)
      (GaussCoframeKinetic.coefficient_smooth i j) (fiberSection v f)=
      fiberSection v (coframeCoefficient i j f) := by
  apply DFunLike.ext
  intro z
  change (GaussCoframeKinetic.coefficient i j z : ℂ) • (f z • v)=
    ((GaussCoframeKinetic.coefficient i j z : ℂ)*f z) • v
  exact (mul_smul _ _ _).symm

private theorem section_term (N : ℕ) (v : FockFiber)
    (concentrated : ∀ word : Occupation, word.card≠N → v word=0)
    (i j : Fin 6) (f : ScalarTest) :
    GaussCoframeKinetic.term i j (fiberSection v f)=fiberSection v (coframeTerm N i j f) := by
  simp only [GaussCoframeKinetic.term,GaussCoframeCore.momentum,GaussCoframeCore.adjoint,
    LinearMap.comp_apply,LinearMap.smul_apply]
  rw [section_derivative,map_smul,section_coefficient,map_smul,section_transpose N v concentrated]
  simp only [smul_smul,mul_neg,Complex.I_mul_I,neg_neg,one_smul]
  rfl

private theorem section_kinetic (N : ℕ) (v : FockFiber)
    (concentrated : ∀ word : Occupation, word.card≠N → v word=0) (f : ScalarTest) :
    GaussCoframeKinetic.kinetic (fiberSection v f)=fiberSection v (coframeKinetic N f) := by
  simp only [GaussCoframeKinetic.kinetic,coframeKinetic,LinearMap.sum_apply,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact section_term N v concentrated i j f

def vacuumSection : ScalarTest →ₗ[ℂ] GaussCoreDifferential.QuantumTest := fiberSection vacuumFiber

theorem original_vacuum_kinetic (f : ScalarTest) :
    GaussCoframeKinetic.kinetic (vacuumSection f)=vacuumSection (coframeKinetic 0 f) := by
  apply section_kinetic
  intro word h
  have nonempty : word≠∅ := by intro he; subst word; exact h rfl
  rw [vacuumFiber_single]
  simp [EuclideanSpace.single,nonempty]

theorem original_seed_kinetic (f : ScalarTest) :
    GaussCoframeKinetic.kinetic (seedSection f)=seedSection (coframeKinetic 1 f) :=
  section_kinetic 1 CanonicalCompletedSector.seed seed_zero_off_one f

theorem original_symmetric_momentum (i : Fin 6) (f : ScalarTest) :
    (1/2 : ℂ) • (GaussCoframeCore.momentum i (createdCore f)+
      GaussCoframeCore.adjoint i (createdCore f))=
      createdCore ((1/2 : ℂ) •
        ((-Complex.I) • GaussDensityCore.derivative (GaussCoframeCore.coframeDirection i) f+
          Complex.I • weightedTranspose 0 (GaussCoframeCore.coframeDirection i) f)) := by
  change (1/2 : ℂ) •
    ((-Complex.I) • GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i)
      (fiberSection CanonicalCompletedSector.seed (numberRaiseCore f))+
    Complex.I • GaussCoframeCore.transpose (GaussCoframeCore.coframeDirection i)
      (fiberSection CanonicalCompletedSector.seed (numberRaiseCore f)))=_
  rw [section_derivative,section_transpose 1 CanonicalCompletedSector.seed seed_zero_off_one]
  have h := congrArg (fiberSection CanonicalCompletedSector.seed)
    (weighted_symmetric_momentum (GaussCoframeCore.coframeDirection i) f)
  have hs : fiberSection CanonicalCompletedSector.seed=seedSection := rfl
  rw [hs] at h ⊢
  simpa only [createdCore,map_smul,map_add] using h

def coframeCorrectionTerm (i j : Fin 6) (f : ScalarTest) : ScalarTest :=
  -weightedTranspose 0 (GaussCoframeCore.coframeDirection i)
    (coframeCoefficient i j (drift (GaussCoframeCore.coframeDirection j) f))-
  drift (GaussCoframeCore.coframeDirection i)
    (coframeCoefficient i j (GaussDensityCore.derivative (GaussCoframeCore.coframeDirection j) f))+
  drift (GaussCoframeCore.coframeDirection i)
    (coframeCoefficient i j (drift (GaussCoframeCore.coframeDirection j) f))

def coframeCorrection (f : ScalarTest) : ScalarTest :=
  ∑ i : Fin 6, ∑ j : Fin 6, coframeCorrectionTerm i j f

theorem coefficient_numberRaise (i j : Fin 6) (f : ScalarTest) :
    coframeCoefficient i j (numberRaiseCore f)=numberRaiseCore (coframeCoefficient i j f) :=
  (numberRaiseCore_multiply _ _ f).symm

theorem term_numberRaise (i j : Fin 6) (f : ScalarTest) :
    coframeTerm 1 i j (numberRaiseCore f)=
      numberRaiseCore (coframeTerm 0 i j f+coframeCorrectionTerm i j f) := by
  change weightedTranspose 1 (GaussCoframeCore.coframeDirection i)
    (coframeCoefficient i j (GaussDensityCore.derivative (GaussCoframeCore.coframeDirection j)
      (numberRaiseCore f)))=_
  rw [derivative_numberRaise,coefficient_numberRaise,transpose_numberRaise]
  simp only [coframeTerm,coframeCorrectionTerm,LinearMap.comp_apply,map_add,map_sub,map_neg]
  module

theorem kinetic_numberRaise (f : ScalarTest) :
    coframeKinetic 1 (numberRaiseCore f)=numberRaiseCore (coframeKinetic 0 f+coframeCorrection f) := by
  simp only [coframeKinetic,coframeCorrection,LinearMap.sum_apply,term_numberRaise,
    map_add,map_sum,Finset.sum_add_distrib]

theorem original_kinetic_creation (f : ScalarTest) :
    GaussCoframeKinetic.kinetic (createdCore f)=
      createdCore (coframeKinetic 0 f+coframeCorrection f) := by
  change GaussCoframeKinetic.kinetic (seedSection (numberRaiseCore f))=_
  rw [original_seed_kinetic,kinetic_numberRaise]
  rfl

theorem original_kinetic_sourceCreated_difference (f : ScalarTest) :
    embed (GaussCoframeKinetic.kinetic (createdCore f))-
      sourceCreated (GaussHalfDensity.halfDensityEquiv 0 (scalarLp 0 (coframeKinetic 0 f)))=
      sourceCreated (GaussHalfDensity.halfDensityEquiv 0 (scalarLp 0 (coframeCorrection f))) := by
  rw [sourceCreated_core,sourceCreated_core,original_kinetic_creation]
  simp only [createdCore,map_add,add_sub_cancel_left]

theorem original_full_creation_return (f : ScalarTest) :
    GaussFullHamiltonian.fullAction (createdCore f)=
      createdCore (coframeKinetic 0 f+coframeCorrection f)+
      GaussNativeForm.nativeAction (createdCore f)+GaussCoframeForm.currentAction (createdCore f)+
      (∑ a : Fin 7, GaussCoframeForm.spinSquare a (createdCore f))+
      GaussCoframeForm.numberShift (createdCore f)+
      GaussNativeForm.multiply GaussCoframeForm.volumePotential
        GaussCoframeForm.volumePotential_smooth (createdCore f)+
      GaussMatterCore.matterAction (createdCore f)+GaussYukawaOperator.originalAction (createdCore f) := by
  simp only [GaussFullHamiltonian.fullAction,GaussDiagonalHistory.diagonalAction,
    GaussCoframeForm.coframeAction,LinearMap.add_apply,LinearMap.sum_apply]
  rw [original_kinetic_creation]
  abel

end LowEnergy.CanonicalPreparationMomentum
