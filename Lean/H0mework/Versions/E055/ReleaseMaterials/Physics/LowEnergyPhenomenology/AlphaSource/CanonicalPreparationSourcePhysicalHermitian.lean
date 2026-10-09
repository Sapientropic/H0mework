import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceNativePolePrice

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalCharacteristic
open PreparationVacuumOriginalGreenFeedback PreparationVacuumMixedPrincipal PreparationVacuumMixedEffective
open PreparationVacuumFullOriginResponse CanonicalGradedSpatialSource
open scoped Matrix BigOperators Topology

/-- Original Fourier clock and spatial coordinates; omega is not a fitted propagation speed. -/
def physicalFrequencyMomentum (omega : ℝ) (k : PhysicalMomentum) : Fin 4→ℂ:=
  Fin.cases (-Complex.I*(omega:ℂ)) (fun j=>Complex.I*(k j:ℂ))

theorem physicalFrequencyMomentum_star (omega : ℝ) (k : PhysicalMomentum) :
    (fun i=>star (physicalFrequencyMomentum omega k i))= -physicalFrequencyMomentum omega k:=by
  funext i
  refine Fin.cases ?_ (fun j=>?_) i
  · simp [physicalFrequencyMomentum]
  · simp [physicalFrequencyMomentum]

private theorem coefficient_star (c : SourceCoefficient) : star (coefficientValue c)=coefficientValue c:=by
  simp [coefficientValue,rootTwo,rootFifteen]

private theorem powers_star (a : Powers) (p : Fin 4→ℂ) : star (a.value p)=a.value (fun i=>star (p i)):=by
  simp [Powers.value]

theorem sourceMatrix_adjoint (terms : List SourceTerm) (p : Fin 4→ℂ) :
    (sourceMatrix terms p).conjTranspose=(sourceMatrix terms (fun i=>star (p i))).transpose:=by
  induction terms with
  | nil=>simp only [sourceMatrix_nil,Matrix.conjTranspose_zero,Matrix.transpose_zero]
  | cons a rest ih=>
    have term : (a.matrix p).conjTranspose=(a.matrix (fun i=>star (p i))).transpose:=by
      simp only [SourceTerm.matrix,Matrix.conjTranspose_single,Matrix.transpose_single,star_mul,coefficient_star,powers_star,mul_comm]
    simp only [sourceMatrix_cons,Matrix.conjTranspose_add,Matrix.transpose_add,term,ih]

theorem physicalActive_hermitian (omega : ℝ) (k : PhysicalMomentum) :
    (activeKernel (physicalFrequencyMomentum omega k)).IsHermitian:=by
  change (activeKernel (physicalFrequencyMomentum omega k)).conjTranspose=activeKernel (physicalFrequencyMomentum omega k)
  calc
    _=(activeKernel (fun i=>star (physicalFrequencyMomentum omega k i))).transpose:=sourceMatrix_adjoint activeTerms _
    _=(activeKernel (-physicalFrequencyMomentum omega k)).transpose:=by rw [physicalFrequencyMomentum_star]
    _= _:=activeKernel_reflect _

theorem physicalOriginal_hermitian (omega : ℝ) (k : PhysicalMomentum) :
    (originalJacobi (physicalFrequencyMomentum omega k)).IsHermitian:=by
  change (originalJacobi (physicalFrequencyMomentum omega k)).conjTranspose=originalJacobi (physicalFrequencyMomentum omega k)
  calc
    _=(originalJacobi (fun i=>star (physicalFrequencyMomentum omega k i))).transpose:=sourceMatrix_adjoint originalJacobiTerms _
    _=(originalJacobi (-physicalFrequencyMomentum omega k)).transpose:=by rw [physicalFrequencyMomentum_star]
    _= _:=original_jacobi_reciprocity _

theorem physicalFrequencyMomentum_bound (omega : ℝ) (k : PhysicalMomentum) (r : ℝ)
    (clock : |omega|≤r) (space : ∀i,|k i|≤r) : ∀i,‖physicalFrequencyMomentum omega k i‖≤r:=by
  intro i
  refine Fin.cases ?_ (fun j=>?_) i
  · simpa only [physicalFrequencyMomentum,Fin.cases_zero,norm_mul,norm_neg,Complex.norm_I,
      Complex.norm_real,Real.norm_eq_abs,one_mul] using clock
  · simpa only [physicalFrequencyMomentum,Fin.cases_succ,norm_mul,Complex.norm_I,
      Complex.norm_real,Real.norm_eq_abs,one_mul] using space j

def physicalDomain : Set (ℝ×PhysicalMomentum):={x | |x.1|≤PreparationVacuumFullOriginResponse.sourceRadius ∧
  ∀i,|x.2 i|≤PreparationVacuumFullOriginResponse.sourceRadius}

def physicalPoint (x : physicalDomain) : PreparationVacuumFullOriginResponse.complementRegular:=
  PreparationVacuumFullOriginResponse.controlledPoint (physicalFrequencyMomentum x.val.1 x.val.2)
    (physicalFrequencyMomentum_bound _ _ _ x.property.1 x.property.2)

theorem physicalDomain_origin : ((0:ℝ),(0:PhysicalMomentum))∈physicalDomain:=by
  constructor
  · simpa only [abs_zero] using PreparationVacuumFullOriginResponse.sourceRadius_pos.le
  · intro i
    simpa only [Pi.zero_apply,abs_zero] using PreparationVacuumFullOriginResponse.sourceRadius_pos.le

private theorem projection_hermitian (flag : Fin 289→Bool) : (projectionMatrix flag).IsHermitian:=by
  simp [Matrix.IsHermitian,projectionMatrix]

private theorem frame_adjoint : fullKernelFrame.conjTranspose=fullKernelFrame.transpose:=by
  have h:=sourceMatrix_adjoint fullKernelTerms (0:Fin 4→ℂ)
  have zero : (fun i : Fin 4=>star ((0:Fin 4→ℂ) i))=0:=by funext i;exact star_zero _
  simpa only [zero,fullKernel_generated] using h

/-- Full source complement, without dropping the linear temporal dual block. -/
theorem physicalComplement_hermitian (omega : ℝ) (k : PhysicalMomentum) :
    (PreparationVacuumFullOriginResponse.complementKernel (physicalFrequencyMomentum omega k)).IsHermitian:=by
  have projection : fullComplementProjection.conjTranspose=fullComplementProjection:=projection_hermitian fullComplementFlag
  have active:=(physicalActive_hermitian omega k).eq
  simp only [Matrix.IsHermitian,PreparationVacuumFullOriginResponse.complementKernel,
    Matrix.conjTranspose_add,Matrix.conjTranspose_sub,Matrix.conjTranspose_mul,Matrix.conjTranspose_one,projection,active,mul_assoc]

theorem physicalGreen_hermitian (omega : ℝ) (k : PhysicalMomentum)
    (regular : physicalFrequencyMomentum omega k∈PreparationVacuumFullOriginResponse.complementRegular) :
    (PreparationVacuumFullOriginResponse.complementGreen ⟨physicalFrequencyMomentum omega k,regular⟩).IsHermitian:=by
  have projection : fullComplementProjection.conjTranspose=fullComplementProjection:=projection_hermitian fullComplementFlag
  have inverse:=(physicalComplement_hermitian omega k).inv.eq
  simp only [Matrix.IsHermitian,PreparationVacuumFullOriginResponse.complementGreen,
    Matrix.conjTranspose_mul,projection,inverse,mul_assoc]

theorem physicalEffective_hermitian (omega : ℝ) (k : PhysicalMomentum)
    (regular : physicalFrequencyMomentum omega k∈PreparationVacuumFullOriginResponse.complementRegular) :
    (PreparationVacuumFullOriginResponse.effectiveKernel ⟨physicalFrequencyMomentum omega k,regular⟩).IsHermitian:=by
  have active:=(physicalActive_hermitian omega k).eq
  have green:=(physicalGreen_hermitian omega k regular).eq
  have back : fullKernelFrame.transpose.conjTranspose=fullKernelFrame:=by
    rw [←frame_adjoint,Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.IsHermitian,PreparationVacuumFullOriginResponse.effectiveKernel,
    Matrix.conjTranspose_sub,Matrix.conjTranspose_mul,frame_adjoint,back,active,green,mul_assoc]

theorem physicalPoint_effective_hermitian (x : physicalDomain) :
    (PreparationVacuumFullOriginResponse.effectiveKernel (physicalPoint x)).IsHermitian:=
  physicalEffective_hermitian x.val.1 x.val.2 (physicalPoint x).property

end LowEnergy.PreparationVacuumPhysicalCharacteristic
