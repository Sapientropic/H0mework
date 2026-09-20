import H0mework.Physics.LowEnergyMatterSpace.GeneratorDomain
import H0mework.Physics.LowEnergyMatterSpace.Phase
import H0mework.Physics.LowEnergyMatterSpace.Connection

/-! Schwartz fields enter the exact source domain and recover the original spatial derivatives. -/
set_option autoImplicit false
open MeasureTheory Filter Topology FourierTransform LineDeriv
open scoped SchwartzMap InnerProductSpace Matrix Kronecker
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
open Fermion DiracCliffordRepresentation Stage9C.Material.SpinPair
noncomputable section
attribute [local instance] instLinearOrderSourceIndex

private theorem derivative_scalar (L : MatterFiber →L[ℂ] MatterFiber) (r : ℝ) (v : MatterFiber) :
    (-Complex.I) • L ((2*Real.pi*Complex.I : ℂ) • (r • v))=
      ((2*Real.pi*r : ℝ) : ℂ) • L v := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) r v,map_smul,map_smul]
  simp only [smul_smul]
  congr 1
  push_cast
  ring_nf
  simp [Complex.I_sq]

def spatialDirection (j : Fin 3) : Position := EuclideanSpace.basisFun (Fin 3) ℝ j

def sourceDifferential (f : 𝓢(Position, MatterFiber)) : 𝓢(Position, MatterFiber) :=
  f.postcompCLM (hamiltonianOperator sourceConstant)+
    (-Complex.I) • ∑ j, (∂_{spatialDirection j} f).postcompCLM (hamiltonianOperator (sourceSpatial j))

attribute [local irreducible] sourceConstant sourceSpatial sourceCharge sourceHamiltonian
  hamiltonianOperator spatialDirection sourceDifferential

theorem sourceDifferential_apply (f : 𝓢(Position, MatterFiber)) (x : Position) :
    sourceDifferential f x=hamiltonianOperator sourceConstant (f x)+
      (-Complex.I) • ∑ j, hamiltonianOperator (sourceSpatial j) ((∂_{spatialDirection j} f) x) := by
  simp [sourceDifferential]

theorem sourceHamiltonian_operator_sum (xi : Position) :
    hamiltonianOperator (actualFourierHamiltonian xi)=hamiltonianOperator sourceConstant+
      ∑ j, ((2*Real.pi*xi j : ℝ) : ℂ) • hamiltonianOperator (sourceSpatial j) := by
  rw [actualFourierHamiltonian_value]
  simp [hamiltonianOperator]

theorem sourceDifferential_fourier (f : 𝓢(Position, MatterFiber)) (xi : Position) :
    (𝓕 (sourceDifferential f)) xi=hamiltonianOperator (actualFourierHamiltonian xi) ((𝓕 f) xi) := by
  have term (j : Fin 3) :
      (-Complex.I) • ((𝓕 ((∂_{spatialDirection j} f).postcompCLM
        (hamiltonianOperator (sourceSpatial j)))) xi)=
      ((2*Real.pi*xi j : ℝ) : ℂ) • hamiltonianOperator (sourceSpatial j) ((𝓕 f) xi) := by
    rw [constant_map_fourier_schwartz,SchwartzMap.postcompCLM_apply]
    have growth : (fun y : Position => inner ℝ y (spatialDirection j)).HasTemperateGrowth :=
      ((innerSL ℝ).flip (spatialDirection j)).hasTemperateGrowth
    have derivative := congrArg (fun g : 𝓢(Position,MatterFiber) => g xi)
      (SchwartzMap.fourier_lineDerivOp_eq f (spatialDirection j))
    simp only [smul_apply] at derivative
    rw [SchwartzMap.smulLeftCLM_apply_apply growth] at derivative
    have coordinate : inner ℝ xi (spatialDirection j)=xi j := by
      unfold spatialDirection
      exact EuclideanSpace.inner_basisFun_real (Fin 3) xi j
    rw [coordinate] at derivative
    rw [derivative]
    rw [derivative_scalar]
  rw [sourceDifferential,FourierTransform.fourier_add,FourierTransform.fourier_smul,
    FourierTransform.fourier_sum,constant_map_fourier_schwartz,
    sourceHamiltonian_operator_sum]
  change hamiltonianOperator sourceConstant ((𝓕 f) xi)+
      (-Complex.I) • (∑ j, (𝓕 ((∂_{spatialDirection j} f).postcompCLM
        (hamiltonianOperator (sourceSpatial j)))) xi)=_
  simp only [Finset.smul_sum]
  rw [add_apply,sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact term j

theorem schwartz_energy_ae (f : 𝓢(Position, MatterFiber)) :
    sourceEnergyField (f.toLp 2)=ᵐ[volume] fun xi => (𝓕 (sourceDifferential f)) xi := by
  have input : fourier (f.toLp 2)=(𝓕 f).toLp 2 := SchwartzMap.toLp_fourier_eq f
  filter_upwards [(𝓕 f).coeFn_toLp 2 volume] with xi hxi
  change hamiltonianOperator (actualFourierHamiltonian xi) (fourier (f.toLp 2) xi)=_
  rw [input,hxi,sourceDifferential_fourier]

theorem schwartz_finite_energy (f : 𝓢(Position, MatterFiber)) :
    MemLp (sourceEnergyField (f.toLp 2)) 2 volume :=
  ((𝓕 (sourceDifferential f)).memLp 2 volume).ae_eq (schwartz_energy_ae f).symm

theorem schwartz_domain (f : 𝓢(Position, MatterFiber)) :
    (f.toLp 2 : MatterL2) ∈ Quantum.Generator.domain spatialAction :=
  (source_domain_iff (f.toLp 2)).mpr (schwartz_finite_energy f)

theorem schwartz_hamiltonian_value (f : 𝓢(Position, MatterFiber)) :
    Quantum.Generator.hamiltonian spatialAction (sourceDomainPoint (f.toLp 2) (schwartz_finite_energy f))=
      (sourceDifferential f).toLp 2 := by
  apply fourier.injective
  apply Lp.ext
  have left := source_hamiltonian_fourier_ae (f.toLp 2 volume) (schwartz_finite_energy f)
  have right : fourier ((sourceDifferential f).toLp 2 volume)=
      (𝓕 (sourceDifferential f)).toLp 2 volume := SchwartzMap.toLp_fourier_eq _
  rw [right]
  have bridge := schwartz_energy_ae f
  change (fun xi => hamiltonianOperator (actualFourierHamiltonian xi) (fourier (f.toLp 2 volume) xi))=ᵐ[volume]
    (fun xi => (𝓕 (sourceDifferential f)) xi) at bridge
  exact left.trans (bridge.trans (((𝓕 (sourceDifferential f)).coeFn_toLp 2 volume).symm))

def diracTimeRead : SourceMatrix :=
  (lapse : ℂ) • (diracGammaZero ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ))

def diracSpatialMatrix (j : Fin 3) : SourceMatrix :=
  diracGamma j.succ ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ)

theorem diracTimeRead_constant : diracTimeRead*occupiedDiracConstant=sourceConstant := by
  simpa only [diracTimeRead,Matrix.smul_mul] using sourceConstant_from_original_connection

theorem diracTimeRead_spatial (j : Fin 3) :
    Complex.I • (diracTimeRead*diracSpatialMatrix j)=(-Complex.I) • sourceSpatial j := by
  simp only [diracTimeRead,diracSpatialMatrix,sourceSpatial,Matrix.smul_mul,
    ← Matrix.mul_kronecker_mul,Matrix.one_mul,smul_smul]
  congr 1
  ring

private theorem operator_product (A B : SourceMatrix) (v : MatterFiber) :
    hamiltonianOperator (A*B) v=hamiltonianOperator A (hamiltonianOperator B v) := by
  unfold hamiltonianOperator
  rw [map_mul]
  rfl

private theorem operator_scalar (c : ℂ) (A : SourceMatrix) (v : MatterFiber) :
    hamiltonianOperator (c • A) v=c • hamiltonianOperator A v := by
  unfold hamiltonianOperator
  rw [map_smul]
  rfl

def occupiedSpatialDirac (f : 𝓢(Position,MatterFiber)) (x : Position) : MatterFiber :=
  hamiltonianOperator occupiedDiracConstant (f x)+
    Complex.I • ∑ j, hamiltonianOperator (diracSpatialMatrix j) ((∂_{spatialDirection j} f) x)

theorem sourceDifferential_from_original_connection (f : 𝓢(Position,MatterFiber)) (x : Position) :
    sourceDifferential f x=hamiltonianOperator diracTimeRead (occupiedSpatialDirac f x) := by
  rw [sourceDifferential_apply,occupiedSpatialDirac,map_add,map_smul,map_sum,
    ← operator_product,diracTimeRead_constant]
  congr 1
  rw [Finset.smul_sum,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← operator_product,← operator_scalar,← operator_scalar,diracTimeRead_spatial]

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
