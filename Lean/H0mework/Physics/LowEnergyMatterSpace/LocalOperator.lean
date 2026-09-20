import H0mework.Physics.LowEnergyMatterSpace.CurrentOperator
import Mathlib.MeasureTheory.Function.Holder

/-! Bounded spatial profiles generate the local gauge and current operators. -/
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
open Fermion SU7MotherLieAlgebra DiracCliffordRepresentation
noncomputable section
attribute [local instance] instLinearOrderSourceIndex

abbrev BoundedProfile := Lp (α := Position) ℂ ⊤ volume

def boundedMultiplier (profile : BoundedProfile) : MatterL2 →L[ℂ] MatterL2 :=
  (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] MatterFiber →L[ℂ] MatterFiber).holderL volume ⊤ 2 2 profile

theorem boundedMultiplier_ae (profile : BoundedProfile) (v : MatterL2) :
    boundedMultiplier profile v=ᵐ[volume] fun x => profile x • v x :=
  (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] MatterFiber →L[ℂ] MatterFiber).coeFn_holder profile v

theorem boundedMultiplier_selfAdjoint (profile : BoundedProfile)
    (real : ∀ᵐ x ∂volume, star (profile x)=profile x) :
    IsSelfAdjoint (boundedMultiplier profile) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro u v
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [boundedMultiplier_ae profile u,boundedMultiplier_ae profile v,real] with x hu hv hx
  change inner ℂ (boundedMultiplier profile u x) (v x)=inner ℂ (u x) (boundedMultiplier profile v x)
  rw [hu,hv,inner_smul_left,inner_smul_right]
  simpa only [Complex.star_def] using congrArg (fun c : ℂ => c*inner ℂ (u x) (v x)) hx

def localMatrixOperator (profile : BoundedProfile) (A : SourceMatrix) : MatterL2 →L[ℂ] MatterL2 :=
  (boundedMultiplier profile).comp ((hamiltonianOperator A).compLpL 2 volume)

theorem localMatrixOperator_ae (profile : BoundedProfile) (A : SourceMatrix) (v : MatterL2) :
    localMatrixOperator profile A v=ᵐ[volume] fun x => profile x • hamiltonianOperator A (v x) := by
  filter_upwards [boundedMultiplier_ae profile ((hamiltonianOperator A).compLpL 2 volume v),
    (hamiltonianOperator A).coeFn_compLpL v] with x hg hA
  change boundedMultiplier profile ((hamiltonianOperator A).compLpL 2 volume v) x=_
  rw [hg,hA]

theorem localMatrixOperator_selfAdjoint (profile : BoundedProfile)
    (real : ∀ᵐ x ∂volume, star (profile x)=profile x) (A : SourceMatrix)
    (hermitian : A.conjTranspose=A) : IsSelfAdjoint (localMatrixOperator profile A) := by
  have finite : IsSelfAdjoint (hamiltonianOperator A) := by
    change star (hamiltonianOperator A)=hamiltonianOperator A
    unfold hamiltonianOperator
    rw [← map_star]
    exact congrArg (Matrix.toEuclideanCLM (n := SourceIndex) (𝕜 := ℂ)) hermitian
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro u v
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [localMatrixOperator_ae profile A u,localMatrixOperator_ae profile A v,real]
    with x hu hv hx
  change inner ℂ (localMatrixOperator profile A u x) (v x)=
    inner ℂ (u x) (localMatrixOperator profile A v x)
  have symmetric := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp finite) (u x) (v x)
  change inner ℂ (hamiltonianOperator A (u x)) (v x)=
    inner ℂ (u x) (hamiltonianOperator A (v x)) at symmetric
  rw [hu,hv,inner_smul_left,inner_smul_right,symmetric]
  simpa only [Complex.star_def] using
    congrArg (fun c : ℂ => c*inner ℂ (u x) (hamiltonianOperator A (v x))) hx

def localGaugeHamiltonian (profile : BoundedProfile) (data : LorentzianIndex → P286LieBlockData) :
    MatterL2 →L[ℂ] MatterL2 := localMatrixOperator profile (gaugeHamiltonianMatrix data)

def localCurrentOperator (profile : BoundedProfile) (data : LorentzianIndex → P286LieBlockData) :
    MatterL2 →L[ℂ] MatterL2 := localMatrixOperator profile (gaugeCurrentMatrix data)

theorem localGaugeHamiltonian_selfAdjoint (profile : BoundedProfile)
    (real : ∀ᵐ x ∂volume, star (profile x)=profile x) (data : LorentzianIndex → P286LieBlockData) :
    IsSelfAdjoint (localGaugeHamiltonian profile data) :=
  localMatrixOperator_selfAdjoint profile real _ (gaugeHamiltonianMatrix_hermitian data)

theorem localCurrentOperator_selfAdjoint (profile : BoundedProfile)
    (real : ∀ᵐ x ∂volume, star (profile x)=profile x) (data : LorentzianIndex → P286LieBlockData) :
    IsSelfAdjoint (localCurrentOperator profile data) :=
  localMatrixOperator_selfAdjoint profile real _ (gaugeCurrentMatrix_hermitian data)

theorem localMatrixOperator_continuous (A : SourceMatrix) :
    Continuous (fun profile : BoundedProfile => localMatrixOperator profile A) := by
  unfold localMatrixOperator boundedMultiplier
  fun_prop

theorem localGaugeHistory_continuous (profile : ℝ → BoundedProfile)
    (continuousProfile : Continuous profile) (data : LorentzianIndex → P286LieBlockData) :
    Continuous (fun t => localGaugeHamiltonian (profile t) data) :=
  (localMatrixOperator_continuous _).comp continuousProfile

theorem localCurrent_original (profile : BoundedProfile)
    (real : ∀ᵐ x ∂volume, star (profile x)=profile x)
    (data : LorentzianIndex → P286LieBlockData) (v : MatterL2) :
    (inner ℂ v (localCurrentOperator profile data v)).re=
      ∫ x, (profile x).re * gaugeCurrentValue data (v x)
        ((Stage9C.Material.SpinPair.spinScale : ℂ) •
          StageNineFullDiracAdjointMaterial.fullCanonicalDiracAdjoint (tripletLift (v x))) := by
  have pointwise : (fun x => inner ℂ (v x) (localCurrentOperator profile data v x))=ᵐ[volume]
      fun x => profile x*inner ℂ (v x) (hamiltonianOperator (gaugeCurrentMatrix data) (v x)) := by
    filter_upwards [localMatrixOperator_ae profile (gaugeCurrentMatrix data) v] with x hx
    change inner ℂ (v x) (localMatrixOperator profile (gaugeCurrentMatrix data) v x)=_
    rw [hx,inner_smul_right]
  have integrable := (L2.integrable_inner (𝕜 := ℂ) v (localCurrentOperator profile data v)).congr pointwise
  rw [L2.inner_def,integral_congr_ae pointwise]
  change RCLike.re (∫ x, profile x*inner ℂ (v x)
    (hamiltonianOperator (gaugeCurrentMatrix data) (v x)))=_
  rw [← integral_re integrable]
  apply integral_congr_ae
  filter_upwards [real] with x hx
  have imaginary : (profile x).im=0 := by
    have same := congrArg Complex.im hx
    simp only [Complex.star_def,Complex.conj_im] at same
    linarith
  change (profile x*inner ℂ (v x) (hamiltonianOperator (gaugeCurrentMatrix data) (v x))).re=_
  rw [gaugeCurrent_canonical,Complex.mul_re,imaginary,zero_mul,sub_zero]

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
