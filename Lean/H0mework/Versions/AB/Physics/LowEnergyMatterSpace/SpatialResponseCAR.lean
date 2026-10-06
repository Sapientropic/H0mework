import H0mework.Versions.AB.Physics.LowEnergyMatterSpace.SpatialResponseKubo
import H0mework.Versions.AB.Physics.LowEnergyMatterSpace.SpatialCARState

/-! The continuum Kubo kernel is read from complete CAR words on its actual source-prepared test span. -/
set_option autoImplicit false
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response
open SpatialCAR
noncomputable section

def kuboTests (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2) (current : MatterL2 →L[ℂ] MatterL2)
    (u : MatterL2) (t s : ℝ) : Bool → MatterL2 :=
  fun label => if label then heisenberg current t u else heisenberg (perturbation s) s u

def kuboCAR (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2) (current : MatterL2 →L[ℂ] MatterL2)
    (u : MatterL2) (t s : ℝ) : ℂ :=
  spatialMoment u (kuboTests perturbation current u t s)
      [.create none,.annihilate (some false),.create (some true),.annihilate none]-
    spatialMoment u (kuboTests perturbation current u t s)
      [.create none,.annihilate (some true),.create (some false),.annihilate none]

theorem kuboKernel_CAR (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2)
    (hermitian : ∀ s, IsSelfAdjoint (perturbation s)) (current : MatterL2 →L[ℂ] MatterL2)
    (currentHermitian : IsSelfAdjoint current) (u : MatterL2) (unit : ‖u‖=1) (t s : ℝ) :
    kuboKernel perturbation current u t s=kuboCAR perturbation current u t s := by
  have self : inner ℂ u u=1 := by rw [inner_self_eq_norm_sq_to_K,unit]; norm_num
  rw [kuboCAR,spatialMoment_fourPoint,spatialMoment_fourPoint]
  simp only [family,kuboTests,Bool.false_eq_true,↓reduceIte,self,mul_one]
  change inner ℂ u ((heisenberg (perturbation s) s) (heisenberg current t u)-
    (heisenberg current t) (heisenberg (perturbation s) s u))=_
  rw [inner_sub_right]
  exact congrArg₂ (·-·)
    (heisenberg_symmetric _ (hermitian s) s u (heisenberg current t u)).symm
    (heisenberg_symmetric _ currentHermitian t u (heisenberg (perturbation s) s u)).symm

theorem kuboCAR_continuous (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2)
    (continuousPerturbation : Continuous perturbation) (hermitian : ∀ s, IsSelfAdjoint (perturbation s))
    (current : MatterL2 →L[ℂ] MatterL2) (currentHermitian : IsSelfAdjoint current)
    (u : MatterL2) (unit : ‖u‖=1) (t : ℝ) : Continuous (kuboCAR perturbation current u t) := by
  have same : kuboCAR perturbation current u t=kuboKernel perturbation current u t :=
    funext fun s => (kuboKernel_CAR perturbation hermitian current currentHermitian u unit t s).symm
  rw [same]
  exact kuboKernel_continuous perturbation continuousPerturbation current u t

theorem source_currentVariation_CAR (preparation : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousPreparation : Continuous preparation) (preparedAt : ℝ)
    (nonzero : spatialPreparation preparation continuousPreparation preparedAt≠0)
    (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2) (continuousPerturbation : Continuous perturbation)
    (hermitian : ∀ s, IsSelfAdjoint (perturbation s)) (current : MatterL2 →L[ℂ] MatterL2)
    (currentHermitian : IsSelfAdjoint current) (t : ℝ) :
    currentVariation perturbation current (normalizedPreparation preparation continuousPreparation preparedAt) t=
      Complex.I*∫ s in (0 : ℝ)..t,
        kuboCAR perturbation current (normalizedPreparation preparation continuousPreparation preparedAt) t s := by
  rw [currentVariation_kubo perturbation continuousPerturbation hermitian]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  exact kuboKernel_CAR perturbation hermitian current currentHermitian _
    (normalizedPreparation_norm preparation continuousPreparation preparedAt nonzero) t s

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response
