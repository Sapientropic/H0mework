import H0mework.Physics.LowEnergy.FullQuantum.GaugeHistory.Interaction
import H0mework.Quantum.Generator.SelfAdjoint

/-! The generated complete gauge field satisfies the original free-domain weak time equation. -/
set_option autoImplicit false
open MeasureTheory Set
open scoped InnerProductSpace LinearPMap
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeHistory
open FullSpace GaugeGreen PerturbedGreen YangMills.FullPairing
noncomputable section

def freeAction : Multiplicative ℝ →* (FullMatterL2 ≃ₗᵢ[ℂ] FullMatterL2) where
  toFun t := freeUnitary t.toAdd
  map_one' := by apply LinearIsometryEquiv.ext; intro f; exact spatialFree_zero f
  map_mul' s t := by apply LinearIsometryEquiv.ext; intro f; exact spatialFree_add s.toAdd t.toAdd f

theorem freeAction_continuous (field : FullMatterL2) : Continuous (Quantum.Generator.orbit freeAction field) :=
  spatialFree_continuous field

theorem free_domain_derivative (field : Quantum.Generator.domain freeAction) (t : ℝ) :
    HasDerivAt (fun s => spatialFree s (field : FullMatterL2))
      (spatialFree t (Quantum.Generator.generator freeAction field)) t :=
  Quantum.Generator.orbit_hasDerivAt freeAction field t

theorem free_domain_dense : Dense (Quantum.Generator.domain freeAction : Set FullMatterL2) :=
  Quantum.Generator.domain_dense freeAction freeAction_continuous

theorem freeHamiltonian_selfAdjoint : IsSelfAdjoint (Quantum.Generator.hamiltonianOperator freeAction) :=
  Quantum.Generator.hamiltonianOperator_selfAdjoint freeAction freeAction_continuous

theorem gaugeUnitary_weak (profile : ℝ → GaugeProfile) (continuousProfile : Continuous profile)
    (epsilon start time : ℝ) (initial : FullMatterL2) (test : Quantum.Generator.domain freeAction) :
    HasDerivAt (fun t => inner ℂ (test : FullMatterL2)
      (gaugeUnitary profile continuousProfile epsilon start t initial))
      (-Complex.I*inner ℂ (Quantum.Generator.hamiltonian freeAction test)
        (gaugeUnitary profile continuousProfile epsilon start time initial)+
        inner ℂ (test : FullMatterL2) ((-Complex.I*(epsilon : ℂ)) •
          gaugePotential (profile time) (gaugeUnitary profile continuousProfile epsilon start time initial))) time := by
  have left := (free_domain_derivative test (-time)).scomp time (hasDerivAt_neg time)
  have right := gaugeUnitary_equation profile continuousProfile epsilon start time initial
  have paired := left.inner ℂ right
  have identity (t : ℝ) :
      inner ℂ (spatialFree (-t) (test : FullMatterL2))
        (spatialFree (-t) (gaugeUnitary profile continuousProfile epsilon start t initial))=
      inner ℂ (test : FullMatterL2) (gaugeUnitary profile continuousProfile epsilon start t initial) :=
    (freeUnitary (-t)).inner_map_map _ _
  simp only [Function.comp_apply,neg_smul,one_smul,inner_neg_left,identity] at paired
  have unitary (t : ℝ) (u v : FullMatterL2) : inner ℂ (spatialFree t u) (spatialFree t v)=inner ℂ u v :=
    (freeUnitary t).inner_map_map _ _
  simp only [inner_smul_right,unitary] at paired
  convert! paired using 1
  change (-Complex.I)*inner ℂ (Complex.I • Quantum.Generator.generator freeAction test)
    (gaugeUnitary profile continuousProfile epsilon start time initial)+
    inner ℂ (test : FullMatterL2) ((-Complex.I*(epsilon : ℂ)) •
      gaugePotential (profile time) (gaugeUnitary profile continuousProfile epsilon start time initial))=_
  rw [inner_smul_left,inner_smul_right]
  simp only [Complex.conj_I]
  ring_nf
  simp [Complex.I_sq,sub_eq_add_neg]

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeHistory
