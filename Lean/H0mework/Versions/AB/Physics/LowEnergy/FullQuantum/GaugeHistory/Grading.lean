import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.GaugeHistory.Interaction

/-! The same exterior projection is preserved by the generated nonautonomous gauge development. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeHistory
open FullSpace GaugeGreen ScalarGreen Triangular YangMills.FullPairing
open ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair
noncomputable section

theorem freeMatrices_six (time : ℝ) (frequency : Position) :
    Commute (operator MixedSymbol.degreeSix) (freeMatrices time frequency) :=
  commutes_flow _ _ (operator_commute _ _ (grade_freeDrift 0 actual 0 (physicalMomentum frequency))) time

theorem momentumFree_six (time : ℝ) (field : FullMatterL2) :
    six (momentumFree time field)=momentumFree time (six field) := by
  apply Lp.ext
  filter_upwards [six_ae (momentumFree time field),momentumFree_ae time field,
    momentumFree_ae time (six field),six_ae field] with frequency outer applied projected inner
  rw [outer,applied,projected,inner]
  exact congrArg (fun A : FiberOperators => A (field frequency)) (freeMatrices_six time frequency).eq

theorem spatialFree_six (time : ℝ) (field : FullMatterL2) :
    six (spatialFree time field)=spatialFree time (six field) := by
  apply fourier.injective
  rw [six_fourier,spatialFree_fourier,spatialFree_fourier,six_fourier,momentumFree_six]

theorem interactionHamiltonian_six (profile : ℝ → GaugeProfile) (time : ℝ) (field : FullMatterL2) :
    six (interactionHamiltonian profile time field)=interactionHamiltonian profile time (six field) := by
  simp only [interactionHamiltonian_apply,spatialFree_six,gaugePotential_six]

theorem native_curve_six (profile : ℝ → GaugeProfile) (continuousProfile : Continuous profile)
    (epsilon start time : ℝ) (initial : FullMatterL2) :
    six ((nativeDevelopment profile continuousProfile).curve epsilon start initial time)=
      (nativeDevelopment profile continuousProfile).curve epsilon start (six initial) time := by
  let d := nativeDevelopment profile continuousProfile
  have evolves (t : ℝ) : HasDerivAt (fun u => six (d.curve epsilon start initial u))
      (generator (interactionHamiltonian profile) epsilon t (six (d.curve epsilon start initial t))) t := by
    have generated := (six.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (d.evolves epsilon start initial t)
    simpa only [ContinuousLinearMap.coe_restrictScalars',Function.comp_def,generator,
      smul_apply,map_smul,interactionHamiltonian_six] using! generated
  exact congrFun (global_curve_unique _ (interactionHamiltonian_selfAdjoint profile) epsilon start
    (fun u => six (d.curve epsilon start initial u)) (d.curve epsilon start (six initial))
    evolves (d.evolves epsilon start (six initial)) (by rw [d.starts,d.starts])) time

theorem gaugeUnitary_six (profile : ℝ → GaugeProfile) (continuousProfile : Continuous profile)
    (epsilon start time : ℝ) (initial : FullMatterL2) :
    six (gaugeUnitary profile continuousProfile epsilon start time initial)=
      gaugeUnitary profile continuousProfile epsilon start time (six initial) := by
  simp only [gaugeUnitary_apply,spatialFree_six,native_curve_six]

theorem gaugeUnitary_inverse (profile : ℝ → GaugeProfile) (continuousProfile : Continuous profile)
    (epsilon start time : ℝ) (initial : FullMatterL2) :
    gaugeUnitary profile continuousProfile epsilon time start
      (gaugeUnitary profile continuousProfile epsilon start time initial)=initial := by
  rw [gaugeUnitary_compose,gaugeUnitary_starts]

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeHistory
