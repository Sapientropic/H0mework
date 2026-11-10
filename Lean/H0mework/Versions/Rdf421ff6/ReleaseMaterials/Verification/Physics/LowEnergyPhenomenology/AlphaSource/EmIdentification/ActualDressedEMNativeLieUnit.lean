import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMNativeAuxiliaryPencil

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMNativeAuxiliary
open SourcePropagationNativeActionHessian
open scoped Matrix BigOperators

def auxiliaryLieReader {K : Type*} [Field K] (v : Fin 12 → K) : Fin 12 → K :=
  fun i => if i=6 then 2*v 6+v 7 else if i=7 then v 6+2*v 7 else if i=11 then v 11 else 2*v i

def auxiliaryLieInverse {K : Type*} [Field K] (v : Fin 12 → K) : Fin 12 → K :=
  fun i => if i=6 then (2/3)*v 6-(1/3)*v 7 else if i=7 then -(1/3)*v 6+(2/3)*v 7
    else if i=11 then v 11 else (1/2)*v i

theorem auxiliary_lie_inverse_right {K : Type*} [Field K] [CharZero K] (v : Fin 12 → K) :
    auxiliaryLieReader (auxiliaryLieInverse v)=v := by
  funext i
  by_cases six : i=6
  · subst i;simp [auxiliaryLieReader,auxiliaryLieInverse];ring
  by_cases seven : i=7
  · subst i;simp [auxiliaryLieReader,auxiliaryLieInverse];ring
  by_cases eleven : i=11
  · subst i;simp [auxiliaryLieReader,auxiliaryLieInverse]
  simp [auxiliaryLieReader,auxiliaryLieInverse,six,seven,eleven]

theorem auxiliary_lie_inverse_left {K : Type*} [Field K] [CharZero K] (v : Fin 12 → K) :
    auxiliaryLieInverse (auxiliaryLieReader v)=v := by
  funext i
  by_cases six : i=6
  · subst i;simp [auxiliaryLieReader,auxiliaryLieInverse];ring
  by_cases seven : i=7
  · subst i;simp [auxiliaryLieReader,auxiliaryLieInverse];ring
  by_cases eleven : i=11
  · subst i;simp [auxiliaryLieReader,auxiliaryLieInverse]
  simp [auxiliaryLieReader,auxiliaryLieInverse,six,seven,eleven]

/-- The native colour pairing fixes this inverse; it is not an electromagnetic mode norm. -/
theorem source_raw_gauge_lie_reader (u v : Fin 12 → ℝ) :
    rawGaugePair u v=dotProduct u (auxiliaryLieReader v) := by
  simp [rawGaugePair,auxiliaryLieReader,dotProduct,Fin.sum_univ_succ]
  ring

end LowEnergy.GaussComposite.ActualDressedEMNativeAuxiliary
