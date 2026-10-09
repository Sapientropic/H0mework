import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowConservation.SourceTimeIntegral

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowConservation

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient ContinuousSeed TrueFlowDifferential
open TrueFlowGeometry TrueTubeWholeActual WholeCellPartition Set
noncomputable section

def retime (p : BandPoint) (s : Time) : BandPoint :=
  ⟨Function.update p.val 2 s, by
    constructor
    · intro i
      by_cases time : i = 2
      · subst i
        rw [Function.update_self]
        have bound : fullLower 2 = (-(1 / 2) : ℝ) := by norm_num [fullLower, fullLowerQ, halfFlow_exact]
        rw [bound]
        exact s.property.1
      · simpa only [Function.update_of_ne time] using p.property.1 i
    · intro i
      by_cases time : i = 2
      · subst i
        rw [Function.update_self]
        have bound : fullUpper 2 = (1 / 2 : ℝ) := by norm_num [fullUpper, fullUpperQ, halfFlow_exact]
        rw [bound]
        exact s.property.2
      · simpa only [Function.update_of_ne time] using p.property.2 i⟩

@[simp] theorem retime_time (p : BandPoint) (s : Time) : actualParameterTime (retime p s) = s := by
  apply Subtype.ext
  exact Function.update_self 2 s p.val

@[simp] theorem retime_seed (p : BandPoint) (s : Time) :
    ContinuousParameterMap.initialMap 0 4 (retime p s).val =
      ContinuousParameterMap.initialMap 0 4 p.val := by
  simp only [ContinuousParameterMap.initialMap, bandSeed, bandU, retime,
    Function.update_of_ne (show (0 : Fin 3) ≠ 2 by decide),
    Function.update_of_ne (show (1 : Fin 3) ≠ 2 by decide)]

@[simp] theorem retime_seedDerivative (p : BandPoint) (s : Time) :
    seedFlowDerivative (retime p s) = seedFlowDerivative p := by
  unfold seedFlowDerivative
  rw [retime_seed]
  simp only [bandSeedDerivative, bandUDerivative, retime,
    Function.update_of_ne (show (0 : Fin 3) ≠ 2 by decide),
    Function.update_of_ne (show (1 : Fin 3) ≠ 2 by decide)]

theorem retime_initialDerivative (p : BandPoint) (s t : Time) :
    initialFlowDerivative (retime p s) t = initialFlowDerivative p t := by
  have derivative := initialFlow_hasStrictFDerivAt (retime p s) t
  rw [retime_seed] at derivative
  exact derivative.hasFDerivAt.unique (initialFlow_hasStrictFDerivAt p t).hasFDerivAt

theorem evolvingJacobian_eq_retimed (p : BandPoint) (s : Time) :
    evolvingJacobian p s = LinearMap.toMatrix' (trueJacobian (retime p s)).toLinearMap := by
  rw [trueJacobian_flow_factorization]
  change evolvingJacobian p s =
    LinearMap.toMatrix' ((initialFlowDerivative (retime p s)
      (actualParameterTime (retime p s))).comp (seedFlowDerivative (retime p s))).toLinearMap
  rw [retime_time, retime_initialDerivative, retime_seedDerivative]
  ext i j
  change extendPath (sourceResponse p (seedFlowDerivative p (Pi.single j 1))) (s : ℝ) i =
    sourceResponse p (seedFlowDerivative p (Pi.single j 1)) s i
  rw [extendPath_coe]

theorem evolvingJacobian_det_ne_zero (p : BandPoint) (s : Time) :
    (evolvingJacobian p s).det ≠ 0 := by
  rw [evolvingJacobian_eq_retimed, LinearMap.det_toMatrix']
  exact trueJacobian_det_ne_zero (retime p s)

end
end LAlanine40K2025.BasinRefinement.TrueFlowConservation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
