import H0mework.Physics.RLCResponse.Response

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace RLCSourceInverse

open Physical.Interface Units.Interface
open Netlist.Dissipative.Producer Netlist.Producer
open Netlist.Dissipative.Dimensioned.Producer Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section

theorem flow_left_inverse (run : FiniteSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (time : ℝ) :
    finiteSeriesRLCFlowAt run (finiteSeriesRLCFlowAt run initial time) (-time) = initial := by
  funext channel
  have rotation := congrFun (harmonicFlow_neg_leftInverse
    (run.baseRun.frequencyAt channel * time) initial) channel
  have scales : Real.exp (-run.dampingRateAt channel * -time) *
      Real.exp (-run.dampingRateAt channel * time) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  simp only [harmonicFlow, sourcePort, targetPort, Real.cos_neg, Real.sin_neg] at rotation
  apply Prod.ext
  · have inverse := congrArg Prod.fst rotation
    simp only [finiteSeriesRLCFlowAt, finiteSeriesRLCScaleAt, finiteParallelLCFlowAt,
      harmonicFlow, sourcePort, targetPort, mul_neg, Real.cos_neg, Real.sin_neg]
    calc
      _ = (Real.exp (-run.dampingRateAt channel * -time) * Real.exp (-run.dampingRateAt channel * time)) *
          (Real.cos (run.baseRun.frequencyAt channel * time) *
              (Real.cos (run.baseRun.frequencyAt channel * time) * (initial channel).1 -
                Real.sin (run.baseRun.frequencyAt channel * time) * (initial channel).2) +
            Real.sin (run.baseRun.frequencyAt channel * time) *
              (Real.sin (run.baseRun.frequencyAt channel * time) * (initial channel).1 +
                Real.cos (run.baseRun.frequencyAt channel * time) * (initial channel).2)) := by
                  simp only [mul_neg]
                  ring
      _ = (initial channel).1 := by
        rw [scales, one_mul]
        simpa only [neg_mul, sub_neg_eq_add] using inverse
  · have inverse := congrArg Prod.snd rotation
    simp only [finiteSeriesRLCFlowAt, finiteSeriesRLCScaleAt, finiteParallelLCFlowAt,
      harmonicFlow, sourcePort, targetPort, mul_neg, Real.cos_neg, Real.sin_neg]
    calc
      _ = (Real.exp (-run.dampingRateAt channel * -time) * Real.exp (-run.dampingRateAt channel * time)) *
          (-Real.sin (run.baseRun.frequencyAt channel * time) *
              (Real.cos (run.baseRun.frequencyAt channel * time) * (initial channel).1 -
                Real.sin (run.baseRun.frequencyAt channel * time) * (initial channel).2) +
            Real.cos (run.baseRun.frequencyAt channel * time) *
              (Real.sin (run.baseRun.frequencyAt channel * time) * (initial channel).1 +
                Real.cos (run.baseRun.frequencyAt channel * time) * (initial channel).2)) := by
                  simp only [mul_neg]
                  ring
      _ = (initial channel).2 := by rw [scales, one_mul]; exact inverse

end
end RLCSourceInverse
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
