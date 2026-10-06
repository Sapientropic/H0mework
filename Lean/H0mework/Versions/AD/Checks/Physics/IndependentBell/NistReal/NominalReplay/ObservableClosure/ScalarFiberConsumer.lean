import H0mework.Versions.AD.Checks.Physics.IndependentBell.NistReal.NominalReplay.ObservableClosure.ScalarFiber
import H0mework.Versions.AD.Checks.Physics.IndependentBell.NistReal.NominalReplay.ObservableClosure.Closureconsumer

set_option autoImplicit false

namespace P23.ObservableClosure.ScalarFiber.Consumer

noncomputable section

def predictedFiberWindow (s : ScaledSource) (loss : ℝ) (hl : LegalLoss s loss)
    (seed cell : Cell) (w bgA bgB : ℝ) : P23.ObservableClosure.Consumer.Outcomes :=
  P23.ObservableClosure.Consumer.windowOutcomes (baseline s loss hl) cell bgA bgB
    (observedClosure s loss hl seed cell w)

theorem generated_window_readback (s : ScaledSource) (loss : ℝ) (hl : LegalLoss s loss)
    (seed : Cell) (w : ℝ) (hg : g (baseline s loss hl) seed ≠ 0)
    (hp : PhaseDomain s loss hl seed w) (cell : Cell) (bgA bgB : ℝ) :
    P23.ObservableClosure.Consumer.generatedWindow (generatedSnapshot s loss hl seed w hg hp) cell bgA bgB=
      predictedFiberWindow s loss hl seed cell w bgA bgB := by
  unfold P23.ObservableClosure.Consumer.generatedWindow
  rw [generated_cell_readback]
  rfl

theorem source_fiber_generates_seed_and_windows (s : ScaledSource) (loss : ℝ) (hl : LegalLoss s loss)
    (seed : Cell) (w : ℝ) (hg : g (baseline s loss hl) seed ≠ 0)
    (hp : PhaseDomain s loss hl seed w) (bgA bgB : ℝ) :
    let snap := generatedSnapshot s loss hl seed w hg hp
    h snap=s.h ∧ v snap=s.v ∧ ratio snap=s.r ∧ e snap=loss ∧
    pulse00 snap seed=w ∧
    (∀ a b, meanA snap a=scaledMeanA s a ∧ meanB snap b=scaledMeanB s b) ∧
    (∀ cell, P23.ObservableClosure.Consumer.generatedWindow snap cell bgA bgB=
      predictedFiberWindow s loss hl seed cell w bgA bgB) := by
  have hs := lossSnapshot_scaled s loss hl (inferredLambda s loss hl seed w)
    (inferred_lambda_bounds s loss hl seed w hg hp).1
    (inferred_lambda_bounds s loss hl seed w hg hp).2
  refine ⟨hs.1,hs.2.1,hs.2.2.1,hs.2.2.2,generated_seed_readback s loss hl seed w hg hp,?_,?_⟩
  · intro a b
    exact lossSnapshot_means s loss hl (inferredLambda s loss hl seed w)
      (inferred_lambda_bounds s loss hl seed w hg hp).1
      (inferred_lambda_bounds s loss hl seed w hg hp).2 a b
  · intro cell
    exact generated_window_readback s loss hl seed w hg hp cell bgA bgB

end
end P23.ObservableClosure.ScalarFiber.Consumer
