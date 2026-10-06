import H0mework.Versions.AD.Checks.Physics.IndependentBell.NistReal.NominalReplay.ObservableClosure.FullStatisticalFiber.Phasefiber
import H0mework.Versions.AD.Checks.Physics.IndependentBell.NistReal.NominalReplay.ObservableClosure.Closureconsumer

/-! Same-source phase fibre directly generates complete N5/OR cell readouts. -/

set_option autoImplicit false

namespace P23.ObservableClosure.PhaseFiber.Consumer

open P23.ObservableClosure.Consumer

noncomputable section

def phaseWindow (raw : RawSource) (k : ℝ) (cell : Cell) (bgA bgB : ℝ) : Outcomes :=
  windowOutcomes raw.baseline cell bgA bgB (affinePulse raw cell k)

theorem generated_window_readback (raw : RawSource) (k : ℝ) (hk : PhysicalPhase raw k)
    (cell : Cell) (bgA bgB : ℝ) :
    generatedWindow (generatedSnapshot raw k hk) cell bgA bgB=
      phaseWindow raw k cell bgA bgB := by
  unfold generatedWindow
  rw [generated_all_cells]
  rfl

theorem shared_phase_relation (raw : RawSource) (k : ℝ) (hk : PhysicalPhase raw k)
    (cell0 cell1 : Cell) :
    g raw.baseline cell1*
      (pulse00 (generatedSnapshot raw k hk) cell0*E raw.baseline cell0 (e raw.baseline)-
        L raw.baseline cell0 (e raw.baseline))=
    g raw.baseline cell0*
      (pulse00 (generatedSnapshot raw k hk) cell1*E raw.baseline cell1 (e raw.baseline)-
        L raw.baseline cell1 (e raw.baseline)) := by
  rw [generated_all_cells,generated_all_cells]
  have he0 := ne_of_gt (E_pos raw.baseline cell0)
  have he1 := ne_of_gt (E_pos raw.baseline cell1)
  dsimp [affinePulse]
  field_simp [he0,he1]
  ring

def singleA (raw : RawSource) (a bgA : ℝ) : ℝ :=
  1-((1-bgA)/(1+meanA raw.baseline a))^5

def singleB (raw : RawSource) (b bgB : ℝ) : ℝ :=
  1-((1-bgB)/(1+meanB raw.baseline b))^5

theorem generated_marginals (raw : RawSource) (k : ℝ) (hk : PhysicalPhase raw k)
    (cell : Cell) (bgA bgB : ℝ) :
    let o := generatedWindow (generatedSnapshot raw k hk) cell bgA bgB
    o.both+o.onlyA=singleA raw cell.a bgA ∧
      o.both+o.onlyB=singleB raw cell.b bgB := by
  rw [generated_window_readback]
  dsimp [phaseWindow,windowOutcomes,singleA,singleB]
  constructor <;> ring

theorem no_signaling_restrictions (raw : RawSource) (k : ℝ) (hk : PhysicalPhase raw k)
    (a0 a1 b0 b1 bgA bgB : ℝ) :
    let s := generatedSnapshot raw k hk
    let c00 := generatedWindow s ⟨a0,b0⟩ bgA bgB
    let c01 := generatedWindow s ⟨a0,b1⟩ bgA bgB
    let c10 := generatedWindow s ⟨a1,b0⟩ bgA bgB
    let c11 := generatedWindow s ⟨a1,b1⟩ bgA bgB
    (c01.both+c01.onlyA=c00.both+c00.onlyA) ∧
    (c10.both+c10.onlyA=c11.both+c11.onlyA) ∧
    (c10.both+c10.onlyB=c00.both+c00.onlyB) ∧
    (c01.both+c01.onlyB=c11.both+c11.onlyB) := by
  dsimp only
  have h00 := generated_marginals raw k hk ⟨a0,b0⟩ bgA bgB
  have h01 := generated_marginals raw k hk ⟨a0,b1⟩ bgA bgB
  have h10 := generated_marginals raw k hk ⟨a1,b0⟩ bgA bgB
  have h11 := generated_marginals raw k hk ⟨a1,b1⟩ bgA bgB
  exact ⟨h01.1.trans h00.1.symm,h10.1.trans h11.1.symm,
    h10.2.trans h00.2.symm,h01.2.trans h11.2.symm⟩

structure GeneratedPhaseReadout (raw : RawSource) (cell0 cell1 : Cell)
    (lo0 hi0 lo1 hi1 k bgA bgB : ℝ) (hq : PhaseQualified raw cell0 cell1 lo0 hi0 lo1 hi1 k) :
    Prop where
  interference_eq : interference (generatedSnapshot raw k hq.physical)=k
  training : TrainingQualified raw (phaseRecipe raw k)
    (phase_recipe_bounds raw k hq.physical).1 (phase_recipe_bounds raw k hq.physical).2
    cell0 cell1 lo0 hi0 lo1 hi1
  pulse_readback : ∀ cell,
    pulse00 (generatedSnapshot raw k hq.physical) cell=affinePulse raw cell k
  window_readback : ∀ cell,
    generatedWindow (generatedSnapshot raw k hq.physical) cell bgA bgB=
      phaseWindow raw k cell bgA bgB
  marginals : ∀ cell,
    let o := generatedWindow (generatedSnapshot raw k hq.physical) cell bgA bgB
    o.both+o.onlyA=singleA raw cell.a bgA ∧ o.both+o.onlyB=singleB raw cell.b bgB

/-- The direct consumer preserves one generated source for both training and every heldout cell. -/
theorem generates_training_and_all_windows (raw : RawSource) (cell0 cell1 : Cell)
    (lo0 hi0 lo1 hi1 k bgA bgB : ℝ)
    (hq : PhaseQualified raw cell0 cell1 lo0 hi0 lo1 hi1 k) :
    GeneratedPhaseReadout raw cell0 cell1 lo0 hi0 lo1 hi1 k bgA bgB hq := by
  refine ⟨generated_interference raw k hq.physical,?_,generated_all_cells raw k hq.physical,
    fun cell => generated_window_readback raw k hq.physical cell bgA bgB,
    fun cell => generated_marginals raw k hq.physical cell bgA bgB⟩
  apply (training_qualified_iff_phase raw _ _ _ cell0 cell1 lo0 hi0 lo1 hi1).2
  change PhaseQualified raw cell0 cell1 lo0 hi0 lo1 hi1
    (interference (generatedSnapshot raw k hq.physical))
  simpa [generated_interference] using hq

end
end P23.ObservableClosure.PhaseFiber.Consumer
