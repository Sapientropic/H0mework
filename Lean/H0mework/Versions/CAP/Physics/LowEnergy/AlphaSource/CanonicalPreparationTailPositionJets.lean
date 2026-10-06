import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationTailGlobalGerms
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumTailSupport
open PreparationVacuumWholeTail PreparationVacuumLocalizedTail PreparationVacuumCanonicalMoyal
open PreparationVacuumMoyalSymmetry PreparationVacuumClockSymbol PreparationVacuumWeyl
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open MeasureTheory
open scoped BigOperators ContDiff Topology

def tailJet (B : ℕ → Fin 5 → ArrayBound) (m : ℕ) (w : Word m) : Symbol :=
  listJet (List.ofFn (slotDirection∘w)) (energyTailFor B)

theorem tailJet_actual (B : ℕ → Fin 5 → ArrayBound) (m : ℕ) (w : Word m) (x : Phase) :
    tailJet B m w x=jet m (energyTailFor B) w x := by
  exact listJet_ofFn isOpen_univ (energyTailFor_global_smooth B).contDiffOn m _ x (Set.mem_univ x)

theorem tailJet_global_smooth (B : ℕ → Fin 5 → ArrayBound) (m : ℕ) (w : Word m) :
    ContDiff ℝ ∞ (tailJet B m w) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact listJet_smooth _ (energyTailFor_global_smooth B).contDiffAt

theorem tailJet_position_zero (B : ℕ → Fin 5 → ArrayBound) (m : ℕ) (w : Word m) (x : Phase)
    (outside : x.1∉thetaPositionClosed) : tailJet B m w x=0 := by
  have germ:=energyTailFor_position_germ B x outside
  have read:=congrArg (fun D=>D (slotDirection∘w)) ((germ.iteratedFDeriv ℝ m).eq_of_nhds)
  rw [tailJet_actual]
  change iteratedFDeriv ℝ m (energyTailFor B) x (slotDirection∘w)=0
  rw [read]
  cases m <;> simp

def positionJet (B : ℕ → Fin 5 → ArrayBound) (m : ℕ) (w : Word m) (p : PhysicalMomentum) :
    FlatConfiguration → ℝ := fun z=>tailJet B m w (z,p)

theorem positionJet_smooth (B : ℕ → Fin 5 → ArrayBound) (m : ℕ) (w : Word m) (p : PhysicalMomentum) :
    ContDiff ℝ ∞ (positionJet B m w p) :=
  (tailJet_global_smooth B m w).comp (contDiff_id.prodMk contDiff_const)

theorem positionJet_support (B : ℕ → Fin 5 → ArrayBound) (m : ℕ) (w : Word m) (p : PhysicalMomentum) :
    tsupport (positionJet B m w p)⊆thetaPositionClosed := by
  apply closure_minimal _ thetaPositionClosed_closed
  intro z nonzero
  by_contra outside
  exact nonzero (tailJet_position_zero B m w (z,p) outside)

theorem positionJet_compact (B : ℕ → Fin 5 → ArrayBound) (m : ℕ) (w : Word m) (p : PhysicalMomentum) :
    HasCompactSupport (positionJet B m w p) :=
  thetaPositionClosed_compact.of_isClosed_subset isClosed_closure (positionJet_support B m w p)

theorem positionJet_integrable (B : ℕ → Fin 5 → ArrayBound) (m : ℕ) (w : Word m) (p : PhysicalMomentum) :
    Integrable (positionJet B m w p) flatMeasure := by
  rw [←raw100_volume]
  exact (positionJet_smooth B m w p).continuous.integrable_of_hasCompactSupport (positionJet_compact B m w p)

end LowEnergy.PreparationVacuumTailSupport
