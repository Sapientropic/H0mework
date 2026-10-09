import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Normalized
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Geometry

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1ElectronicSource
noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace

def spatialValue (centre : Point) (n : Nat) (i : Fin n)
    (jet : Fin 3 → Nat) (x : Point) : ℂ :=
  ∑ j : Fin n, coefficients centre n j i * orbitalValue centre j.val jet x

theorem spatial_memLp (centre : Point) (n : Nat) (i : Fin n) (jet : Fin 3 → Nat) :
    MemLp (spatialValue centre n i jet) 2 (volume : Measure Point) := by
  apply memLp_finsetSum
  intro j _
  exact (orbital_memLp centre j.val jet).const_mul (coefficients centre n j i)

def spatialField (centre : Point) (n : Nat) (i : Fin n) (jet : Fin 3 → Nat) : SpatialLp :=
  (spatial_memLp centre n i jet).toLp (spatialValue centre n i jet)

theorem spatial_continuous (centre : Point) (n : Nat) (i : Fin n) (jet : Fin 3 → Nat) :
    Continuous (spatialValue centre n i jet) := by
  apply continuous_finsetSum
  intro j _
  exact continuous_const.mul (orbital_continuous centre j.val jet)

variable {frame : CPS1Recycling.Frame}

abbrev SpatialIndex (geometry : Geometry frame) := Fin (spatialModes frame geometry.originJoint)
abbrev SpinIndex (geometry : Geometry frame) := SpatialIndex geometry × Bool
abbrev ElectronIndex (geometry : Geometry frame) := Fin (electronCount frame geometry.originJoint)

def basis (geometry : Geometry frame) (index : SpinIndex geometry) : SpinSpace :=
  PiLp.single 2 index.2 (normalizedField 0 (spatialModes frame geometry.originJoint) index.1)

def basisValue (geometry : Geometry frame) (index : SpinIndex geometry) (jet : Fin 3 → Nat)
    (spin : Bool) (x : Point) : ℂ :=
  if spin = index.2 then spatialValue 0 (spatialModes frame geometry.originJoint) index.1 jet x else 0

def occupiedIndex (geometry : Geometry frame) (slot : ElectronIndex geometry) : SpinIndex geometry :=
  (⟨slot.val/2,by unfold spatialModes; omega⟩,decide (slot.val%2=1))

def occupation (geometry : Geometry frame) : Matrix (SpinIndex geometry) (ElectronIndex geometry) ℂ :=
  fun index slot => if index = occupiedIndex geometry slot then 1 else 0

theorem spatial_field_normalized (centre : Point) (n : Nat) (i : Fin n) :
    spatialField centre n i 0 = normalizedField centre n i := by
  rw [normalized_synthesis]
  apply Lp.ext
  have each (j : Fin n) :
      (fun x : Point => (coefficients centre n j i • rawFields centre n j) x) =ᵐ[volume]
        fun x => coefficients centre n j i * orbitalValue centre j.val 0 x := by
    filter_upwards [Lp.coeFn_smul (coefficients centre n j i) (rawFields centre n j),
      orbital_field_source centre j.val 0] with x scalar source
    simpa only [rawFields,Pi.smul_apply,smul_eq_mul,source] using scalar
  filter_upwards [(spatial_memLp centre n i 0).coeFn_toLp,
    Lp.coeFn_fun_finsetSum Finset.univ (fun j => coefficients centre n j i • rawFields centre n j),
    Filter.eventually_all.mpr each] with x source summed scalar
  have rhs : (∑ j : Fin n, coefficients centre n j i • rawFields centre n j) x =
      spatialValue centre n i 0 x :=
    summed.trans (Finset.sum_congr rfl (fun j _ => scalar j))
  exact source.trans rhs.symm


end
end CPS1ElectronicSource
