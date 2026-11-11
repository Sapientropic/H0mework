import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.VolterraMoments
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerMaterialConsumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.PaPowerWholeSource
open Complex MeasureTheory Set
open CenteredGram.IntegralGraphJointAction
open OriginalRieszFinitePairing.CoPoisson.Ward
open scoped InnerProductSpace BigOperators
namespace Port
export OriginalKCrossParameterRAdjointSource.PaNativePortSource
  (Pa sourceMap correction loop port actual_original_R actual_source_loop)
export OriginalKCrossParameterRAdjointSource.PaNativePortMoments (actual_port_log_moment)
end Port
namespace Unit
export OriginalKFiniteOrderRelease.UnitPowerSource (unitPower)
end Unit
namespace Native
export OriginalKCombFirstFullSourceDynamics (raw)
export OriginalKCountedPaSource (actualField counted)
export OriginalKFiniteOrderRelease.UnitPowerMaterialConsumer (actual_raw_original_power)
end Native
open private original_power_source from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerMaterialConsumer
open private allPa_fourier_power_zero from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerSource
local notation "R" => burnolDirectRightResolventCLM
local notation "p0" => VolterraMoments.originalPa
local notation "q" => burnolUnscaledCommonGapRadius

private theorem whole_zero_shift (c:BurnolCompletedMellinCoordinate) (p:↥Port.Pa) (k:ℕ) :
    ((R c)^k) (p:BurnolL2)=(Port.loop c k p:BurnolL2)+
      ∑i∈Finset.range k,Port.port c i p •
        ((R c)^(k-1-i)) (burnolUnitTailResponse c 4) := by
  induction k with
  | zero => simp [Port.loop]
  | succ k previous =>
    rw [pow_succ',mul_apply_eq_comp,previous,map_add,map_sum,Port.actual_original_R c k p]
    have moved : (∑i∈Finset.range k,(R c) (Port.port c i p •
        ((R c)^(k-1-i)) (burnolUnitTailResponse c 4)))=
        ∑i∈Finset.range k,Port.port c i p •
          ((R c)^(k-i)) (burnolUnitTailResponse c 4) := by
      apply Finset.sum_congr rfl
      intro i hi
      have index:(k-1-i)+1=k-i := by have inside:=Finset.mem_range.mp hi;omega
      calc
        _=Port.port c i p • (R c) (((R c)^(k-1-i)) (burnolUnitTailResponse c 4)) := by rw [map_smul]
        _=Port.port c i p • ((R c)^((k-1-i)+1)) (burnolUnitTailResponse c 4) := by
          rw [pow_succ',mul_apply_eq_comp]
        _=_ := by rw [index]
    rw [moved,Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel,Nat.sub_self,pow_zero,one_apply_eq_self]
    module

private theorem whole_shifted (c:BurnolCompletedMellinCoordinate) (p:↥Port.Pa) (r k:ℕ) :
    ((R c)^(r+k)) (p:BurnolL2)=((R c)^r) (Port.loop c k p:BurnolL2)+
      ∑i∈Finset.range k,Port.port c i p •
        ((R c)^(r+k-1-i)) (burnolUnitTailResponse c 4) := by
  rw [pow_add,mul_apply_eq_comp,whole_zero_shift c p k,map_add,map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have index:r+(k-1-i)=r+k-1-i := by have inside:=Finset.mem_range.mp hi;omega
  rw [map_smul,←mul_apply_eq_comp,←pow_add,index]

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "FK" => fourierL2 (burnolCompletedMellinRieszVector c:BurnolL2)

def remainingPa : ↥Port.Pa := Port.loop c (m+3) p0

def bulkRaw : BurnolL2 := ((R c)^(m-1)) (remainingPa observation half:BurnolL2)

include nontrivial in
private theorem bulk_physical : bulkRaw observation half∈evenBurnolClosedFace q := by
  have before:m-1<m := by have positive:=generatedRiemannXiZeroOrder_pos observation nontrivial;omega
  exact CombSource.Division.whole_pa_physical observation nontrivial half.down (m-1) before.le
    (remainingPa observation half:BurnolPaAmbientCarrier) (remainingPa observation half).property

def bulkSource : BurnolPaAmbientCarrier := ⟨bulkRaw observation half,bulk_physical observation nontrivial half⟩

/-- Physical and Fourier-low qualification comes from the original exact-m source, before counting. -/
theorem bulk_fourier_zero : inner ℂ FK (bulkSource observation nontrivial half:BurnolL2)=0 := by
  have before:m-1<m := by have positive:=generatedRiemannXiZeroOrder_pos observation nontrivial;omega
  exact allPa_fourier_power_zero observation nontrivial half
    (remainingPa observation half:BurnolPaAmbientCarrier) (remainingPa observation half).property (m-1) before

/-- The finite port inventory reads the existing same-source all-order moment producer. -/
def coefficient (i:Fin (m+3)) : ℂ := Port.port c i p0

theorem coefficient_source (i:Fin (m+3)) :
    coefficient observation half i=(2:ℂ)*(-2:ℂ)^i.val/(i.val.factorial:ℂ)*
      ∫x:ℝ in Icc (1/4:ℝ) 4,(x:ℂ)^(-(c).value)*(Real.log (x/(1/4:ℝ)):ℂ)^i.val*
        Port.sourceMap p0 x :=
  Port.actual_port_log_moment c i.val p0

private theorem original_actual_power (depth:ℕ) :
    Native.raw observation nontrivial half depth m=((R c)^(2*m+2)) (p0:BurnolL2) := by
  have actual:=Native.actual_raw_original_power observation nontrivial half depth 0 m
  rw [Nat.zero_add] at actual
  have raw0:Native.raw observation nontrivial half depth 0=((R c)^(m+2)) (p0:BurnolL2) := by
    rw [OriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial.actual_raw_field,
      OriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial.actual_iterate_power]
    rfl
  calc
    _=((OriginalKCombPhysicalAction.R observation nontrivial half)^m)
        (Native.raw observation nontrivial half depth 0) := actual
    _=((R c)^m) (Native.raw observation nontrivial half depth 0) :=
      original_power_source observation nontrivial half m _
    _=((R c)^m) (((R c)^(m+2)) (p0:BurnolL2)) := by rw [raw0]
    _=_ := by
      rw [←mul_apply_eq_comp,←pow_add,show m+(m+2)=2*m+2 by omega]

/-- The old actual ordinal m is read through its own successor-generated R prefix. -/
theorem actual_raw_whole (depth:ℕ) :
    Native.raw observation nontrivial half depth m=(bulkSource observation nontrivial half:BurnolL2)+
      ∑i∈Finset.range (m+3),Port.port c i p0 • Unit.unitPower observation half (2*m+1-i) := by
  have positive:=generatedRiemannXiZeroOrder_pos observation nontrivial
  have index:(m-1)+(m+3)=2*m+2 := by omega
  have whole:=whole_shifted c p0 (m-1) (m+3)
  rw [index] at whole
  rw [original_actual_power]
  change _=((R c)^(m-1)) (Port.loop c (m+3) p0:BurnolL2)+_
  rw [whole]
  congr 1

/-- The literal same-N adjoint acts on the whole old ordinal, including every unit foot. -/
theorem actual_counted_whole (depth N:ℕ) :
    Native.actualField observation nontrivial half depth m N=
      DualSource.source N (bulkSource observation nontrivial half:BurnolL2)+
      ∑i∈Finset.range (m+3),Port.port c i p0 •
        DualSource.source N (Unit.unitPower observation half (2*m+1-i)) := by
  change DualSource.source N (Native.raw observation nontrivial half depth m)=_
  simpa only [CountingDual.dual_eq_adjoint,map_add,map_sum,map_smul] using
    congrArg ((CountingDual.sourceCLM N).adjoint)
      (actual_raw_whole observation nontrivial half depth)

end CountedPaInitial.PaPowerWholeSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
