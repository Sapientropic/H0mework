import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceMomentumContinuation

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.PreparationVacuumFullPoleContinuation
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumGradedTransport
open PreparationVacuumYukawaTransport PreparationVacuumPhysicalHalfAxis
open PreparationVacuumSharedPoleCarrier PreparationVacuumJointFieldResponse
open PreparationVacuumRawJointFeedback PreparationVacuumPhysicalFeedback
open scoped Topology
local instance : NormedAlgebra ℝ (H→L[ℂ] H):=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ (H→L[ℂ] H):=NormedAlgebra.restrictScalars ℚ ℂ _

attribute [local irreducible] CanonicalPhysicalSpatial.physicalAction actualC actualA jointGenerator jointResolvent physicalTime

theorem sourcePhysicalSpan_momentum (p k : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    physicalSpan p F=physicalSpan k F:=by
  change Submodule.span ℂ ((fun x : Core=>(x:H)) '' ((show Finset Core from F):Set Core))=
    Submodule.span ℂ ((fun x : Core=>(x:H)) '' ((show Finset Core from F):Set Core))
  rfl


private theorem basisSupport_congr (P Q : Submodule ℂ H) [FiniteDimensional ℂ P] [FiniteDimensional ℂ Q]
    (hP : P≤Core) (hQ : Q≤Core) (same : P=Q) :
    (⋃i : Fin (Module.finrank ℂ P),tsupport (coreEquiv.symm
      ⟨((stdOrthonormalBasis ℂ P i:P):H),hP (stdOrthonormalBasis ℂ P i).property⟩))=
    (⋃i : Fin (Module.finrank ℂ Q),tsupport (coreEquiv.symm
      ⟨((stdOrthonormalBasis ℂ Q i:Q):H),hQ (stdOrthonormalBasis ℂ Q i).property⟩)):=by
  subst Q
  rfl

theorem sourceFiniteSet_momentum (p k : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    finiteSourceSet p F=finiteSourceSet k F:=by
  let : FiniteDimensional ℂ (physicalSpan p F):=FiniteCoreEvolution.coreSpan_finite (CanonicalPhysicalSpatial.physical p) F
  let : FiniteDimensional ℂ (physicalSpan k F):=FiniteCoreEvolution.coreSpan_finite (CanonicalPhysicalSpatial.physical k) F
  exact congrArg (fun S=>tsupport PreparationChartGuard.actualNativeLocalizer∪S)
    (basisSupport_congr (physicalSpan p F) (physicalSpan k F)
      (FiniteCoreEvolution.coreSpan_le (CanonicalPhysicalSpatial.physical p) F)
      (FiniteCoreEvolution.coreSpan_le (CanonicalPhysicalSpatial.physical k) F)
      (sourcePhysicalSpan_momentum p k F))

theorem sourceRetainer_momentum (p k : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    finiteRetainer p F=finiteRetainer k F:=by
  unfold finiteRetainer
  simp only [sourceFiniteSet_momentum p k F]

theorem actualA_momentum (p k : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    actualA p F=actualA k F:=by
  unfold actualA
  rw [sourceRetainer_momentum p k F]

theorem actualJointGenerator_momentum (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z : ℂ) :
    jointGenerator p F z 0=actualC p F+actualA 0 F-z • 1:=by
  have zero : (0:ℂ) • (1:H→L[ℂ] H)=0:=by
    apply ContinuousLinearMap.ext
    intro x
    exact zero_smul ℂ x
  calc
    _=jointGenerator p F 0 0-z • 1:=by simp only [jointGenerator,zero,sub_zero]
    _= _:=congrArg (fun A : H→L[ℂ] H=>A-z • 1)
      ((actualGenerator_source p F).trans
        (congrArg (fun A : H→L[ℂ] H=>actualC p F+A) (actualA_momentum p 0 F)))

theorem actualJointGenerator_continuous (F : GaussUnitaryHistory.Index) (z : ℂ) :
    Continuous (fun p : PhysicalMomentum=>jointGenerator p F z 0):=by
  simp only [actualJointGenerator_momentum]
  exact ((actualC_continuous F).add continuous_const).sub continuous_const

theorem actualJointResolvent_continuous (F : GaussUnitaryHistory.Index) (z : ℂ) (nonreal : z.im≠0) :
    Continuous (fun p : PhysicalMomentum=>jointResolvent p F z 0):=by
  unfold jointResolvent
  apply continuous_iff_continuousAt.mpr
  intro p
  have inverse : ContinuousAt Ring.inverse (jointGenerator p F z 0):=by
    obtain ⟨u,hu⟩:=jointGenerator_unit p F z nonreal
    rw [←hu]
    exact NormedRing.inverse_continuousAt u
  exact inverse.tendsto.comp (actualJointGenerator_continuous F z).continuousAt.tendsto

theorem actualJointTime_continuous (F : GaussUnitaryHistory.Index) :
    Continuous (fun pt : PhysicalMomentum×ℝ=>physicalTime pt.1 F pt.2 0):=by
  unfold physicalTime SourceFiniteUnitary.time
  exact NormedSpace.exp_continuous.comp (continuous_snd.smul
    ((actualJointGenerator_continuous F 0).comp continuous_fst |>.const_smul (-Complex.I)))

theorem actualJointTime_source_price (F : GaussUnitaryHistory.Index) (p : PhysicalMomentum) (t : ℝ) :
    ‖physicalTime p F t 0‖≤actualGrowth 0 F |t|:=by
  have bound:=actual_time_bound p F t
  simpa only [actualGrowth,actualA_momentum p 0 F] using bound

end LowEnergy.PreparationVacuumFullPoleContinuation
