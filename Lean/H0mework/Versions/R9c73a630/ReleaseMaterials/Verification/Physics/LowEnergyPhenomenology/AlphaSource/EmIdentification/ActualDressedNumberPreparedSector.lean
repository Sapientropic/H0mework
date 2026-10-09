import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNumberOrderedTime

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNumberSector
open SaturationMonoid.PhysicsCore
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumScalarChart
open SourceQuantumGaugeSliceCoordinates GaussCoreHilbert GaussCoreDifferential GaussCoreLabel GaussHistoryHilbert
open GaussFockLabel GaussFockPair GaussQuantumMultiplier NativeHistoryGrade
open SourceFockRaising SourceGradeTransport SourceQuantumFockGrade56
open CanonicalCompletedSector CanonicalPreparationCore CanonicalPreparationCreation
open PreparationVacuumPreparedCurrent PreparationVacuumSourcePreparedResponse
open ActualDressedSourcePreparation
open GaussComposite.SourceGraph
open GaussDensityCore PreparationVacuumLocalizedYukawa
open scoped BigOperators Topology
attribute [local instance] SourceRealScalarFock.branchOrder
local instance occupationModeEq : DecidableEq Mode :=
  @LinearOrder.toDecidableEq Mode SourceQuantumFockGauge.modeOrder

def numberTwoProjection : H→L[ℂ]H:=numberTwoGrade 0+numberTwoGrade 1+numberTwoGrade 2

private theorem count_below_word {ι : Type*} [Fintype ι] [LinearOrder ι] (s word : Finset ι) :
    SourceGradeTransport.count s word≤word.card := by
  unfold SourceGradeTransport.count
  exact Finset.card_filter_le _ _

private theorem two_slot_resolution {V : Type*} [AddCommMonoid V]
    (x : Occupation→V) (supported : ∀word : Occupation,word.card≠2→x word=0) (word : Occupation) :
    (∑g : Fin 3,if NativeHistoryGrade.sourceLabel word=(2,g.castLE (by decide)) then x word else 0)=x word := by
  by_cases number : word.card=2
  · have hn : (NativeHistoryGrade.sourceLabel word).1=(2:Fin 505):=Fin.ext number
    have hg : (NativeHistoryGrade.sourceLabel word).2.val≤2 := by
      rw [←number]
      exact @count_below_word Mode inferInstance SourceQuantumFockGauge.modeOrder target word
    have cases : (NativeHistoryGrade.sourceLabel word).2=(0:Fin 57) ∨
        (NativeHistoryGrade.sourceLabel word).2=(1:Fin 57) ∨
        (NativeHistoryGrade.sourceLabel word).2=(2:Fin 57) := by
      have values : (NativeHistoryGrade.sourceLabel word).2.val=0 ∨
          (NativeHistoryGrade.sourceLabel word).2.val=1 ∨ (NativeHistoryGrade.sourceLabel word).2.val=2 := by omega
      exact values.elim (fun h=>Or.inl (Fin.ext h))
        (fun h=>h.elim (fun h=>Or.inr (Or.inl (Fin.ext h))) (fun h=>Or.inr (Or.inr (Fin.ext h))))
    rcases cases with h|h|h
    · have label : NativeHistoryGrade.sourceLabel word=(2,0):=Prod.ext hn h
      simp [Fin.sum_univ_three,label]
    · have label : NativeHistoryGrade.sourceLabel word=(2,1):=Prod.ext hn h
      simp [Fin.sum_univ_three,label]
    · have label : NativeHistoryGrade.sourceLabel word=(2,2):=Prod.ext hn h
      simp [Fin.sum_univ_three,label]
  · simp only [supported word number,ite_self,Finset.sum_const_zero]

private theorem seed_one_supported (word : Occupation) (different : word.card≠1) :
    CanonicalCompletedSector.seed word=0 := seed_zero_off_one word different

private theorem created_seed_two_supported (i : Mode) (word : Occupation) (different : word.card≠2) :
    GaussCARHistory.createFiber i CanonicalCompletedSector.seed word=0 := by
  change SourceCARBound.createOp i CanonicalCompletedSector.seed word=0
  have original:=congrFun (SourceCARBound.coordinates_liftOp (LowEnergy.Fermion.creation i) CanonicalCompletedSector.seed) word
  change SourceCARBound.createOp i CanonicalCompletedSector.seed word=
    QuantizationCheck.Fermion.create i (fiberCoordinates CanonicalCompletedSector.seed) word at original
  rw [original]
  by_cases inside : i∈word
  · rw [QuantizationCheck.Fermion.create,if_pos inside]
    have lower : (word.erase i).card≠1 := by
      have count:=Finset.card_erase_of_mem inside
      have positive:=Finset.card_pos.mpr ⟨i,inside⟩
      omega
    have zero : fiberCoordinates CanonicalCompletedSector.seed (word.erase i)=0 := by
      simpa only [fiberCoordinates] using! seed_one_supported (word.erase i) lower
    simpa only [mul_zero] using! congrArg (fun z : ℂ=>QuantizationCheck.Fermion.sign i (word.erase i)*z) zero
  · simp only [QuantizationCheck.Fermion.create,if_neg inside]

private theorem creation_fiber_two (a s : Fin 2) (phi : Scalar) (word : Occupation) (different : word.card≠2) :
    fiberCreation a s phi CanonicalCompletedSector.seed word=0 := by
  simp only [fiberCreation,sum_apply,smul_apply,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply]
  apply Finset.sum_eq_zero
  intro c _
  rw [created_seed_two_supported _ word different,smul_zero]

/-- The original scalar field, root-volume factor and canonical N1 seed positively generate N2 support on every source test. -/
theorem source_creation_test_N2 (f : ScalarTest) :
    numberTwoProjection (leg true 1 0 (preparedCore f))=leg true 1 0 (preparedCore f) := by
  rw [←legTest_embed]
  have source : legTest true 1 0 (preparedCore f)=creationTest 1 0 (preparedCore f) := rfl
  rw [source]
  have test_support (z : SourceCoordinateSlice) (word : Occupation) (different : word.card≠2) :
      creationTest 1 0 (preparedCore f) z word=0 := by
    change (((rootVolume z:ℂ)⁻¹) • fiberCreation 1 0 (GaussNativePotential.scalarField z)
      ((CanonicalPreparationCore.numberRaise z*(PreparationVacuumWeylDomain.sourceVacuumInputCore f z)) • CanonicalCompletedSector.seed)) word=0
    rw [map_smul]
    simp only [PiLp.smul_apply,creation_fiber_two 1 0 _ word different,smul_zero]
  have fixed : ∑ g : Fin 3,GaussCoreLabel.project (2,g.castLE (by decide)) (creationTest 1 0 (preparedCore f))=
      creationTest 1 0 (preparedCore f) := by
    apply DFunLike.ext
    intro z
    apply PiLp.ext
    intro word
    have hs : ∀v : Occupation,v.card≠2→creationTest 1 0 (preparedCore f) z v=0:=test_support z
    simp only [Fin.sum_univ_three]
    change (fiberPiece (2,0) (creationTest 1 0 (preparedCore f) z)+
      fiberPiece (2,1) (creationTest 1 0 (preparedCore f) z)+
      fiberPiece (2,2) (creationTest 1 0 (preparedCore f) z)) word=_
    simp only [WithLp.ofLp_add,Pi.add_apply,GaussCoreLabel.fiberPiece_apply]
    simpa only [Fin.sum_univ_three] using!
      two_slot_resolution (fun v : Occupation=>creationTest 1 0 (preparedCore f) z v) hs word
  have embedded:=congrArg embed fixed
  simpa only [Fin.sum_univ_three,map_add,numberTwoProjection,numberTwoGrade,add_apply,
    ←GaussCoreLabel.embed_project] using! embedded

end LowEnergy.GaussComposite.ActualDressedNumberSector
