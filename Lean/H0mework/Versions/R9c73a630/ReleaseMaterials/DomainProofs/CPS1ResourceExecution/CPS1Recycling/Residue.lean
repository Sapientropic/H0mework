import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1InitiationTermination.NativeComplete

set_option autoImplicit false

namespace CPS1Recycling.ResidueSplit
open CPS1ResourceExecution
open CPS1InitiationTermination.NativeComplete

/-- These factors are already returned by the source-native translation occurrence. -/
def nextActors : Stock := factorStock [.metRS,.eIF1,.eIF1A,.eIF2,.eIF3]

def returnedInitiator : List AA → Stock
  | [] => []
  | _ :: _ => [.initiatorTRNA]

def remainingElongationWaste : List AA → Stock
  | [] => []
  | aa :: rest => CPS1EndogenousTranslation.elongationWaste (.M,[aa]) rest ++
      [.gdp,.phosphate,.proton,.gdp,.phosphate,.proton]

/-- No product is discarded: the peptide, previous-cycle tRNAs, currencies and other factors stay. -/
def remainder (tail : List AA) : Stock :=
  [.releasedPeptide (.M,tail)] ++ remainingElongationWaste tail ++ terminationWaste ++
    loadingWaste ++ chargingWaste tail ++ [.amp,.ppi] ++ factorStock [.eIF5,.eIF5B]

theorem final_products_recycling_partition (tail : List AA) :
    (finalProducts tail).Perm
      (terminalComplex tail :: nextActors ++ returnedInitiator tail ++ remainder tail) := by
  cases tail with
  | nil =>
      apply List.perm_iff_count.mpr
      intro species
      simp only [finalProducts,elongationWasteWithInitiator,returnedInitiator,
        remainder,remainingElongationWaste,nextActors,passiveActors,factorStock,
        List.map_cons,List.map_nil,List.count_cons,List.count_append,List.count_nil]
      omega
  | cons aa rest =>
      apply List.perm_iff_count.mpr
      intro species
      simp only [finalProducts,elongationWasteWithInitiator,firstCycleWaste,
        returnedInitiator,remainder,remainingElongationWaste,nextActors,passiveActors,
        factorStock,List.map_cons,List.map_nil,List.count_cons,List.count_append,List.count_nil]
      omega

theorem native_elongation_waste_has_no_initiator (chain : Peptide) (tail : List AA) :
    (CPS1EndogenousTranslation.elongationWaste chain tail).count .initiatorTRNA = 0 := by
  induction tail generalizing chain with
  | nil => rfl
  | cons aa rest inductionHypothesis =>
      change ((CPS1EndogenousTranslation.elongationWaste (Peptide.extend chain aa) rest) ++
        CPS1EndogenousTranslation.cycleWaste chain).count .initiatorTRNA = 0
      rw [List.count_append,inductionHypothesis]
      simp [CPS1EndogenousTranslation.cycleWaste]

theorem charging_waste_has_no_initiator (tail : List AA) :
    (chargingWaste tail).count .initiatorTRNA = 0 := by
  induction tail with
  | nil => rfl
  | cons aa rest inductionHypothesis =>
      simp [chargingWaste,List.flatMap_cons] at inductionHypothesis ⊢
      exact inductionHypothesis

theorem remainder_has_no_initiator (tail : List AA) :
    (remainder tail).count .initiatorTRNA = 0 := by
  have charged := charging_waste_has_no_initiator tail
  cases tail with
  | nil =>
      simp [remainder,remainingElongationWaste,terminationWaste,loadingWaste,factorStock,charged]
  | cons aa rest =>
      simp [remainder,remainingElongationWaste,terminationWaste,loadingWaste,factorStock,
        native_elongation_waste_has_no_initiator,charged]

theorem source_free_initiator_count (tail : List AA) :
    (finalProducts tail).count .initiatorTRNA = if tail = [] then 0 else 1 := by
  have partition := (final_products_recycling_partition tail).count_eq .initiatorTRNA
  cases tail with
  | nil =>
      simpa [terminalComplex,nextActors,returnedInitiator,remainder_has_no_initiator,factorStock] using partition
  | cons aa rest =>
      simpa [terminalComplex,nextActors,returnedInitiator,remainder_has_no_initiator,factorStock] using partition

/-- The deacyl tRNA released from the actual source postTC keeps its fine role. -/
def postReleasedTrna : List AA → Stock
  | [] => [.initiatorTRNA]
  | aa :: rest => [.tRNA (Peptide.last (.M,aa :: rest))]

def remainingReturnedTrna : List AA → Stock
  | [] => []
  | aa :: rest => [.tRNA (Peptide.last (.M,aa :: rest))]

/-- The source has exactly one free initiator after removal for both singleton and longer chains. -/
theorem post_removal_initiator_partition (tail : List AA) :
    (returnedInitiator tail ++ postReleasedTrna tail).Perm
      (.initiatorTRNA :: remainingReturnedTrna tail) := by
  cases tail <;> exact List.Perm.refl _

theorem post_removal_initiator_count (tail : List AA) :
    (returnedInitiator tail ++ postReleasedTrna tail ++ remainder tail).count .initiatorTRNA = 1 := by
  have partition := (post_removal_initiator_partition tail).append_right (remainder tail)
  have counted := partition.count_eq .initiatorTRNA
  cases tail <;> simpa [remainingReturnedTrna,remainder_has_no_initiator] using counted

end CPS1Recycling.ResidueSplit
