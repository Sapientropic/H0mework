import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualBraContactRows0
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualBraContactRows1
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualBraContactRows2
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualBraContactRows3
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.ActualBraContactDualContraction
open ActualCandidateBra ActualContactDualImaginary MixedSpectatorContactExchange MixedSpectatorPairedSourceFrame
open scoped Matrix BigOperators

theorem actual_contact_bra_contraction (dual : Bool) :
    (∑a : Fin 97,∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) a b)*pairPoint dual a b) =
      (-1/25 : ℂ)*(Real.sqrt 30 : ℂ) := by
  have hrow (a : Fin 97) :
      (∑b : Fin 97,((-1/2 : ℂ)*contactCoefficient (worldTransfer Complex.I 0) a b)*pairPoint dual a b) =
        (![contactBraRow0 dual,contactBraRow1 dual,contactBraRow2 dual,contactBraRow3 dual,contactBraRow4 dual,contactBraRow5 dual,contactBraRow6 dual,contactBraRow7 dual,contactBraRow8 dual,contactBraRow9 dual,contactBraRow10 dual,contactBraRow11 dual,contactBraRow12 dual,contactBraRow13 dual,contactBraRow14 dual,contactBraRow15 dual,contactBraRow16 dual,contactBraRow17 dual,contactBraRow18 dual,contactBraRow19 dual,contactBraRow20 dual,contactBraRow21 dual,contactBraRow22 dual,contactBraRow23 dual,contactBraRow24 dual,contactBraRow25 dual,contactBraRow26 dual,contactBraRow27 dual,contactBraRow28 dual,contactBraRow29 dual,contactBraRow30 dual,contactBraRow31 dual,contactBraRow32 dual,contactBraRow33 dual,contactBraRow34 dual,contactBraRow35 dual,contactBraRow36 dual,contactBraRow37 dual,contactBraRow38 dual,contactBraRow39 dual,contactBraRow40 dual,contactBraRow41 dual,contactBraRow42 dual,contactBraRow43 dual,contactBraRow44 dual,contactBraRow45 dual,contactBraRow46 dual,contactBraRow47 dual,contactBraRow48 dual,contactBraRow49 dual,contactBraRow50 dual,contactBraRow51 dual,contactBraRow52 dual,contactBraRow53 dual,contactBraRow54 dual,contactBraRow55 dual,contactBraRow56 dual,contactBraRow57 dual,contactBraRow58 dual,contactBraRow59 dual,contactBraRow60 dual,contactBraRow61 dual,contactBraRow62 dual,contactBraRow63 dual,contactBraRow64 dual,contactBraRow65 dual,contactBraRow66 dual,contactBraRow67 dual,contactBraRow68 dual,contactBraRow69 dual,contactBraRow70 dual,contactBraRow71 dual,contactBraRow72 dual,contactBraRow73 dual,contactBraRow74 dual,contactBraRow75 dual,contactBraRow76 dual,contactBraRow77 dual,contactBraRow78 dual,contactBraRow79 dual,contactBraRow80 dual,contactBraRow81 dual,contactBraRow82 dual,contactBraRow83 dual,contactBraRow84 dual,contactBraRow85 dual,contactBraRow86 dual,contactBraRow87 dual,contactBraRow88 dual,contactBraRow89 dual,contactBraRow90 dual,contactBraRow91 dual,contactBraRow92 dual,contactBraRow93 dual,contactBraRow94 dual,contactBraRow95 dual,contactBraRow96 dual] : Fin 97 → ℂ) a := by
    fin_cases a
    · exact actual_contact_bra_row0 dual
    · exact actual_contact_bra_row1 dual
    · exact actual_contact_bra_row2 dual
    · exact actual_contact_bra_row3 dual
    · exact actual_contact_bra_row4 dual
    · exact actual_contact_bra_row5 dual
    · exact actual_contact_bra_row6 dual
    · exact actual_contact_bra_row7 dual
    · exact actual_contact_bra_row8 dual
    · exact actual_contact_bra_row9 dual
    · exact actual_contact_bra_row10 dual
    · exact actual_contact_bra_row11 dual
    · exact actual_contact_bra_row12 dual
    · exact actual_contact_bra_row13 dual
    · exact actual_contact_bra_row14 dual
    · exact actual_contact_bra_row15 dual
    · exact actual_contact_bra_row16 dual
    · exact actual_contact_bra_row17 dual
    · exact actual_contact_bra_row18 dual
    · exact actual_contact_bra_row19 dual
    · exact actual_contact_bra_row20 dual
    · exact actual_contact_bra_row21 dual
    · exact actual_contact_bra_row22 dual
    · exact actual_contact_bra_row23 dual
    · exact actual_contact_bra_row24 dual
    · exact actual_contact_bra_row25 dual
    · exact actual_contact_bra_row26 dual
    · exact actual_contact_bra_row27 dual
    · exact actual_contact_bra_row28 dual
    · exact actual_contact_bra_row29 dual
    · exact actual_contact_bra_row30 dual
    · exact actual_contact_bra_row31 dual
    · exact actual_contact_bra_row32 dual
    · exact actual_contact_bra_row33 dual
    · exact actual_contact_bra_row34 dual
    · exact actual_contact_bra_row35 dual
    · exact actual_contact_bra_row36 dual
    · exact actual_contact_bra_row37 dual
    · exact actual_contact_bra_row38 dual
    · exact actual_contact_bra_row39 dual
    · exact actual_contact_bra_row40 dual
    · exact actual_contact_bra_row41 dual
    · exact actual_contact_bra_row42 dual
    · exact actual_contact_bra_row43 dual
    · exact actual_contact_bra_row44 dual
    · exact actual_contact_bra_row45 dual
    · exact actual_contact_bra_row46 dual
    · exact actual_contact_bra_row47 dual
    · exact actual_contact_bra_row48 dual
    · exact actual_contact_bra_row49 dual
    · exact actual_contact_bra_row50 dual
    · exact actual_contact_bra_row51 dual
    · exact actual_contact_bra_row52 dual
    · exact actual_contact_bra_row53 dual
    · exact actual_contact_bra_row54 dual
    · exact actual_contact_bra_row55 dual
    · exact actual_contact_bra_row56 dual
    · exact actual_contact_bra_row57 dual
    · exact actual_contact_bra_row58 dual
    · exact actual_contact_bra_row59 dual
    · exact actual_contact_bra_row60 dual
    · exact actual_contact_bra_row61 dual
    · exact actual_contact_bra_row62 dual
    · exact actual_contact_bra_row63 dual
    · exact actual_contact_bra_row64 dual
    · exact actual_contact_bra_row65 dual
    · exact actual_contact_bra_row66 dual
    · exact actual_contact_bra_row67 dual
    · exact actual_contact_bra_row68 dual
    · exact actual_contact_bra_row69 dual
    · exact actual_contact_bra_row70 dual
    · exact actual_contact_bra_row71 dual
    · exact actual_contact_bra_row72 dual
    · exact actual_contact_bra_row73 dual
    · exact actual_contact_bra_row74 dual
    · exact actual_contact_bra_row75 dual
    · exact actual_contact_bra_row76 dual
    · exact actual_contact_bra_row77 dual
    · exact actual_contact_bra_row78 dual
    · exact actual_contact_bra_row79 dual
    · exact actual_contact_bra_row80 dual
    · exact actual_contact_bra_row81 dual
    · exact actual_contact_bra_row82 dual
    · exact actual_contact_bra_row83 dual
    · exact actual_contact_bra_row84 dual
    · exact actual_contact_bra_row85 dual
    · exact actual_contact_bra_row86 dual
    · exact actual_contact_bra_row87 dual
    · exact actual_contact_bra_row88 dual
    · exact actual_contact_bra_row89 dual
    · exact actual_contact_bra_row90 dual
    · exact actual_contact_bra_row91 dual
    · exact actual_contact_bra_row92 dual
    · exact actual_contact_bra_row93 dual
    · exact actual_contact_bra_row94 dual
    · exact actual_contact_bra_row95 dual
    · exact actual_contact_bra_row96 dual
  simp_rw [hrow]
  cases dual <;> norm_num [Fin.sum_univ_succ,contactBraRow0,contactBraRow1,contactBraRow2,contactBraRow3,contactBraRow4,contactBraRow5,contactBraRow6,contactBraRow7,contactBraRow8,contactBraRow9,contactBraRow10,contactBraRow11,contactBraRow12,contactBraRow13,contactBraRow14,contactBraRow15,contactBraRow16,contactBraRow17,contactBraRow18,contactBraRow19,contactBraRow20,contactBraRow21,contactBraRow22,contactBraRow23,contactBraRow24,contactBraRow25,contactBraRow26,contactBraRow27,contactBraRow28,contactBraRow29,contactBraRow30,contactBraRow31,contactBraRow32,contactBraRow33,contactBraRow34,contactBraRow35,contactBraRow36,contactBraRow37,contactBraRow38,contactBraRow39,contactBraRow40,contactBraRow41,contactBraRow42,contactBraRow43,contactBraRow44,contactBraRow45,contactBraRow46,contactBraRow47,contactBraRow48,contactBraRow49,contactBraRow50,contactBraRow51,contactBraRow52,contactBraRow53,contactBraRow54,contactBraRow55,contactBraRow56,contactBraRow57,contactBraRow58,contactBraRow59,contactBraRow60,contactBraRow61,contactBraRow62,contactBraRow63,contactBraRow64,contactBraRow65,contactBraRow66,contactBraRow67,contactBraRow68,contactBraRow69,contactBraRow70,contactBraRow71,contactBraRow72,contactBraRow73,contactBraRow74,contactBraRow75,contactBraRow76,contactBraRow77,contactBraRow78,contactBraRow79,contactBraRow80,contactBraRow81,contactBraRow82,contactBraRow83,contactBraRow84,contactBraRow85,contactBraRow86,contactBraRow87,contactBraRow88,contactBraRow89,contactBraRow90,contactBraRow91,contactBraRow92,contactBraRow93,contactBraRow94,contactBraRow95,contactBraRow96]
  all_goals ring

end LowEnergy.ActualBraContactDualContraction
