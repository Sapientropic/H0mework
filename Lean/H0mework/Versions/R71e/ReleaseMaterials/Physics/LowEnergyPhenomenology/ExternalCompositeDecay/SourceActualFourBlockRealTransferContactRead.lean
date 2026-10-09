import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRealTransferContactRows0
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRealTransferContactRows1
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRealTransferContactRows2
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRealTransferContactRows3
set_option autoImplicit false
noncomputable section
namespace LowEnergy.ActualFourBlockRealTransfer

theorem actual_contact_read (q : Fin 4 → ℂ) (a b : Fin 97) :
    MixedSpectatorContactExchange.contactCoefficient q a b = contactRead q a b := by
  fin_cases a
  · exact actual_contact_read_row0 q b
  · exact actual_contact_read_row1 q b
  · exact actual_contact_read_row2 q b
  · exact actual_contact_read_row3 q b
  · exact actual_contact_read_row4 q b
  · exact actual_contact_read_row5 q b
  · exact actual_contact_read_row6 q b
  · exact actual_contact_read_row7 q b
  · exact actual_contact_read_row8 q b
  · exact actual_contact_read_row9 q b
  · exact actual_contact_read_row10 q b
  · exact actual_contact_read_row11 q b
  · exact actual_contact_read_row12 q b
  · exact actual_contact_read_row13 q b
  · exact actual_contact_read_row14 q b
  · exact actual_contact_read_row15 q b
  · exact actual_contact_read_row16 q b
  · exact actual_contact_read_row17 q b
  · exact actual_contact_read_row18 q b
  · exact actual_contact_read_row19 q b
  · exact actual_contact_read_row20 q b
  · exact actual_contact_read_row21 q b
  · exact actual_contact_read_row22 q b
  · exact actual_contact_read_row23 q b
  · exact actual_contact_read_row24 q b
  · exact actual_contact_read_row25 q b
  · exact actual_contact_read_row26 q b
  · exact actual_contact_read_row27 q b
  · exact actual_contact_read_row28 q b
  · exact actual_contact_read_row29 q b
  · exact actual_contact_read_row30 q b
  · exact actual_contact_read_row31 q b
  · exact actual_contact_read_row32 q b
  · exact actual_contact_read_row33 q b
  · exact actual_contact_read_row34 q b
  · exact actual_contact_read_row35 q b
  · exact actual_contact_read_row36 q b
  · exact actual_contact_read_row37 q b
  · exact actual_contact_read_row38 q b
  · exact actual_contact_read_row39 q b
  · exact actual_contact_read_row40 q b
  · exact actual_contact_read_row41 q b
  · exact actual_contact_read_row42 q b
  · exact actual_contact_read_row43 q b
  · exact actual_contact_read_row44 q b
  · exact actual_contact_read_row45 q b
  · exact actual_contact_read_row46 q b
  · exact actual_contact_read_row47 q b
  · exact actual_contact_read_row48 q b
  · exact actual_contact_read_row49 q b
  · exact actual_contact_read_row50 q b
  · exact actual_contact_read_row51 q b
  · exact actual_contact_read_row52 q b
  · exact actual_contact_read_row53 q b
  · exact actual_contact_read_row54 q b
  · exact actual_contact_read_row55 q b
  · exact actual_contact_read_row56 q b
  · exact actual_contact_read_row57 q b
  · exact actual_contact_read_row58 q b
  · exact actual_contact_read_row59 q b
  · exact actual_contact_read_row60 q b
  · exact actual_contact_read_row61 q b
  · exact actual_contact_read_row62 q b
  · exact actual_contact_read_row63 q b
  · exact actual_contact_read_row64 q b
  · exact actual_contact_read_row65 q b
  · exact actual_contact_read_row66 q b
  · exact actual_contact_read_row67 q b
  · exact actual_contact_read_row68 q b
  · exact actual_contact_read_row69 q b
  · exact actual_contact_read_row70 q b
  · exact actual_contact_read_row71 q b
  · exact actual_contact_read_row72 q b
  · exact actual_contact_read_row73 q b
  · exact actual_contact_read_row74 q b
  · exact actual_contact_read_row75 q b
  · exact actual_contact_read_row76 q b
  · exact actual_contact_read_row77 q b
  · exact actual_contact_read_row78 q b
  · exact actual_contact_read_row79 q b
  · exact actual_contact_read_row80 q b
  · exact actual_contact_read_row81 q b
  · exact actual_contact_read_row82 q b
  · exact actual_contact_read_row83 q b
  · exact actual_contact_read_row84 q b
  · exact actual_contact_read_row85 q b
  · exact actual_contact_read_row86 q b
  · exact actual_contact_read_row87 q b
  · exact actual_contact_read_row88 q b
  · exact actual_contact_read_row89 q b
  · exact actual_contact_read_row90 q b
  · exact actual_contact_read_row91 q b
  · exact actual_contact_read_row92 q b
  · exact actual_contact_read_row93 q b
  · exact actual_contact_read_row94 q b
  · exact actual_contact_read_row95 q b
  · exact actual_contact_read_row96 q b

end LowEnergy.ActualFourBlockRealTransfer
