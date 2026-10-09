import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B005
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B006

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v129_pa : Scalar.QComplex := ((999971759572535932747778704772 : Int)/10^30,(7515321510513781818124254424 : Int)/10^30)
theorem v129_pa_checked : Scalar.distance (sourceCoefficient 1 34 1 0) v129_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v129_pb : Scalar.QComplex := ((3242656331249382506453410 : Int)/10^30,(-431460550651384224501639483 : Int)/10^30)
theorem v129_pb_checked : Scalar.distance (sourceCoefficient 1 34 1 1) v129_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v129_pg : Scalar.QComplex := ((-93083284914979258784040 : Int)/10^30,(-699570569562752377227 : Int)/10^30)
theorem v129_pg_checked : Scalar.distance (sourceCoefficient 1 34 1 2) v129_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v129_mb : Scalar.QComplex := ((2870324100909930952136804 : Int)/10^30,(-431463188265272544160984239 : Int)/10^30)
theorem v129_mb_checked : Scalar.distance (sourceCoefficient 1 34 3 1) v129_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v129_mg : Scalar.QComplex := ((-93083853953712212474199 : Int)/10^30,(-619243626514556777263 : Int)/10^30)
theorem v129_mg_checked : Scalar.distance (sourceCoefficient 1 34 3 2) v129_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v129_upper : Scalar.QComplex := ((999983240995207488959443746138 : Int)/10^30,(5789449777032394786199830908 : Int)/10^30)
theorem v129_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 34 5) 1) 14) v129_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material129 : Material (1 : Basis) (34 : Basis) where
  plus := ![v129_pa,v129_pb,v129_pg]
  minus := ![(Primitive.Addresses.material129 1).one,v129_mb,v129_mg]
  upper := v129_upper
  lower := (Primitive.Addresses.material129 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v129_pa_checked.trans (by decide +kernel)
    · exact v129_pb_checked.trans (by decide +kernel)
    · exact v129_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 34 Primitive.Addresses.material129
    · exact v129_mb_checked.trans (by decide +kernel)
    · exact v129_mg_checked.trans (by decide +kernel)
  upper_error := v129_upper_checked
  lower_error := reuse_lower_error 1 34 Primitive.Addresses.material129

def v130_pa : Scalar.QComplex := ((999972144256265881976174293009 : Int)/10^30,(7463960847015280719683825100 : Int)/10^30)
theorem v130_pa_checked : Scalar.distance (sourceCoefficient 1 35 1 0) v130_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v130_pb : Scalar.QComplex := ((3220495154068820574508064 : Int)/10^30,(-431460656183492817182759134 : Int)/10^30)
theorem v130_pb_checked : Scalar.distance (sourceCoefficient 1 35 1 1) v130_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v130_pg : Scalar.QComplex := ((-93083314203065974827084 : Int)/10^30,(-694789566602222233928 : Int)/10^30)
theorem v130_pg_checked : Scalar.distance (sourceCoefficient 1 35 1 2) v130_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v130_mb : Scalar.QComplex := ((2848162840911531374593870 : Int)/10^30,(-431463274673244037958982902 : Int)/10^30)
theorem v130_mb_checked : Scalar.distance (sourceCoefficient 1 35 3 1) v130_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v130_mg : Scalar.QComplex := ((-93083879115997796666490 : Int)/10^30,(-614462600059912789313 : Int)/10^30)
theorem v130_mg_checked : Scalar.distance (sourceCoefficient 1 35 3 2) v130_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v130_upper : Scalar.QComplex := ((999983537034518701542634506177 : Int)/10^30,(5738088526100349064432471904 : Int)/10^30)
theorem v130_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 35 5) 1) 14) v130_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material130 : Material (1 : Basis) (35 : Basis) where
  plus := ![v130_pa,v130_pb,v130_pg]
  minus := ![(Primitive.Addresses.material130 1).one,v130_mb,v130_mg]
  upper := v130_upper
  lower := (Primitive.Addresses.material130 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v130_pa_checked.trans (by decide +kernel)
    · exact v130_pb_checked.trans (by decide +kernel)
    · exact v130_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 35 Primitive.Addresses.material130
    · exact v130_mb_checked.trans (by decide +kernel)
    · exact v130_mg_checked.trans (by decide +kernel)
  upper_error := v130_upper_checked
  lower_error := reuse_lower_error 1 35 Primitive.Addresses.material130

def v131_pa : Scalar.QComplex := ((999972264631023283287486252251 : Int)/10^30,(7447816371443454862297532860 : Int)/10^30)
theorem v131_pa_checked : Scalar.distance (sourceCoefficient 1 36 1 0) v131_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v131_pb : Scalar.QComplex := ((3213529111900319267890556 : Int)/10^30,(-431460689042456784185996667 : Int)/10^30)
theorem v131_pb_checked : Scalar.distance (sourceCoefficient 1 36 1 1) v131_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v131_pg : Scalar.QComplex := ((-93083323350165813854730 : Int)/10^30,(-693286728118940805835 : Int)/10^30)
theorem v131_pg_checked : Scalar.distance (sourceCoefficient 1 36 1 2) v131_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v131_mb : Scalar.QComplex := ((2841196772980999940440327 : Int)/10^30,(-431463301520815117544313219 : Int)/10^30)
theorem v131_mb_checked : Scalar.distance (sourceCoefficient 1 36 3 1) v131_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v131_mg : Scalar.QComplex := ((-93083886966212304071640 : Int)/10^30,(-612959754242671620660 : Int)/10^30)
theorem v131_mg_checked : Scalar.distance (sourceCoefficient 1 36 3 2) v131_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v131_upper : Scalar.QComplex := ((999983629545196597204508194714 : Int)/10^30,(5721943866817912145984166530 : Int)/10^30)
theorem v131_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 36 5) 1) 14) v131_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material131 : Material (1 : Basis) (36 : Basis) where
  plus := ![v131_pa,v131_pb,v131_pg]
  minus := ![(Primitive.Addresses.material131 1).one,v131_mb,v131_mg]
  upper := v131_upper
  lower := (Primitive.Addresses.material131 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v131_pa_checked.trans (by decide +kernel)
    · exact v131_pb_checked.trans (by decide +kernel)
    · exact v131_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 36 Primitive.Addresses.material131
    · exact v131_mb_checked.trans (by decide +kernel)
    · exact v131_mg_checked.trans (by decide +kernel)
  upper_error := v131_upper_checked
  lower_error := reuse_lower_error 1 36 Primitive.Addresses.material131

def v132_pa : Scalar.QComplex := ((999972315952929247751174370779 : Int)/10^30,(7440922505646882627335687419 : Int)/10^30)
theorem v132_pa_checked : Scalar.distance (sourceCoefficient 1 37 1 0) v132_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v132_pb : Scalar.QComplex := ((3210554536605449223516527 : Int)/10^30,(-431460703027900999208099271 : Int)/10^30)
theorem v132_pb_checked : Scalar.distance (sourceCoefficient 1 37 1 1) v132_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v132_pg : Scalar.QComplex := ((-93083327247451606892900 : Int)/10^30,(-692644999832835046308 : Int)/10^30)
theorem v132_pg_checked : Scalar.distance (sourceCoefficient 1 37 1 2) v132_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v132_mb : Scalar.QComplex := ((2838222186724891746614287 : Int)/10^30,(-431463312939329615571604462 : Int)/10^30)
theorem v132_mb_checked : Scalar.distance (sourceCoefficient 1 37 3 1) v132_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v132_mg : Scalar.QComplex := ((-93083890309714037432024 : Int)/10^30,(-612318022832328518326 : Int)/10^30)
theorem v132_mg_checked : Scalar.distance (sourceCoefficient 1 37 3 2) v132_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v132_upper : Scalar.QComplex := ((999983668968839165453935891467 : Int)/10^30,(5715049922711989396929101971 : Int)/10^30)
theorem v132_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 37 5) 1) 14) v132_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material132 : Material (1 : Basis) (37 : Basis) where
  plus := ![v132_pa,v132_pb,v132_pg]
  minus := ![(Primitive.Addresses.material132 1).one,v132_mb,v132_mg]
  upper := v132_upper
  lower := (Primitive.Addresses.material132 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v132_pa_checked.trans (by decide +kernel)
    · exact v132_pb_checked.trans (by decide +kernel)
    · exact v132_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 37 Primitive.Addresses.material132
    · exact v132_mb_checked.trans (by decide +kernel)
    · exact v132_mg_checked.trans (by decide +kernel)
  upper_error := v132_upper_checked
  lower_error := reuse_lower_error 1 37 Primitive.Addresses.material132

def v133_pa : Scalar.QComplex := ((999972489062522508109592763514 : Int)/10^30,(7417622132685304855196506373 : Int)/10^30)
theorem v133_pa_checked : Scalar.distance (sourceCoefficient 1 38 1 0) v133_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v133_pb : Scalar.QComplex := ((3200500858064984263936734 : Int)/10^30,(-431460750094502014212509181 : Int)/10^30)
theorem v133_pb_checked : Scalar.distance (sourceCoefficient 1 38 1 1) v133_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v133_pg : Scalar.QComplex := ((-93083340381567211410784 : Int)/10^30,(-690476041441798548727 : Int)/10^30)
theorem v133_pg_checked : Scalar.distance (sourceCoefficient 1 38 1 2) v133_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v133_mb : Scalar.QComplex := ((2828168471311513908527661 : Int)/10^30,(-431463351330041325980850483 : Int)/10^30)
theorem v133_mb_checked : Scalar.distance (sourceCoefficient 1 38 3 1) v133_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v133_mg : Scalar.QComplex := ((-93083901572111346313559 : Int)/10^30,(-610149053914744127932 : Int)/10^30)
theorem v133_mg_checked : Scalar.distance (sourceCoefficient 1 38 3 2) v133_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v133_upper : Scalar.QComplex := ((999983801863844661047866590564 : Int)/10^30,(5691749285682126509230451544 : Int)/10^30)
theorem v133_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 38 5) 1) 14) v133_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material133 : Material (1 : Basis) (38 : Basis) where
  plus := ![v133_pa,v133_pb,v133_pg]
  minus := ![(Primitive.Addresses.material133 1).one,v133_mb,v133_mg]
  upper := v133_upper
  lower := (Primitive.Addresses.material133 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v133_pa_checked.trans (by decide +kernel)
    · exact v133_pb_checked.trans (by decide +kernel)
    · exact v133_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 38 Primitive.Addresses.material133
    · exact v133_mb_checked.trans (by decide +kernel)
    · exact v133_mg_checked.trans (by decide +kernel)
  upper_error := v133_upper_checked
  lower_error := reuse_lower_error 1 38 Primitive.Addresses.material133

def v134_pa : Scalar.QComplex := ((999972589238083681032964771967 : Int)/10^30,(7404105110191852276943788565 : Int)/10^30)
theorem v134_pa_checked : Scalar.distance (sourceCoefficient 1 39 1 0) v134_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v134_pb : Scalar.QComplex := ((3194668514023840836317674 : Int)/10^30,(-431460777255635777405513766 : Int)/10^30)
theorem v134_pb_checked : Scalar.distance (sourceCoefficient 1 39 1 1) v134_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v134_pg : Scalar.QComplex := ((-93083347973910763838170 : Int)/10^30,(-689217784391995547321 : Int)/10^30)
theorem v134_pg_checked : Scalar.distance (sourceCoefficient 1 39 1 2) v134_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v134_mb : Scalar.QComplex := ((2822336106003183573135276 : Int)/10^30,(-431463373458114747360161215 : Int)/10^30)
theorem v134_mb_checked : Scalar.distance (sourceCoefficient 1 39 3 1) v134_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v134_mg : Scalar.QComplex := ((-93083908078632907578305 : Int)/10^30,(-608890790781597192071 : Int)/10^30)
theorem v134_mg_checked : Scalar.distance (sourceCoefficient 1 39 3 2) v134_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v134_upper : Scalar.QComplex := ((999983878710102065242799466534 : Int)/10^30,(5678232110426760385428359213 : Int)/10^30)
theorem v134_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 39 5) 1) 14) v134_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material134 : Material (1 : Basis) (39 : Basis) where
  plus := ![v134_pa,v134_pb,v134_pg]
  minus := ![(Primitive.Addresses.material134 1).one,v134_mb,v134_mg]
  upper := v134_upper
  lower := (Primitive.Addresses.material134 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v134_pa_checked.trans (by decide +kernel)
    · exact v134_pb_checked.trans (by decide +kernel)
    · exact v134_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 39 Primitive.Addresses.material134
    · exact v134_mb_checked.trans (by decide +kernel)
    · exact v134_mg_checked.trans (by decide +kernel)
  upper_error := v134_upper_checked
  lower_error := reuse_lower_error 1 39 Primitive.Addresses.material134

def v135_pa : Scalar.QComplex := ((999972757315661025707686155554 : Int)/10^30,(7381370232829307934911005344 : Int)/10^30)
theorem v135_pa_checked : Scalar.distance (sourceCoefficient 1 40 1 0) v135_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v135_pb : Scalar.QComplex := ((3184858837428947253219397 : Int)/10^30,(-431460822702052631560284107 : Int)/10^30)
theorem v135_pb_checked : Scalar.distance (sourceCoefficient 1 40 1 1) v135_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v135_pg : Scalar.QComplex := ((-93083360699051975824297 : Int)/10^30,(-687101466324051647120 : Int)/10^30)
theorem v135_pg_checked : Scalar.distance (sourceCoefficient 1 40 1 2) v135_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v135_mb : Scalar.QComplex := ((2812526393842669996181559 : Int)/10^30,(-431463410439205589776793371 : Int)/10^30)
theorem v135_mb_checked : Scalar.distance (sourceCoefficient 1 40 3 1) v135_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v135_mg : Scalar.QComplex := ((-93083918977482204204710 : Int)/10^30,(-606774462520431482220 : Int)/10^30)
theorem v135_mg_checked : Scalar.distance (sourceCoefficient 1 40 3 2) v135_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v135_upper : Scalar.QComplex := ((999984007549093242321337738222 : Int)/10^30,(5655496976838494630407351614 : Int)/10^30)
theorem v135_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 40 5) 1) 14) v135_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material135 : Material (1 : Basis) (40 : Basis) where
  plus := ![v135_pa,v135_pb,v135_pg]
  minus := ![(Primitive.Addresses.material135 1).one,v135_mb,v135_mg]
  upper := v135_upper
  lower := (Primitive.Addresses.material135 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v135_pa_checked.trans (by decide +kernel)
    · exact v135_pb_checked.trans (by decide +kernel)
    · exact v135_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 40 Primitive.Addresses.material135
    · exact v135_mb_checked.trans (by decide +kernel)
    · exact v135_mg_checked.trans (by decide +kernel)
  upper_error := v135_upper_checked
  lower_error := reuse_lower_error 1 40 Primitive.Addresses.material135

def v136_pa : Scalar.QComplex := ((999972864122495638051774676658 : Int)/10^30,(7366886632280692611161419399 : Int)/10^30)
theorem v136_pa_checked : Scalar.distance (sourceCoefficient 1 41 1 0) v136_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v136_pb : Scalar.QComplex := ((3178609433618968847516773 : Int)/10^30,(-431460851499314355248435781 : Int)/10^30)
theorem v136_pb_checked : Scalar.distance (sourceCoefficient 1 41 1 1) v136_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v136_pg : Scalar.QComplex := ((-93083368776524093376132 : Int)/10^30,(-685753233643175714071 : Int)/10^30)
theorem v136_pg_checked : Scalar.distance (sourceCoefficient 1 41 1 2) v136_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v136_mb : Scalar.QComplex := ((2806276967508890353776504 : Int)/10^30,(-431463433843502565616156220 : Int)/10^30)
theorem v136_mb_checked : Scalar.distance (sourceCoefficient 1 41 3 1) v136_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v136_mg : Scalar.QComplex := ((-93083925891487232694422 : Int)/10^30,(-605426223371069551931 : Int)/10^30)
theorem v136_mg_checked : Scalar.distance (sourceCoefficient 1 41 3 2) v136_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v136_upper : Scalar.QComplex := ((999984089358388173499453432562 : Int)/10^30,(5641013213522593860025982101 : Int)/10^30)
theorem v136_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 41 5) 1) 14) v136_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material136 : Material (1 : Basis) (41 : Basis) where
  plus := ![v136_pa,v136_pb,v136_pg]
  minus := ![(Primitive.Addresses.material136 1).one,v136_mb,v136_mg]
  upper := v136_upper
  lower := (Primitive.Addresses.material136 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v136_pa_checked.trans (by decide +kernel)
    · exact v136_pb_checked.trans (by decide +kernel)
    · exact v136_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 41 Primitive.Addresses.material136
    · exact v136_mb_checked.trans (by decide +kernel)
    · exact v136_mg_checked.trans (by decide +kernel)
  upper_error := v136_upper_checked
  lower_error := reuse_lower_error 1 41 Primitive.Addresses.material136

def v137_pa : Scalar.QComplex := ((999972950126368244791355319675 : Int)/10^30,(7355203298879435009116880207 : Int)/10^30)
theorem v137_pa_checked : Scalar.distance (sourceCoefficient 1 42 1 0) v137_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v137_pb : Scalar.QComplex := ((3173568293117825931893807 : Int)/10^30,(-431460874640951841628579753 : Int)/10^30)
theorem v137_pb_checked : Scalar.distance (sourceCoefficient 1 42 1 1) v137_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v137_pg : Scalar.QComplex := ((-93083375275691576886458 : Int)/10^30,(-684665669018426074093 : Int)/10^30)
theorem v137_pg_checked : Scalar.distance (sourceCoefficient 1 42 1 2) v137_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v137_mb : Scalar.QComplex := ((2801235808914603548147307 : Int)/10^30,(-431463452634854227360584730 : Int)/10^30)
theorem v137_mb_checked : Scalar.distance (sourceCoefficient 1 42 3 1) v137_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v137_mg : Scalar.QComplex := ((-93083931452133007201125 : Int)/10^30,(-604338653542781099274 : Int)/10^30)
theorem v137_mg_checked : Scalar.distance (sourceCoefficient 1 42 3 2) v137_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v137_upper : Scalar.QComplex := ((999984155197759140729538305642 : Int)/10^30,(5629329749087407029548874518 : Int)/10^30)
theorem v137_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 42 5) 1) 14) v137_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material137 : Material (1 : Basis) (42 : Basis) where
  plus := ![v137_pa,v137_pb,v137_pg]
  minus := ![(Primitive.Addresses.material137 1).one,v137_mb,v137_mg]
  upper := v137_upper
  lower := (Primitive.Addresses.material137 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v137_pa_checked.trans (by decide +kernel)
    · exact v137_pb_checked.trans (by decide +kernel)
    · exact v137_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 42 Primitive.Addresses.material137
    · exact v137_mb_checked.trans (by decide +kernel)
    · exact v137_mg_checked.trans (by decide +kernel)
  upper_error := v137_upper_checked
  lower_error := reuse_lower_error 1 42 Primitive.Addresses.material137

def v138_pa : Scalar.QComplex := ((999973063848871522128068471092 : Int)/10^30,(7339725928174575079807654418 : Int)/10^30)
theorem v138_pa_checked : Scalar.distance (sourceCoefficient 1 43 1 0) v138_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v138_pb : Scalar.QComplex := ((3166890096549034777540084 : Int)/10^30,(-431460905176657780361886550 : Int)/10^30)
theorem v138_pb_checked : Scalar.distance (sourceCoefficient 1 43 1 1) v138_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v138_pg : Scalar.QComplex := ((-93083383862565719726328 : Int)/10^30,(-683224929468255341406 : Int)/10^30)
theorem v138_pg_checked : Scalar.distance (sourceCoefficient 1 43 1 2) v138_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v138_mb : Scalar.QComplex := ((2794557588481471237031287 : Int)/10^30,(-431463477407565932196426271 : Int)/10^30)
theorem v138_mb_checked : Scalar.distance (sourceCoefficient 1 43 3 1) v138_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v138_mg : Scalar.QComplex := ((-93083938795710609458535 : Int)/10^30,(-602897907118977899351 : Int)/10^30)
theorem v138_mg_checked : Scalar.distance (sourceCoefficient 1 43 3 2) v138_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v138_upper : Scalar.QComplex := ((999984242207555301270313574428 : Int)/10^30,(5613852205159548833674523581 : Int)/10^30)
theorem v138_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 43 5) 1) 14) v138_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material138 : Material (1 : Basis) (43 : Basis) where
  plus := ![v138_pa,v138_pb,v138_pg]
  minus := ![(Primitive.Addresses.material138 1).one,v138_mb,v138_mg]
  upper := v138_upper
  lower := (Primitive.Addresses.material138 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v138_pa_checked.trans (by decide +kernel)
    · exact v138_pb_checked.trans (by decide +kernel)
    · exact v138_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 43 Primitive.Addresses.material138
    · exact v138_mb_checked.trans (by decide +kernel)
    · exact v138_mg_checked.trans (by decide +kernel)
  upper_error := v138_upper_checked
  lower_error := reuse_lower_error 1 43 Primitive.Addresses.material138

def v139_pa : Scalar.QComplex := ((999973106811542986112841707995 : Int)/10^30,(7333870306355464168163112104 : Int)/10^30)
theorem v139_pa_checked : Scalar.distance (sourceCoefficient 1 44 1 0) v139_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v139_pb : Scalar.QComplex := ((3164363505114948510553808 : Int)/10^30,(-431460916693430556197338470 : Int)/10^30)
theorem v139_pb_checked : Scalar.distance (sourceCoefficient 1 44 1 1) v139_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v139_pg : Scalar.QComplex := ((-93083387104492024978335 : Int)/10^30,(-682679848138436982576 : Int)/10^30)
theorem v139_pg_checked : Scalar.distance (sourceCoefficient 1 44 1 2) v139_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v139_mb : Scalar.QComplex := ((2792030988049694222533168 : Int)/10^30,(-431463486743999805648562494 : Int)/10^30)
theorem v139_mb_checked : Scalar.distance (sourceCoefficient 1 44 3 1) v139_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v139_mg : Scalar.QComplex := ((-93083941567255069511745 : Int)/10^30,(-602352823194481840567 : Int)/10^30)
theorem v139_mg_checked : Scalar.distance (sourceCoefficient 1 44 3 2) v139_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v139_upper : Scalar.QComplex := ((999984275063890735479041144096 : Int)/10^30,(5607996517912025368209566468 : Int)/10^30)
theorem v139_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 44 5) 1) 14) v139_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material139 : Material (1 : Basis) (44 : Basis) where
  plus := ![v139_pa,v139_pb,v139_pg]
  minus := ![(Primitive.Addresses.material139 1).one,v139_mb,v139_mg]
  upper := v139_upper
  lower := (Primitive.Addresses.material139 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v139_pa_checked.trans (by decide +kernel)
    · exact v139_pb_checked.trans (by decide +kernel)
    · exact v139_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 44 Primitive.Addresses.material139
    · exact v139_mb_checked.trans (by decide +kernel)
    · exact v139_mg_checked.trans (by decide +kernel)
  upper_error := v139_upper_checked
  lower_error := reuse_lower_error 1 44 Primitive.Addresses.material139

def v140_pa : Scalar.QComplex := ((999973128173235655618064428346 : Int)/10^30,(7330957061231167171409704861 : Int)/10^30)
theorem v140_pa_checked : Scalar.distance (sourceCoefficient 1 45 1 0) v140_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v140_pb : Scalar.QComplex := ((3163106494279322081624412 : Int)/10^30,(-431460922415820303765789956 : Int)/10^30)
theorem v140_pb_checked : Scalar.distance (sourceCoefficient 1 45 1 1) v140_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v140_pg : Scalar.QComplex := ((-93083388716003672333610 : Int)/10^30,(-682408663358296921029 : Int)/10^30)
theorem v140_pg_checked : Scalar.distance (sourceCoefficient 1 45 1 2) v140_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v140_mb : Scalar.QComplex := ((2790773972743945750656065 : Int)/10^30,(-431463491381643685030615192 : Int)/10^30)
theorem v140_mb_checked : Scalar.distance (sourceCoefficient 1 45 3 1) v140_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v140_mg : Scalar.QComplex := ((-93083942944745865275814 : Int)/10^30,(-602081637124654294546 : Int)/10^30)
theorem v140_mg_checked : Scalar.distance (sourceCoefficient 1 45 3 2) v140_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v140_upper : Scalar.QComplex := ((999984291397554792248912242030 : Int)/10^30,(5605083240258321140339808244 : Int)/10^30)
theorem v140_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 45 5) 1) 14) v140_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material140 : Material (1 : Basis) (45 : Basis) where
  plus := ![v140_pa,v140_pb,v140_pg]
  minus := ![(Primitive.Addresses.material140 1).one,v140_mb,v140_mg]
  upper := v140_upper
  lower := (Primitive.Addresses.material140 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v140_pa_checked.trans (by decide +kernel)
    · exact v140_pb_checked.trans (by decide +kernel)
    · exact v140_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 45 Primitive.Addresses.material140
    · exact v140_mb_checked.trans (by decide +kernel)
    · exact v140_mg_checked.trans (by decide +kernel)
  upper_error := v140_upper_checked
  lower_error := reuse_lower_error 1 45 Primitive.Addresses.material140

def v141_pa : Scalar.QComplex := ((999973248004909527926447753916 : Int)/10^30,(7314593256750700998787143719 : Int)/10^30)
theorem v141_pa_checked : Scalar.distance (sourceCoefficient 1 46 1 0) v141_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v141_pb : Scalar.QComplex := ((3156045818624720250132576 : Int)/10^30,(-431460954467948193897958594 : Int)/10^30)
theorem v141_pb_checked : Scalar.distance (sourceCoefficient 1 46 1 1) v141_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v141_pg : Scalar.QComplex := ((-93083397750793452062806 : Int)/10^30,(-680885408546503762910 : Int)/10^30)
theorem v141_pg_checked : Scalar.distance (sourceCoefficient 1 46 1 2) v141_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v141_mb : Scalar.QComplex := ((2783713272058813359259173 : Int)/10^30,(-431463517340714551796065414 : Int)/10^30)
theorem v141_mb_checked : Scalar.distance (sourceCoefficient 1 46 3 1) v141_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v141_mg : Scalar.QComplex := ((-93083950665031983212361 : Int)/10^30,(-600558375083421850962 : Int)/10^30)
theorem v141_mg_checked : Scalar.distance (sourceCoefficient 1 46 3 2) v141_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v141_upper : Scalar.QComplex := ((999984382986608168816956754386 : Int)/10^30,(5588719253331221454797704810 : Int)/10^30)
theorem v141_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 46 5) 1) 14) v141_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material141 : Material (1 : Basis) (46 : Basis) where
  plus := ![v141_pa,v141_pb,v141_pg]
  minus := ![(Primitive.Addresses.material141 1).one,v141_mb,v141_mg]
  upper := v141_upper
  lower := (Primitive.Addresses.material141 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v141_pa_checked.trans (by decide +kernel)
    · exact v141_pb_checked.trans (by decide +kernel)
    · exact v141_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 46 Primitive.Addresses.material141
    · exact v141_mb_checked.trans (by decide +kernel)
    · exact v141_mg_checked.trans (by decide +kernel)
  upper_error := v141_upper_checked
  lower_error := reuse_lower_error 1 46 Primitive.Addresses.material141

def v142_pa : Scalar.QComplex := ((999973276802336249058456004200 : Int)/10^30,(7310655319340975959442244058 : Int)/10^30)
theorem v142_pa_checked : Scalar.distance (sourceCoefficient 1 47 1 0) v142_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v142_pb : Scalar.QComplex := ((3154346672319960449475211 : Int)/10^30,(-431460962158270538567240134 : Int)/10^30)
theorem v142_pb_checked : Scalar.distance (sourceCoefficient 1 47 1 1) v142_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v142_pg : Scalar.QComplex := ((-93083399920667432554738 : Int)/10^30,(-680518838411803530245 : Int)/10^30)
theorem v142_pg_checked : Scalar.distance (sourceCoefficient 1 47 1 2) v142_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v142_mb : Scalar.QComplex := ((2782014119750321558497588 : Int)/10^30,(-431463523564747298707926392 : Int)/10^30)
theorem v142_mb_checked : Scalar.distance (sourceCoefficient 1 47 3 1) v142_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v142_mg : Scalar.QComplex := ((-93083952518571639220739 : Int)/10^30,(-600191803212708914860 : Int)/10^30)
theorem v142_mg_checked : Scalar.distance (sourceCoefficient 1 47 3 2) v142_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v142_upper : Scalar.QComplex := ((999984404987469277270380028289 : Int)/10^30,(5584781272084845566086152284 : Int)/10^30)
theorem v142_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 47 5) 1) 14) v142_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material142 : Material (1 : Basis) (47 : Basis) where
  plus := ![v142_pa,v142_pb,v142_pg]
  minus := ![(Primitive.Addresses.material142 1).one,v142_mb,v142_mg]
  upper := v142_upper
  lower := (Primitive.Addresses.material142 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v142_pa_checked.trans (by decide +kernel)
    · exact v142_pb_checked.trans (by decide +kernel)
    · exact v142_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 47 Primitive.Addresses.material142
    · exact v142_mb_checked.trans (by decide +kernel)
    · exact v142_mg_checked.trans (by decide +kernel)
  upper_error := v142_upper_checked
  lower_error := reuse_lower_error 1 47 Primitive.Addresses.material142

def v143_pa : Scalar.QComplex := ((999973476961554821202070027082 : Int)/10^30,(7283225481803321968836470832 : Int)/10^30)
theorem v143_pa_checked : Scalar.distance (sourceCoefficient 1 48 1 0) v143_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v143_pb : Scalar.QComplex := ((3142511211279468451702596 : Int)/10^30,(-431461015477957460279098723 : Int)/10^30)
theorem v143_pb_checked : Scalar.distance (sourceCoefficient 1 48 1 1) v143_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v143_pg : Scalar.QComplex := ((-93083414988274515259470 : Int)/10^30,(-677965481680409331614 : Int)/10^30)
theorem v143_pg_checked : Scalar.distance (sourceCoefficient 1 48 1 2) v143_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v143_mb : Scalar.QComplex := ((2770178617104224229507422 : Int)/10^30,(-431463566670944538496460610 : Int)/10^30)
theorem v143_mb_checked : Scalar.distance (sourceCoefficient 1 48 3 1) v143_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v143_mg : Scalar.QComplex := ((-93083965382741251291758 : Int)/10^30,(-597638434429379828951 : Int)/10^30)
theorem v143_mg_checked : Scalar.distance (sourceCoefficient 1 48 3 2) v143_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v143_upper : Scalar.QComplex := ((999984557804978561202477959637 : Int)/10^30,(5557351129944059499700294774 : Int)/10^30)
theorem v143_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 48 5) 1) 14) v143_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material143 : Material (1 : Basis) (48 : Basis) where
  plus := ![v143_pa,v143_pb,v143_pg]
  minus := ![(Primitive.Addresses.material143 1).one,v143_mb,v143_mg]
  upper := v143_upper
  lower := (Primitive.Addresses.material143 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v143_pa_checked.trans (by decide +kernel)
    · exact v143_pb_checked.trans (by decide +kernel)
    · exact v143_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 48 Primitive.Addresses.material143
    · exact v143_mb_checked.trans (by decide +kernel)
    · exact v143_mg_checked.trans (by decide +kernel)
  upper_error := v143_upper_checked
  lower_error := reuse_lower_error 1 48 Primitive.Addresses.material143

def v144_pa : Scalar.QComplex := ((999973637229236467255982226447 : Int)/10^30,(7261187680495743628711876446 : Int)/10^30)
theorem v144_pa_checked : Scalar.distance (sourceCoefficient 1 49 1 0) v144_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v144_pb : Scalar.QComplex := ((3133002313604580190685778 : Int)/10^30,(-431461058002689023577424657 : Int)/10^30)
theorem v144_pb_checked : Scalar.distance (sourceCoefficient 1 49 1 1) v144_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v144_pg : Scalar.QComplex := ((-93083427034757594259221 : Int)/10^30,(-675914052610331107683 : Int)/10^30)
theorem v144_pg_checked : Scalar.distance (sourceCoefficient 1 49 1 2) v144_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v144_mb : Scalar.QComplex := ((2760669686273005054629840 : Int)/10^30,(-431463600989909839318518351 : Int)/10^30)
theorem v144_mb_checked : Scalar.distance (sourceCoefficient 1 49 3 1) v144_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v144_mg : Scalar.QComplex := ((-93083975658928950293329 : Int)/10^30,(-595586995727570059031 : Int)/10^30)
theorem v144_mg_checked : Scalar.distance (sourceCoefficient 1 49 3 2) v144_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v144_upper : Scalar.QComplex := ((999984680037175704208038193160 : Int)/10^30,(5535313084851718314637391336 : Int)/10^30)
theorem v144_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 49 5) 1) 14) v144_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material144 : Material (1 : Basis) (49 : Basis) where
  plus := ![v144_pa,v144_pb,v144_pg]
  minus := ![(Primitive.Addresses.material144 1).one,v144_mb,v144_mg]
  upper := v144_upper
  lower := (Primitive.Addresses.material144 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v144_pa_checked.trans (by decide +kernel)
    · exact v144_pb_checked.trans (by decide +kernel)
    · exact v144_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 49 Primitive.Addresses.material144
    · exact v144_mb_checked.trans (by decide +kernel)
    · exact v144_mg_checked.trans (by decide +kernel)
  upper_error := v144_upper_checked
  lower_error := reuse_lower_error 1 49 Primitive.Addresses.material144

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
