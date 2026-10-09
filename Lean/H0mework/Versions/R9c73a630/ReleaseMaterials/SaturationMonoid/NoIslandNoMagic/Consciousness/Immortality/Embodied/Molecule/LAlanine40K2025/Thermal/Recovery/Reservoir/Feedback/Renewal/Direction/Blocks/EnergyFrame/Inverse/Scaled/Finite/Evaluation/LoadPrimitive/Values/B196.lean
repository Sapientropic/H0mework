import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B130
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B131

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3137_pa : Scalar.QComplex := ((999998860458373496957418630166 : Int)/10^30,(-1509662861188208017559639777 : Int)/10^30)
theorem v3137_pa_checked : Scalar.distance (sourceCoefficient 40 78 1 0) v3137_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3137_pb : Scalar.QComplex := ((-651385549850731431891536 : Int)/10^30,(-431477003453008070632963660 : Int)/10^30)
theorem v3137_pb_checked : Scalar.distance (sourceCoefficient 40 78 1 1) v3137_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3137_pg : Scalar.QComplex := ((-93086321031498922768265 : Int)/10^30,(140529121884680850322 : Int)/10^30)
theorem v3137_pg_checked : Scalar.distance (sourceCoefficient 40 78 1 2) v3137_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3137_mb : Scalar.QComplex := ((-1023730528287218848479869 : Int)/10^30,(-431476280678008006790200447 : Int)/10^30)
theorem v3137_mb_checked : Scalar.distance (sourceCoefficient 40 78 3 1) v3137_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3137_mg : Scalar.QComplex := ((-93086165100904357924901 : Int)/10^30,(220858372157181729843 : Int)/10^30)
theorem v3137_mg_checked : Scalar.distance (sourceCoefficient 40 78 3 2) v3137_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3137_upper : Scalar.QComplex := ((999994765536396096126704104975 : Int)/10^30,(-3235567926685905013046886763 : Int)/10^30)
theorem v3137_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 78 5) 1) 14) v3137_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3137 : Material (40 : Basis) (78 : Basis) where
  plus := ![v3137_pa,v3137_pb,v3137_pg]
  minus := ![(Primitive.Addresses.material3137 1).one,v3137_mb,v3137_mg]
  upper := v3137_upper
  lower := (Primitive.Addresses.material3137 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3137_pa_checked.trans (by decide +kernel)
    · exact v3137_pb_checked.trans (by decide +kernel)
    · exact v3137_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 78 Primitive.Addresses.material3137
    · exact v3137_mb_checked.trans (by decide +kernel)
    · exact v3137_mg_checked.trans (by decide +kernel)
  upper_error := v3137_upper_checked
  lower_error := reuse_lower_error 40 78 Primitive.Addresses.material3137

def v3138_pa : Scalar.QComplex := ((999998852023309433015040872351 : Int)/10^30,(-1515239935879294277363078127 : Int)/10^30)
theorem v3138_pa_checked : Scalar.distance (sourceCoefficient 40 79 1 0) v3138_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3138_pb : Scalar.QComplex := ((-653791931336396714544478 : Int)/10^30,(-431476999330210897104862037 : Int)/10^30)
theorem v3138_pb_checked : Scalar.distance (sourceCoefficient 40 79 1 1) v3138_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3138_pg : Scalar.QComplex := ((-93086320194180326085992 : Int)/10^30,(141048271762397481314 : Int)/10^30)
theorem v3138_pg_checked : Scalar.distance (sourceCoefficient 40 79 1 2) v3138_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3138_mb : Scalar.QComplex := ((-1026136905319090050089788 : Int)/10^30,(-431476274478613525637650702 : Int)/10^30)
theorem v3138_mb_checked : Scalar.distance (sourceCoefficient 40 79 3 1) v3138_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3138_mg : Scalar.QComplex := ((-93086163815583110187681 : Int)/10^30,(221377521119026897533 : Int)/10^30)
theorem v3138_mg_checked : Scalar.distance (sourceCoefficient 40 79 3 2) v3138_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3138_upper : Scalar.QComplex := ((999994747475819626670237342522 : Int)/10^30,(-3241144978512438298360615901 : Int)/10^30)
theorem v3138_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 79 5) 1) 14) v3138_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3138 : Material (40 : Basis) (79 : Basis) where
  plus := ![v3138_pa,v3138_pb,v3138_pg]
  minus := ![(Primitive.Addresses.material3138 1).one,v3138_mb,v3138_mg]
  upper := v3138_upper
  lower := (Primitive.Addresses.material3138 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3138_pa_checked.trans (by decide +kernel)
    · exact v3138_pb_checked.trans (by decide +kernel)
    · exact v3138_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 79 Primitive.Addresses.material3138
    · exact v3138_mb_checked.trans (by decide +kernel)
    · exact v3138_mg_checked.trans (by decide +kernel)
  upper_error := v3138_upper_checked
  lower_error := reuse_lower_error 40 79 Primitive.Addresses.material3138

def v3139_pa : Scalar.QComplex := ((999998838784663017888639769920 : Int)/10^30,(-1523951877699280856784142018 : Int)/10^30)
theorem v3139_pa_checked : Scalar.distance (sourceCoefficient 40 80 1 0) v3139_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3139_pb : Scalar.QComplex := ((-657550937002408598513318 : Int)/10^30,(-431476992854185843240126870 : Int)/10^30)
theorem v3139_pb_checked : Scalar.distance (sourceCoefficient 40 80 1 1) v3139_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3139_pg : Scalar.QComplex := ((-93086318879446318547615 : Int)/10^30,(141859235173565810789 : Int)/10^30)
theorem v3139_pg_checked : Scalar.distance (sourceCoefficient 40 80 1 2) v3139_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3139_mb : Scalar.QComplex := ((-1029895903996934377412504 : Int)/10^30,(-431476264758738292655266802 : Int)/10^30)
theorem v3139_mb_checked : Scalar.distance (sourceCoefficient 40 80 3 1) v3139_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3139_mg : Scalar.QComplex := ((-93086161801024692782781 : Int)/10^30,(222188483093680251087 : Int)/10^30)
theorem v3139_mg_checked : Scalar.distance (sourceCoefficient 40 80 3 2) v3139_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3139_upper : Scalar.QComplex := ((999994719201171688843817470519 : Int)/10^30,(-3249856884508308201599038795 : Int)/10^30)
theorem v3139_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 80 5) 1) 14) v3139_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3139 : Material (40 : Basis) (80 : Basis) where
  plus := ![v3139_pa,v3139_pb,v3139_pg]
  minus := ![(Primitive.Addresses.material3139 1).one,v3139_mb,v3139_mg]
  upper := v3139_upper
  lower := (Primitive.Addresses.material3139 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3139_pa_checked.trans (by decide +kernel)
    · exact v3139_pb_checked.trans (by decide +kernel)
    · exact v3139_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 80 Primitive.Addresses.material3139
    · exact v3139_mb_checked.trans (by decide +kernel)
    · exact v3139_mg_checked.trans (by decide +kernel)
  upper_error := v3139_upper_checked
  lower_error := reuse_lower_error 40 80 Primitive.Addresses.material3139

def v3140_pa : Scalar.QComplex := ((999998798464082705624148189890 : Int)/10^30,(-1550183986144932138126863427 : Int)/10^30)
theorem v3140_pa_checked : Scalar.distance (sourceCoefficient 40 81 1 0) v3140_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3140_pb : Scalar.QComplex := ((-668869497746465008945755 : Int)/10^30,(-431476973090860328146812410 : Int)/10^30)
theorem v3140_pb_checked : Scalar.distance (sourceCoefficient 40 81 1 1) v3140_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3140_pg : Scalar.QComplex := ((-93086314870939107036188 : Int)/10^30,(144301088025114825986 : Int)/10^30)
theorem v3140_pg_checked : Scalar.distance (sourceCoefficient 40 81 1 2) v3140_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3140_mb : Scalar.QComplex := ((-1041214443471713526665739 : Int)/10^30,(-431476235228011983282983573 : Int)/10^30)
theorem v3140_mb_checked : Scalar.distance (sourceCoefficient 40 81 3 1) v3140_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3140_mg : Scalar.QComplex := ((-93086155685309939904883 : Int)/10^30,(224630331576854664392 : Int)/10^30)
theorem v3140_mg_checked : Scalar.distance (sourceCoefficient 40 81 3 2) v3140_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3140_upper : Scalar.QComplex := ((999994633606412010441739238675 : Int)/10^30,(-3276088884294651628565376127 : Int)/10^30)
theorem v3140_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 81 5) 1) 14) v3140_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3140 : Material (40 : Basis) (81 : Basis) where
  plus := ![v3140_pa,v3140_pb,v3140_pg]
  minus := ![(Primitive.Addresses.material3140 1).one,v3140_mb,v3140_mg]
  upper := v3140_upper
  lower := (Primitive.Addresses.material3140 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3140_pa_checked.trans (by decide +kernel)
    · exact v3140_pb_checked.trans (by decide +kernel)
    · exact v3140_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 81 Primitive.Addresses.material3140
    · exact v3140_mb_checked.trans (by decide +kernel)
    · exact v3140_mg_checked.trans (by decide +kernel)
  upper_error := v3140_upper_checked
  lower_error := reuse_lower_error 40 81 Primitive.Addresses.material3140

def v3141_pa : Scalar.QComplex := ((999998783005448220368359990964 : Int)/10^30,(-1560124233028743201282845774 : Int)/10^30)
theorem v3141_pa_checked : Scalar.distance (sourceCoefficient 40 82 1 0) v3141_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3141_pb : Scalar.QComplex := ((-673158489098019050348924 : Int)/10^30,(-431476965498428550197992378 : Int)/10^30)
theorem v3141_pb_checked : Scalar.distance (sourceCoefficient 40 82 1 1) v3141_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3141_pg : Scalar.QComplex := ((-93086313332453610326956 : Int)/10^30,(145226389932992784537 : Int)/10^30)
theorem v3141_pg_checked : Scalar.distance (sourceCoefficient 40 82 1 2) v3141_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3141_mb : Scalar.QComplex := ((-1045503426674353397360806 : Int)/10^30,(-431476223934376664952071675 : Int)/10^30)
theorem v3141_mb_checked : Scalar.distance (sourceCoefficient 40 82 3 1) v3141_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3141_mg : Scalar.QComplex := ((-93086153348331143596353 : Int)/10^30,(225555631812556741408 : Int)/10^30)
theorem v3141_mg_checked : Scalar.distance (sourceCoefficient 40 82 3 2) v3141_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3141_upper : Scalar.QComplex := ((999994600991836199701264912055 : Int)/10^30,(-3286029089693431896521726856 : Int)/10^30)
theorem v3141_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 82 5) 1) 14) v3141_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3141 : Material (40 : Basis) (82 : Basis) where
  plus := ![v3141_pa,v3141_pb,v3141_pg]
  minus := ![(Primitive.Addresses.material3141 1).one,v3141_mb,v3141_mg]
  upper := v3141_upper
  lower := (Primitive.Addresses.material3141 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3141_pa_checked.trans (by decide +kernel)
    · exact v3141_pb_checked.trans (by decide +kernel)
    · exact v3141_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 82 Primitive.Addresses.material3141
    · exact v3141_mb_checked.trans (by decide +kernel)
    · exact v3141_mg_checked.trans (by decide +kernel)
  upper_error := v3141_upper_checked
  lower_error := reuse_lower_error 40 82 Primitive.Addresses.material3141

def v3142_pa : Scalar.QComplex := ((999998761744660449481747677123 : Int)/10^30,(-1573692837190520664560985243 : Int)/10^30)
theorem v3142_pa_checked : Scalar.distance (sourceCoefficient 40 83 1 0) v3142_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3142_pb : Scalar.QComplex := ((-679013034355264813633448 : Int)/10^30,(-431476955042875449403714824 : Int)/10^30)
theorem v3142_pb_checked : Scalar.distance (sourceCoefficient 40 83 1 1) v3142_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3142_pg : Scalar.QComplex := ((-93086311215074108781795 : Int)/10^30,(146489442590984233354 : Int)/10^30)
theorem v3142_pg_checked : Scalar.distance (sourceCoefficient 40 83 1 2) v3142_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3142_mb : Scalar.QComplex := ((-1051357960729012970081996 : Int)/10^30,(-431476208426618579165126577 : Int)/10^30)
theorem v3142_mb_checked : Scalar.distance (sourceCoefficient 40 83 3 1) v3142_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3142_mg : Scalar.QComplex := ((-93086150140994872381746 : Int)/10^30,(226818682173052814696 : Int)/10^30)
theorem v3142_mg_checked : Scalar.distance (sourceCoefficient 40 83 3 2) v3142_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3142_upper : Scalar.QComplex := ((999994556312900245186694671684 : Int)/10^30,(-3299597636952176412090762714 : Int)/10^30)
theorem v3142_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 83 5) 1) 14) v3142_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3142 : Material (40 : Basis) (83 : Basis) where
  plus := ![v3142_pa,v3142_pb,v3142_pg]
  minus := ![(Primitive.Addresses.material3142 1).one,v3142_mb,v3142_mg]
  upper := v3142_upper
  lower := (Primitive.Addresses.material3142 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3142_pa_checked.trans (by decide +kernel)
    · exact v3142_pb_checked.trans (by decide +kernel)
    · exact v3142_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 83 Primitive.Addresses.material3142
    · exact v3142_mb_checked.trans (by decide +kernel)
    · exact v3142_mg_checked.trans (by decide +kernel)
  upper_error := v3142_upper_checked
  lower_error := reuse_lower_error 40 83 Primitive.Addresses.material3142

def v3143_pa : Scalar.QComplex := ((999998705829201955403807506863 : Int)/10^30,(-1608831849887096769493512676 : Int)/10^30)
theorem v3143_pa_checked : Scalar.distance (sourceCoefficient 40 84 1 0) v3143_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3143_pb : Scalar.QComplex := ((-694174721791436511737711 : Int)/10^30,(-431476927473494490757099695 : Int)/10^30)
theorem v3143_pb_checked : Scalar.distance (sourceCoefficient 40 84 1 1) v3143_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3143_pg : Scalar.QComplex := ((-93086305638696726551584 : Int)/10^30,(149760407115405733573 : Int)/10^30)
theorem v3143_pg_checked : Scalar.distance (sourceCoefficient 40 84 1 2) v3143_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3143_mb : Scalar.QComplex := ((-1066519618728661423865659 : Int)/10^30,(-431476167773394485496129664 : Int)/10^30)
theorem v3143_mb_checked : Scalar.distance (sourceCoefficient 40 84 3 1) v3143_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3143_mg : Scalar.QComplex := ((-93086141741924500689382 : Int)/10^30,(230089640667382201859 : Int)/10^30)
theorem v3143_mg_checked : Scalar.distance (sourceCoefficient 40 84 3 2) v3143_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3143_upper : Scalar.QComplex := ((999994439750776902655746298444 : Int)/10^30,(-3334736500808312073851921009 : Int)/10^30)
theorem v3143_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 84 5) 1) 14) v3143_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3143 : Material (40 : Basis) (84 : Basis) where
  plus := ![v3143_pa,v3143_pb,v3143_pg]
  minus := ![(Primitive.Addresses.material3143 1).one,v3143_mb,v3143_mg]
  upper := v3143_upper
  lower := (Primitive.Addresses.material3143 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3143_pa_checked.trans (by decide +kernel)
    · exact v3143_pb_checked.trans (by decide +kernel)
    · exact v3143_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 84 Primitive.Addresses.material3143
    · exact v3143_mb_checked.trans (by decide +kernel)
    · exact v3143_mg_checked.trans (by decide +kernel)
  upper_error := v3143_upper_checked
  lower_error := reuse_lower_error 40 84 Primitive.Addresses.material3143

def v3144_pa : Scalar.QComplex := ((999998575515090084083259060699 : Int)/10^30,(-1687888559909858179177730779 : Int)/10^30)
theorem v3144_pa_checked : Scalar.distance (sourceCoefficient 40 85 1 0) v3144_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3144_pb : Scalar.QComplex := ((-728285898102986034170614 : Int)/10^30,(-431476862850239468395967804 : Int)/10^30)
theorem v3144_pb_checked : Scalar.distance (sourceCoefficient 40 85 1 1) v3144_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3144_pg : Scalar.QComplex := ((-93086292602588205370930 : Int)/10^30,(157119512182704447940 : Int)/10^30)
theorem v3144_pg_checked : Scalar.distance (sourceCoefficient 40 85 1 2) v3144_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3144_mb : Scalar.QComplex := ((-1100630726572102486802005 : Int)/10^30,(-431476073713754678809584631 : Int)/10^30)
theorem v3144_mb_checked : Scalar.distance (sourceCoefficient 40 85 3 1) v3144_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3144_mg : Scalar.QComplex := ((-93086122355244602157454 : Int)/10^30,(237448731744975242708 : Int)/10^30)
theorem v3144_mg_checked : Scalar.distance (sourceCoefficient 40 85 3 2) v3144_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3144_upper : Scalar.QComplex := ((999994172992149588319786063543 : Int)/10^30,(-3413792868175055472125395060 : Int)/10^30)
theorem v3144_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 85 5) 1) 14) v3144_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3144 : Material (40 : Basis) (85 : Basis) where
  plus := ![v3144_pa,v3144_pb,v3144_pg]
  minus := ![(Primitive.Addresses.material3144 1).one,v3144_mb,v3144_mg]
  upper := v3144_upper
  lower := (Primitive.Addresses.material3144 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3144_pa_checked.trans (by decide +kernel)
    · exact v3144_pb_checked.trans (by decide +kernel)
    · exact v3144_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 85 Primitive.Addresses.material3144
    · exact v3144_mb_checked.trans (by decide +kernel)
    · exact v3144_mg_checked.trans (by decide +kernel)
  upper_error := v3144_upper_checked
  lower_error := reuse_lower_error 40 85 Primitive.Addresses.material3144

def v3145_pa : Scalar.QComplex := ((999998550791480386926912381714 : Int)/10^30,(-1702473183054820648272943107 : Int)/10^30)
theorem v3145_pa_checked : Scalar.distance (sourceCoefficient 40 86 1 0) v3145_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3145_pb : Scalar.QComplex := ((-734578831703526465031660 : Int)/10^30,(-431476850535490280437614701 : Int)/10^30)
theorem v3145_pb_checked : Scalar.distance (sourceCoefficient 40 86 1 1) v3145_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3145_pg : Scalar.QComplex := ((-93086290123487498267344 : Int)/10^30,(158477142311723077088 : Int)/10^30)
theorem v3145_pg_checked : Scalar.distance (sourceCoefficient 40 86 1 2) v3145_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3145_mb : Scalar.QComplex := ((-1106923647202422223414834 : Int)/10^30,(-431476055968491802136978514 : Int)/10^30)
theorem v3145_mb_checked : Scalar.distance (sourceCoefficient 40 86 3 1) v3145_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3145_mg : Scalar.QComplex := ((-93086118704571162184472 : Int)/10^30,(238806359229133872381 : Int)/10^30)
theorem v3145_mg_checked : Scalar.distance (sourceCoefficient 40 86 3 2) v3145_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3145_upper : Scalar.QComplex := ((999994123096840272546791272786 : Int)/10^30,(-3428377426927227568040706452 : Int)/10^30)
theorem v3145_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 86 5) 1) 14) v3145_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3145 : Material (40 : Basis) (86 : Basis) where
  plus := ![v3145_pa,v3145_pb,v3145_pg]
  minus := ![(Primitive.Addresses.material3145 1).one,v3145_mb,v3145_mg]
  upper := v3145_upper
  lower := (Primitive.Addresses.material3145 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3145_pa_checked.trans (by decide +kernel)
    · exact v3145_pb_checked.trans (by decide +kernel)
    · exact v3145_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 86 Primitive.Addresses.material3145
    · exact v3145_mb_checked.trans (by decide +kernel)
    · exact v3145_mg_checked.trans (by decide +kernel)
  upper_error := v3145_upper_checked
  lower_error := reuse_lower_error 40 86 Primitive.Addresses.material3145

def v3146_pa : Scalar.QComplex := ((999998549146839603681654266334 : Int)/10^30,(-1703438938094859818060964555 : Int)/10^30)
theorem v3146_pa_checked : Scalar.distance (sourceCoefficient 40 87 1 0) v3146_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3146_pb : Scalar.QComplex := ((-734995533062854103099680 : Int)/10^30,(-431476849715720344898890825 : Int)/10^30)
theorem v3146_pb_checked : Scalar.distance (sourceCoefficient 40 87 1 1) v3146_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3146_pg : Scalar.QComplex := ((-93086289958512549631269 : Int)/10^30,(158567040975611364291 : Int)/10^30)
theorem v3146_pg_checked : Scalar.distance (sourceCoefficient 40 87 1 2) v3146_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3146_mb : Scalar.QComplex := ((-1107340347699168367909654 : Int)/10^30,(-431476054789127666268855884 : Int)/10^30)
theorem v3146_mb_checked : Scalar.distance (sourceCoefficient 40 87 3 1) v3146_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3146_mg : Scalar.QComplex := ((-93086118462017776926038 : Int)/10^30,(238896257717182827970 : Int)/10^30)
theorem v3146_mg_checked : Scalar.distance (sourceCoefficient 40 87 3 2) v3146_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3146_upper : Scalar.QComplex := ((999994119785396352306019849936 : Int)/10^30,(-3429343177690387260011552184 : Int)/10^30)
theorem v3146_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 87 5) 1) 14) v3146_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3146 : Material (40 : Basis) (87 : Basis) where
  plus := ![v3146_pa,v3146_pb,v3146_pg]
  minus := ![(Primitive.Addresses.material3146 1).one,v3146_mb,v3146_mg]
  upper := v3146_upper
  lower := (Primitive.Addresses.material3146 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3146_pa_checked.trans (by decide +kernel)
    · exact v3146_pb_checked.trans (by decide +kernel)
    · exact v3146_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 87 Primitive.Addresses.material3146
    · exact v3146_mb_checked.trans (by decide +kernel)
    · exact v3146_mg_checked.trans (by decide +kernel)
  upper_error := v3146_upper_checked
  lower_error := reuse_lower_error 40 87 Primitive.Addresses.material3146

def v3147_pa : Scalar.QComplex := ((999998529045946125656458242888 : Int)/10^30,(-1715198514470805642829341938 : Int)/10^30)
theorem v3147_pa_checked : Scalar.distance (sourceCoefficient 40 88 1 0) v3147_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3147_pb : Scalar.QComplex := ((-740069523074303219928008 : Int)/10^30,(-431476839690695052720357068 : Int)/10^30)
theorem v3147_pb_checked : Scalar.distance (sourceCoefficient 40 88 1 1) v3147_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3147_pg : Scalar.QComplex := ((-93086287941559026487242 : Int)/10^30,(159661697649985117412 : Int)/10^30)
theorem v3147_pg_checked : Scalar.distance (sourceCoefficient 40 88 1 2) v3147_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3147_mb : Scalar.QComplex := ((-1112414327170193793904448 : Int)/10^30,(-431476040385481251011721905 : Int)/10^30)
theorem v3147_mb_checked : Scalar.distance (sourceCoefficient 40 88 3 1) v3147_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3147_mg : Scalar.QComplex := ((-93086115500425596307894 : Int)/10^30,(239990912243425822681 : Int)/10^30)
theorem v3147_mg_checked : Scalar.distance (sourceCoefficient 40 88 3 2) v3147_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3147_upper : Scalar.QComplex := ((999994079388570807753230876720 : Int)/10^30,(-3441102701859506845426309948 : Int)/10^30)
theorem v3147_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 88 5) 1) 14) v3147_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3147 : Material (40 : Basis) (88 : Basis) where
  plus := ![v3147_pa,v3147_pb,v3147_pg]
  minus := ![(Primitive.Addresses.material3147 1).one,v3147_mb,v3147_mg]
  upper := v3147_upper
  lower := (Primitive.Addresses.material3147 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3147_pa_checked.trans (by decide +kernel)
    · exact v3147_pb_checked.trans (by decide +kernel)
    · exact v3147_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 88 Primitive.Addresses.material3147
    · exact v3147_mb_checked.trans (by decide +kernel)
    · exact v3147_mg_checked.trans (by decide +kernel)
  upper_error := v3147_upper_checked
  lower_error := reuse_lower_error 40 88 Primitive.Addresses.material3147

def v3148_pa : Scalar.QComplex := ((999998501319850601081602997759 : Int)/10^30,(-1731287975108602951114565648 : Int)/10^30)
theorem v3148_pa_checked : Scalar.distance (sourceCoefficient 40 89 1 0) v3148_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3148_pb : Scalar.QComplex := ((-747011759656139338423550 : Int)/10^30,(-431476825845558199286488414 : Int)/10^30)
theorem v3148_pb_checked : Scalar.distance (sourceCoefficient 40 89 1 1) v3148_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3148_pg : Scalar.QComplex := ((-93086285157630998849033 : Int)/10^30,(161159407667342133004 : Int)/10^30)
theorem v3148_pg_checked : Scalar.distance (sourceCoefficient 40 89 1 2) v3148_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3148_mb : Scalar.QComplex := ((-1119356549219388414399614 : Int)/10^30,(-431476020549512049359398878 : Int)/10^30)
theorem v3148_mb_checked : Scalar.distance (sourceCoefficient 40 89 3 1) v3148_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3148_mg : Scalar.QComplex := ((-93086111424042314629376 : Int)/10^30,(241488619300712445694 : Int)/10^30)
theorem v3148_mg_checked : Scalar.distance (sourceCoefficient 40 89 3 2) v3148_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3148_upper : Scalar.QComplex := ((999994023893567141569669774028 : Int)/10^30,(-3457192090681216950845682947 : Int)/10^30)
theorem v3148_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 89 5) 1) 14) v3148_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3148 : Material (40 : Basis) (89 : Basis) where
  plus := ![v3148_pa,v3148_pb,v3148_pg]
  minus := ![(Primitive.Addresses.material3148 1).one,v3148_mb,v3148_mg]
  upper := v3148_upper
  lower := (Primitive.Addresses.material3148 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3148_pa_checked.trans (by decide +kernel)
    · exact v3148_pb_checked.trans (by decide +kernel)
    · exact v3148_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 89 Primitive.Addresses.material3148
    · exact v3148_mb_checked.trans (by decide +kernel)
    · exact v3148_mg_checked.trans (by decide +kernel)
  upper_error := v3148_upper_checked
  lower_error := reuse_lower_error 40 89 Primitive.Addresses.material3148

def v3149_pa : Scalar.QComplex := ((999998455611716198791688381081 : Int)/10^30,(-1757490876922906101034158412 : Int)/10^30)
theorem v3149_pa_checked : Scalar.distance (sourceCoefficient 40 90 1 0) v3149_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3149_pb : Scalar.QComplex := ((-758317715976337350745750 : Int)/10^30,(-431476802978935535636892059 : Int)/10^30)
theorem v3149_pb_checked : Scalar.distance (sourceCoefficient 40 90 1 1) v3149_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3149_pg : Scalar.QComplex := ((-93086280563618939806141 : Int)/10^30,(163598541516917086197 : Int)/10^30)
theorem v3149_pg_checked : Scalar.distance (sourceCoefficient 40 90 1 2) v3149_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3149_mb : Scalar.QComplex := ((-1130662481596996696706814 : Int)/10^30,(-431475987926366797037810187 : Int)/10^30)
theorem v3149_mb_checked : Scalar.distance (sourceCoefficient 40 90 3 1) v3149_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3149_mg : Scalar.QComplex := ((-93086104725169308474539 : Int)/10^30,(243927748277660892435 : Int)/10^30)
theorem v3149_mg_checked : Scalar.distance (sourceCoefficient 40 90 3 2) v3149_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3149_upper : Scalar.QComplex := ((999993932961669393373095549991 : Int)/10^30,(-3483394874581282488635232747 : Int)/10^30)
theorem v3149_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 90 5) 1) 14) v3149_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3149 : Material (40 : Basis) (90 : Basis) where
  plus := ![v3149_pa,v3149_pb,v3149_pg]
  minus := ![(Primitive.Addresses.material3149 1).one,v3149_mb,v3149_mg]
  upper := v3149_upper
  lower := (Primitive.Addresses.material3149 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3149_pa_checked.trans (by decide +kernel)
    · exact v3149_pb_checked.trans (by decide +kernel)
    · exact v3149_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 90 Primitive.Addresses.material3149
    · exact v3149_mb_checked.trans (by decide +kernel)
    · exact v3149_mg_checked.trans (by decide +kernel)
  upper_error := v3149_upper_checked
  lower_error := reuse_lower_error 40 90 Primitive.Addresses.material3149

def v3150_pa : Scalar.QComplex := ((999998429560324164834851324507 : Int)/10^30,(-1772251924921949368198965078 : Int)/10^30)
theorem v3150_pa_checked : Scalar.distance (sourceCoefficient 40 91 1 0) v3150_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3150_pb : Scalar.QComplex := ((-764686772395335842963359 : Int)/10^30,(-431476789923399814083671030 : Int)/10^30)
theorem v3150_pb_checked : Scalar.distance (sourceCoefficient 40 91 1 1) v3150_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3150_pg : Scalar.QComplex := ((-93086277942810785050780 : Int)/10^30,(164972594347473599644 : Int)/10^30)
theorem v3150_pg_checked : Scalar.distance (sourceCoefficient 40 91 1 2) v3150_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3150_mb : Scalar.QComplex := ((-1137031524378165075674181 : Int)/10^30,(-431475969374627098714184778 : Int)/10^30)
theorem v3150_mb_checked : Scalar.distance (sourceCoefficient 40 91 3 1) v3150_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3150_mg : Scalar.QComplex := ((-93086100918616421837767 : Int)/10^30,(245301798334955339012 : Int)/10^30)
theorem v3150_mg_checked : Scalar.distance (sourceCoefficient 40 91 3 2) v3150_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3150_upper : Scalar.QComplex := ((999993881434086425369708243306 : Int)/10^30,(-3498155855633139428940955735 : Int)/10^30)
theorem v3150_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 91 5) 1) 14) v3150_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3150 : Material (40 : Basis) (91 : Basis) where
  plus := ![v3150_pa,v3150_pb,v3150_pg]
  minus := ![(Primitive.Addresses.material3150 1).one,v3150_mb,v3150_mg]
  upper := v3150_upper
  lower := (Primitive.Addresses.material3150 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3150_pa_checked.trans (by decide +kernel)
    · exact v3150_pb_checked.trans (by decide +kernel)
    · exact v3150_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 91 Primitive.Addresses.material3150
    · exact v3150_mb_checked.trans (by decide +kernel)
    · exact v3150_mg_checked.trans (by decide +kernel)
  upper_error := v3150_upper_checked
  lower_error := reuse_lower_error 40 91 Primitive.Addresses.material3150

def v3151_pa : Scalar.QComplex := ((999998372415460705411459155413 : Int)/10^30,(-1804207978465272315377896281 : Int)/10^30)
theorem v3151_pa_checked : Scalar.distance (sourceCoefficient 40 92 1 0) v3151_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3151_pb : Scalar.QComplex := ((-778475082167815603367757 : Int)/10^30,(-431476761230158715780452965 : Int)/10^30)
theorem v3151_pb_checked : Scalar.distance (sourceCoefficient 40 92 1 1) v3151_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3151_pg : Scalar.QComplex := ((-93086272187982836012003 : Int)/10^30,(167947268315525940961 : Int)/10^30)
theorem v3151_pg_checked : Scalar.distance (sourceCoefficient 40 92 1 2) v3151_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3151_mb : Scalar.QComplex := ((-1150819804255652178668503 : Int)/10^30,(-431475928782706352985399358 : Int)/10^30)
theorem v3151_mb_checked : Scalar.distance (sourceCoefficient 40 92 3 1) v3151_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3151_mg : Scalar.QComplex := ((-93086092596780955497434 : Int)/10^30,(248276466229243280516 : Int)/10^30)
theorem v3151_mg_checked : Scalar.distance (sourceCoefficient 40 92 3 2) v3151_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3151_upper : Scalar.QComplex := ((999993769136058691263791371720 : Int)/10^30,(-3530111762954824255633123837 : Int)/10^30)
theorem v3151_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 92 5) 1) 14) v3151_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3151 : Material (40 : Basis) (92 : Basis) where
  plus := ![v3151_pa,v3151_pb,v3151_pg]
  minus := ![(Primitive.Addresses.material3151 1).one,v3151_mb,v3151_mg]
  upper := v3151_upper
  lower := (Primitive.Addresses.material3151 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3151_pa_checked.trans (by decide +kernel)
    · exact v3151_pb_checked.trans (by decide +kernel)
    · exact v3151_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 92 Primitive.Addresses.material3151
    · exact v3151_mb_checked.trans (by decide +kernel)
    · exact v3151_mg_checked.trans (by decide +kernel)
  upper_error := v3151_upper_checked
  lower_error := reuse_lower_error 40 92 Primitive.Addresses.material3151

def v3152_pa : Scalar.QComplex := ((999998303270594663705733111666 : Int)/10^30,(-1842133527131492604853016716 : Int)/10^30)
theorem v3152_pa_checked : Scalar.distance (sourceCoefficient 40 93 1 0) v3152_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3152_pb : Scalar.QComplex := ((-794839092532066360071395 : Int)/10^30,(-431476726414561126115893795 : Int)/10^30)
theorem v3152_pb_checked : Scalar.distance (sourceCoefficient 40 93 1 1) v3152_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3152_pg : Scalar.QComplex := ((-93086265214221353476980 : Int)/10^30,(171477621017693085761 : Int)/10^30)
theorem v3152_pg_checked : Scalar.distance (sourceCoefficient 40 93 1 2) v3152_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3152_mb : Scalar.QComplex := ((-1167183778482541320968980 : Int)/10^30,(-431475879845717790078366404 : Int)/10^30)
theorem v3152_mb_checked : Scalar.distance (sourceCoefficient 40 93 3 1) v3152_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3152_mg : Scalar.QComplex := ((-93086082576486688825585 : Int)/10^30,(251806811598856696340 : Int)/10^30)
theorem v3152_mg_checked : Scalar.distance (sourceCoefficient 40 93 3 2) v3152_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3152_upper : Scalar.QComplex := ((999993634535239213716160364861 : Int)/10^30,(-3568037135797628839932508133 : Int)/10^30)
theorem v3152_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 93 5) 1) 14) v3152_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3152 : Material (40 : Basis) (93 : Basis) where
  plus := ![v3152_pa,v3152_pb,v3152_pg]
  minus := ![(Primitive.Addresses.material3152 1).one,v3152_mb,v3152_mg]
  upper := v3152_upper
  lower := (Primitive.Addresses.material3152 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3152_pa_checked.trans (by decide +kernel)
    · exact v3152_pb_checked.trans (by decide +kernel)
    · exact v3152_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 93 Primitive.Addresses.material3152
    · exact v3152_mb_checked.trans (by decide +kernel)
    · exact v3152_mg_checked.trans (by decide +kernel)
  upper_error := v3152_upper_checked
  lower_error := reuse_lower_error 40 93 Primitive.Addresses.material3152

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
