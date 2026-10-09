import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B132

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3169_pa : Scalar.QComplex := ((999999407800056072916811560915 : Int)/10^30,(-1088301216186673564096637877 : Int)/10^30)
theorem v3169_pa_checked : Scalar.distance (sourceCoefficient 41 54 1 0) v3169_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3169_pb : Scalar.QComplex := ((-469577509116524391714642 : Int)/10^30,(-431477263875633145314037916 : Int)/10^30)
theorem v3169_pb_checked : Scalar.distance (sourceCoefficient 41 54 1 1) v3169_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3169_pg : Scalar.QComplex := ((-93086374598168974868066 : Int)/10^30,(101306074679047316442 : Int)/10^30)
theorem v3169_pg_checked : Scalar.distance (sourceCoefficient 41 54 1 2) v3169_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3169_mb : Scalar.QComplex := ((-841922779981450851401947 : Int)/10^30,(-431476697992686937657169096 : Int)/10^30)
theorem v3169_mb_checked : Scalar.distance (sourceCoefficient 41 54 3 1) v3169_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3169_mg : Scalar.QComplex := ((-93086252515277662697986 : Int)/10^30,(181635385781704954134 : Int)/10^30)
theorem v3169_mg_checked : Scalar.distance (sourceCoefficient 41 54 3 2) v3169_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3169_upper : Scalar.QComplex := ((999996040109237113761331587313 : Int)/10^30,(-2814207853915133850141848105 : Int)/10^30)
theorem v3169_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 54 5) 1) 14) v3169_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3169 : Material (41 : Basis) (54 : Basis) where
  plus := ![v3169_pa,v3169_pb,v3169_pg]
  minus := ![(Primitive.Addresses.material3169 1).one,v3169_mb,v3169_mg]
  upper := v3169_upper
  lower := (Primitive.Addresses.material3169 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3169_pa_checked.trans (by decide +kernel)
    · exact v3169_pb_checked.trans (by decide +kernel)
    · exact v3169_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 54 Primitive.Addresses.material3169
    · exact v3169_mb_checked.trans (by decide +kernel)
    · exact v3169_mg_checked.trans (by decide +kernel)
  upper_error := v3169_upper_checked
  lower_error := reuse_lower_error 41 54 Primitive.Addresses.material3169

def v3170_pa : Scalar.QComplex := ((999999390983888953347378807696 : Int)/10^30,(-1103644803001709299489125740 : Int)/10^30)
theorem v3170_pa_checked : Scalar.distance (sourceCoefficient 41 55 1 0) v3170_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3170_pb : Scalar.QComplex := ((-476197921511690117299297 : Int)/10^30,(-431477256273317807574492359 : Int)/10^30)
theorem v3170_pb_checked : Scalar.distance (sourceCoefficient 41 55 1 1) v3170_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3170_pg : Scalar.QComplex := ((-93086372995433412213032 : Int)/10^30,(102734354353565699909 : Int)/10^30)
theorem v3170_pg_checked : Scalar.distance (sourceCoefficient 41 55 1 2) v3170_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3170_mb : Scalar.QComplex := ((-848543183351078733576055 : Int)/10^30,(-431476684677256705884647567 : Int)/10^30)
theorem v3170_mb_checked : Scalar.distance (sourceCoefficient 41 55 3 1) v3170_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3170_mg : Scalar.QComplex := ((-93086249680001665033883 : Int)/10^30,(183063663541320933131 : Int)/10^30)
theorem v3170_mg_checked : Scalar.distance (sourceCoefficient 41 55 3 2) v3170_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3170_upper : Scalar.QComplex := ((999995996811456156468248922487 : Int)/10^30,(-2829551388854520511243792821 : Int)/10^30)
theorem v3170_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 55 5) 1) 14) v3170_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3170 : Material (41 : Basis) (55 : Basis) where
  plus := ![v3170_pa,v3170_pb,v3170_pg]
  minus := ![(Primitive.Addresses.material3170 1).one,v3170_mb,v3170_mg]
  upper := v3170_upper
  lower := (Primitive.Addresses.material3170 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3170_pa_checked.trans (by decide +kernel)
    · exact v3170_pb_checked.trans (by decide +kernel)
    · exact v3170_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 55 Primitive.Addresses.material3170
    · exact v3170_mb_checked.trans (by decide +kernel)
    · exact v3170_mg_checked.trans (by decide +kernel)
  upper_error := v3170_upper_checked
  lower_error := reuse_lower_error 41 55 Primitive.Addresses.material3170

def v3171_pa : Scalar.QComplex := ((999999386958376091950398027606 : Int)/10^30,(-1107286264701258976167742782 : Int)/10^30)
theorem v3171_pa_checked : Scalar.distance (sourceCoefficient 41 56 1 0) v3171_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3171_pb : Scalar.QComplex := ((-477769130274961412493682 : Int)/10^30,(-431477254449189697435030670 : Int)/10^30)
theorem v3171_pb_checked : Scalar.distance (sourceCoefficient 41 56 1 1) v3171_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3171_pg : Scalar.QComplex := ((-93086372611305524010162 : Int)/10^30,(103073325011600618910 : Int)/10^30)
theorem v3171_pg_checked : Scalar.distance (sourceCoefficient 41 56 1 2) v3171_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3171_mb : Scalar.QComplex := ((-850114389955176795046641 : Int)/10^30,(-431476681497246876864112027 : Int)/10^30)
theorem v3171_mb_checked : Scalar.distance (sourceCoefficient 41 56 3 1) v3171_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3171_mg : Scalar.QComplex := ((-93086249003357508646958 : Int)/10^30,(183402633741656517380 : Int)/10^30)
theorem v3171_mg_checked : Scalar.distance (sourceCoefficient 41 56 3 2) v3171_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3171_upper : Scalar.QComplex := ((999995986501116748001887407975 : Int)/10^30,(-2833192838182870735485501780 : Int)/10^30)
theorem v3171_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 56 5) 1) 14) v3171_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3171 : Material (41 : Basis) (56 : Basis) where
  plus := ![v3171_pa,v3171_pb,v3171_pg]
  minus := ![(Primitive.Addresses.material3171 1).one,v3171_mb,v3171_mg]
  upper := v3171_upper
  lower := (Primitive.Addresses.material3171 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3171_pa_checked.trans (by decide +kernel)
    · exact v3171_pb_checked.trans (by decide +kernel)
    · exact v3171_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 56 Primitive.Addresses.material3171
    · exact v3171_mb_checked.trans (by decide +kernel)
    · exact v3171_mg_checked.trans (by decide +kernel)
  upper_error := v3171_upper_checked
  lower_error := reuse_lower_error 41 56 Primitive.Addresses.material3171

def v3172_pa : Scalar.QComplex := ((999999373847558616032328240845 : Int)/10^30,(-1119064113758034639450824264 : Int)/10^30)
theorem v3172_pa_checked : Scalar.distance (sourceCoefficient 41 57 1 0) v3172_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3172_pb : Scalar.QComplex := ((-482851007034429677928353 : Int)/10^30,(-431477248497037718979356526 : Int)/10^30)
theorem v3172_pb_checked : Scalar.distance (sourceCoefficient 41 57 1 1) v3172_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3172_pg : Scalar.QComplex := ((-93086371359030953388111 : Int)/10^30,(104169682893946534582 : Int)/10^30)
theorem v3172_pg_checked : Scalar.distance (sourceCoefficient 41 57 1 2) v3172_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3172_mb : Scalar.QComplex := ((-855196259685991007256279 : Int)/10^30,(-431476671159666350478383125 : Int)/10^30)
theorem v3172_mb_checked : Scalar.distance (sourceCoefficient 41 57 3 1) v3172_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3172_mg : Scalar.QComplex := ((-93086246804975929965456 : Int)/10^30,(184498990135121733330 : Int)/10^30)
theorem v3172_mg_checked : Scalar.distance (sourceCoefficient 41 57 3 2) v3172_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3172_upper : Scalar.QComplex := ((999995953062819805231486024726 : Int)/10^30,(-2844970647069842192674367509 : Int)/10^30)
theorem v3172_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 57 5) 1) 14) v3172_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3172 : Material (41 : Basis) (57 : Basis) where
  plus := ![v3172_pa,v3172_pb,v3172_pg]
  minus := ![(Primitive.Addresses.material3172 1).one,v3172_mb,v3172_mg]
  upper := v3172_upper
  lower := (Primitive.Addresses.material3172 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3172_pa_checked.trans (by decide +kernel)
    · exact v3172_pb_checked.trans (by decide +kernel)
    · exact v3172_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 57 Primitive.Addresses.material3172
    · exact v3172_mb_checked.trans (by decide +kernel)
    · exact v3172_mg_checked.trans (by decide +kernel)
  upper_error := v3172_upper_checked
  lower_error := reuse_lower_error 41 57 Primitive.Addresses.material3172

def v3173_pa : Scalar.QComplex := ((999999366675703565461249403163 : Int)/10^30,(-1125454660023855890778217482 : Int)/10^30)
theorem v3173_pa_checked : Scalar.distance (sourceCoefficient 41 58 1 0) v3173_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3173_pb : Scalar.QComplex := ((-485608383890516803292021 : Int)/10^30,(-431477245234059859045299048 : Int)/10^30)
theorem v3173_pb_checked : Scalar.distance (sourceCoefficient 41 58 1 1) v3173_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3173_pg : Scalar.QComplex := ((-93086370673254346435639 : Int)/10^30,(104764556008860825442 : Int)/10^30)
theorem v3173_pg_checked : Scalar.distance (sourceCoefficient 41 58 1 2) v3173_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3173_mb : Scalar.QComplex := ((-857953632699577776695296 : Int)/10^30,(-431476665517197666340455306 : Int)/10^30)
theorem v3173_mb_checked : Scalar.distance (sourceCoefficient 41 58 3 1) v3173_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3173_mg : Scalar.QComplex := ((-93086245605850872278449 : Int)/10^30,(185093862436743250895 : Int)/10^30)
theorem v3173_mg_checked : Scalar.distance (sourceCoefficient 41 58 3 2) v3173_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3173_upper : Scalar.QComplex := ((999995934861472327317069368184 : Int)/10^30,(-2851361171439724275680323893 : Int)/10^30)
theorem v3173_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 58 5) 1) 14) v3173_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3173 : Material (41 : Basis) (58 : Basis) where
  plus := ![v3173_pa,v3173_pb,v3173_pg]
  minus := ![(Primitive.Addresses.material3173 1).one,v3173_mb,v3173_mg]
  upper := v3173_upper
  lower := (Primitive.Addresses.material3173 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3173_pa_checked.trans (by decide +kernel)
    · exact v3173_pb_checked.trans (by decide +kernel)
    · exact v3173_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 58 Primitive.Addresses.material3173
    · exact v3173_mb_checked.trans (by decide +kernel)
    · exact v3173_mg_checked.trans (by decide +kernel)
  upper_error := v3173_upper_checked
  lower_error := reuse_lower_error 41 58 Primitive.Addresses.material3173

def v3174_pa : Scalar.QComplex := ((999999346751768342888198576847 : Int)/10^30,(-1143020575746986034850996699 : Int)/10^30)
theorem v3174_pa_checked : Scalar.distance (sourceCoefficient 41 59 1 0) v3174_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3174_pb : Scalar.QComplex := ((-493187681052957318530718 : Int)/10^30,(-431477236143950712224974796 : Int)/10^30)
theorem v3174_pb_checked : Scalar.distance (sourceCoefficient 41 59 1 1) v3174_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3174_pg : Scalar.QComplex := ((-93086368765385861467747 : Int)/10^30,(106399704325826304660 : Int)/10^30)
theorem v3174_pg_checked : Scalar.distance (sourceCoefficient 41 59 1 2) v3174_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3174_mb : Scalar.QComplex := ((-865532919195544776977272 : Int)/10^30,(-431476649886499811869399608 : Int)/10^30)
theorem v3174_mb_checked : Scalar.distance (sourceCoefficient 41 59 3 1) v3174_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3174_mg : Scalar.QComplex := ((-93086242286923744502369 : Int)/10^30,(186729008498463706417 : Int)/10^30)
theorem v3174_mg_checked : Scalar.distance (sourceCoefficient 41 59 3 2) v3174_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3174_upper : Scalar.QComplex := ((999995884620389808408610831816 : Int)/10^30,(-2868927026613581678683170587 : Int)/10^30)
theorem v3174_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 59 5) 1) 14) v3174_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3174 : Material (41 : Basis) (59 : Basis) where
  plus := ![v3174_pa,v3174_pb,v3174_pg]
  minus := ![(Primitive.Addresses.material3174 1).one,v3174_mb,v3174_mg]
  upper := v3174_upper
  lower := (Primitive.Addresses.material3174 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3174_pa_checked.trans (by decide +kernel)
    · exact v3174_pb_checked.trans (by decide +kernel)
    · exact v3174_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 59 Primitive.Addresses.material3174
    · exact v3174_mb_checked.trans (by decide +kernel)
    · exact v3174_mg_checked.trans (by decide +kernel)
  upper_error := v3174_upper_checked
  lower_error := reuse_lower_error 41 59 Primitive.Addresses.material3174

def v3175_pa : Scalar.QComplex := ((999999323384365880850496696077 : Int)/10^30,(-1163284492473609257022894236 : Int)/10^30)
theorem v3175_pa_checked : Scalar.distance (sourceCoefficient 41 60 1 0) v3175_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3175_pb : Scalar.QComplex := ((-501931104821016168285484 : Int)/10^30,(-431477225437156251135461721 : Int)/10^30)
theorem v3175_pb_checked : Scalar.distance (sourceCoefficient 41 60 1 1) v3175_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3175_pg : Scalar.QComplex := ((-93086366522856489674922 : Int)/10^30,(108285999904753974650 : Int)/10^30)
theorem v3175_pg_checked : Scalar.distance (sourceCoefficient 41 60 1 2) v3175_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3175_mb : Scalar.QComplex := ((-874276330468545959878747 : Int)/10^30,(-431476631634528414762373305 : Int)/10^30)
theorem v3175_mb_checked : Scalar.distance (sourceCoefficient 41 60 3 1) v3175_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3175_mg : Scalar.QComplex := ((-93086238416607078690314 : Int)/10^30,(188615301439835476321 : Int)/10^30)
theorem v3175_mg_checked : Scalar.distance (sourceCoefficient 41 60 3 2) v3175_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3175_upper : Scalar.QComplex := ((999995826279340207385474472166 : Int)/10^30,(-2889190872829464528134874722 : Int)/10^30)
theorem v3175_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 60 5) 1) 14) v3175_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3175 : Material (41 : Basis) (60 : Basis) where
  plus := ![v3175_pa,v3175_pb,v3175_pg]
  minus := ![(Primitive.Addresses.material3175 1).one,v3175_mb,v3175_mg]
  upper := v3175_upper
  lower := (Primitive.Addresses.material3175 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3175_pa_checked.trans (by decide +kernel)
    · exact v3175_pb_checked.trans (by decide +kernel)
    · exact v3175_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 60 Primitive.Addresses.material3175
    · exact v3175_mb_checked.trans (by decide +kernel)
    · exact v3175_mg_checked.trans (by decide +kernel)
  upper_error := v3175_upper_checked
  lower_error := reuse_lower_error 41 60 Primitive.Addresses.material3175

def v3176_pa : Scalar.QComplex := ((999999316551125762095698829208 : Int)/10^30,(-1169143824075312346377832572 : Int)/10^30)
theorem v3176_pa_checked : Scalar.distance (sourceCoefficient 41 61 1 0) v3176_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3176_pb : Scalar.QComplex := ((-504459274450119753129437 : Int)/10^30,(-431477222297246612582111192 : Int)/10^30)
theorem v3176_pb_checked : Scalar.distance (sourceCoefficient 41 61 1 1) v3176_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3176_pg : Scalar.QComplex := ((-93086365866115403673365 : Int)/10^30,(108831424138698097006 : Int)/10^30)
theorem v3176_pg_checked : Scalar.distance (sourceCoefficient 41 61 1 2) v3176_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3176_mb : Scalar.QComplex := ((-876804496446695846956402 : Int)/10^30,(-431476626312923419957733115 : Int)/10^30)
theorem v3176_mb_checked : Scalar.distance (sourceCoefficient 41 61 3 1) v3176_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3176_mg : Scalar.QComplex := ((-93086237289189688325301 : Int)/10^30,(189160724903955250563 : Int)/10^30)
theorem v3176_mg_checked : Scalar.distance (sourceCoefficient 41 61 3 2) v3176_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3176_upper : Scalar.QComplex := ((999995809333435475810243812381 : Int)/10^30,(-2895050183910828943922759488 : Int)/10^30)
theorem v3176_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 61 5) 1) 14) v3176_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3176 : Material (41 : Basis) (61 : Basis) where
  plus := ![v3176_pa,v3176_pb,v3176_pg]
  minus := ![(Primitive.Addresses.material3176 1).one,v3176_mb,v3176_mg]
  upper := v3176_upper
  lower := (Primitive.Addresses.material3176 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3176_pa_checked.trans (by decide +kernel)
    · exact v3176_pb_checked.trans (by decide +kernel)
    · exact v3176_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 61 Primitive.Addresses.material3176
    · exact v3176_mb_checked.trans (by decide +kernel)
    · exact v3176_mg_checked.trans (by decide +kernel)
  upper_error := v3176_upper_checked
  lower_error := reuse_lower_error 41 61 Primitive.Addresses.material3176

def v3177_pa : Scalar.QComplex := ((999999306561541052566895420238 : Int)/10^30,(-1177657181457307575556458631 : Int)/10^30)
theorem v3177_pa_checked : Scalar.distance (sourceCoefficient 41 62 1 0) v3177_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3177_pb : Scalar.QComplex := ((-508132596418184730468303 : Int)/10^30,(-431477217699895576784269401 : Int)/10^30)
theorem v3177_pb_checked : Scalar.distance (sourceCoefficient 41 62 1 1) v3177_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3177_pg : Scalar.QComplex := ((-93086364905254585417768 : Int)/10^30,(109623902143858313444 : Int)/10^30)
theorem v3177_pg_checked : Scalar.distance (sourceCoefficient 41 62 1 2) v3177_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3177_mb : Scalar.QComplex := ((-880477813079708289588138 : Int)/10^30,(-431476618545662677803725603 : Int)/10^30)
theorem v3177_mb_checked : Scalar.distance (sourceCoefficient 41 62 3 1) v3177_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3177_mg : Scalar.QComplex := ((-93086235644456401273242 : Int)/10^30,(189953201784860077055 : Int)/10^30)
theorem v3177_mg_checked : Scalar.distance (sourceCoefficient 41 62 3 2) v3177_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3177_upper : Scalar.QComplex := ((999995784650583129019257577863 : Int)/10^30,(-2903563511372061441226118702 : Int)/10^30)
theorem v3177_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 62 5) 1) 14) v3177_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3177 : Material (41 : Basis) (62 : Basis) where
  plus := ![v3177_pa,v3177_pb,v3177_pg]
  minus := ![(Primitive.Addresses.material3177 1).one,v3177_mb,v3177_mg]
  upper := v3177_upper
  lower := (Primitive.Addresses.material3177 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3177_pa_checked.trans (by decide +kernel)
    · exact v3177_pb_checked.trans (by decide +kernel)
    · exact v3177_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 62 Primitive.Addresses.material3177
    · exact v3177_mb_checked.trans (by decide +kernel)
    · exact v3177_mg_checked.trans (by decide +kernel)
  upper_error := v3177_upper_checked
  lower_error := reuse_lower_error 41 62 Primitive.Addresses.material3177

def v3178_pa : Scalar.QComplex := ((999999277053926423155385885336 : Int)/10^30,(-1202452337725975701823539336 : Int)/10^30)
theorem v3178_pa_checked : Scalar.distance (sourceCoefficient 41 63 1 0) v3178_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3178_pb : Scalar.QComplex := ((-518831147799434921915358 : Int)/10^30,(-431477204072540136698088341 : Int)/10^30)
theorem v3178_pb_checked : Scalar.distance (sourceCoefficient 41 63 1 1) v3178_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3178_pg : Scalar.QComplex := ((-93086362061900881611450 : Int)/10^30,(111931994592535289082 : Int)/10^30)
theorem v3178_pg_checked : Scalar.distance (sourceCoefficient 41 63 1 2) v3178_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3178_mb : Scalar.QComplex := ((-891176348717604862354158 : Int)/10^30,(-431476595685944314653149832 : Int)/10^30)
theorem v3178_mb_checked : Scalar.distance (sourceCoefficient 41 63 3 1) v3178_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3178_mg : Scalar.QComplex := ((-93086230809323925594210 : Int)/10^30,(192261290920442562527 : Int)/10^30)
theorem v3178_mg_checked : Scalar.distance (sourceCoefficient 41 63 3 2) v3178_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3178_upper : Scalar.QComplex := ((999995712348822127017697541739 : Int)/10^30,(-2928358579783791008493442983 : Int)/10^30)
theorem v3178_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 63 5) 1) 14) v3178_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3178 : Material (41 : Basis) (63 : Basis) where
  plus := ![v3178_pa,v3178_pb,v3178_pg]
  minus := ![(Primitive.Addresses.material3178 1).one,v3178_mb,v3178_mg]
  upper := v3178_upper
  lower := (Primitive.Addresses.material3178 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3178_pa_checked.trans (by decide +kernel)
    · exact v3178_pb_checked.trans (by decide +kernel)
    · exact v3178_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 63 Primitive.Addresses.material3178
    · exact v3178_mb_checked.trans (by decide +kernel)
    · exact v3178_mg_checked.trans (by decide +kernel)
  upper_error := v3178_upper_checked
  lower_error := reuse_lower_error 41 63 Primitive.Addresses.material3178

def v3179_pa : Scalar.QComplex := ((999999233814396876932594500674 : Int)/10^30,(-1237889582800403235520342824 : Int)/10^30)
theorem v3179_pa_checked : Scalar.distance (sourceCoefficient 41 64 1 0) v3179_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3179_pb : Scalar.QComplex := ((-534121520504004140000198 : Int)/10^30,(-431477183982334441778431219 : Int)/10^30)
theorem v3179_pb_checked : Scalar.distance (sourceCoefficient 41 64 1 1) v3179_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3179_pg : Scalar.QComplex := ((-93086357882276026426200 : Int)/10^30,(115230721011419174033 : Int)/10^30)
theorem v3179_pg_checked : Scalar.distance (sourceCoefficient 41 64 1 2) v3179_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3179_mb : Scalar.QComplex := ((-906466698391926832533627 : Int)/10^30,(-431476562400843109014624856 : Int)/10^30)
theorem v3179_mb_checked : Scalar.distance (sourceCoefficient 41 64 3 1) v3179_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3179_mg : Scalar.QComplex := ((-93086223783048296300281 : Int)/10^30,(195560012504231835774 : Int)/10^30)
theorem v3179_mg_checked : Scalar.distance (sourceCoefficient 41 64 3 2) v3179_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3179_upper : Scalar.QComplex := ((999995607947886824293156549784 : Int)/10^30,(-2963795697451099417751963030 : Int)/10^30)
theorem v3179_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 64 5) 1) 14) v3179_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3179 : Material (41 : Basis) (64 : Basis) where
  plus := ![v3179_pa,v3179_pb,v3179_pg]
  minus := ![(Primitive.Addresses.material3179 1).one,v3179_mb,v3179_mg]
  upper := v3179_upper
  lower := (Primitive.Addresses.material3179 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3179_pa_checked.trans (by decide +kernel)
    · exact v3179_pb_checked.trans (by decide +kernel)
    · exact v3179_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 64 Primitive.Addresses.material3179
    · exact v3179_mb_checked.trans (by decide +kernel)
    · exact v3179_mg_checked.trans (by decide +kernel)
  upper_error := v3179_upper_checked
  lower_error := reuse_lower_error 41 64 Primitive.Addresses.material3179

def v3180_pa : Scalar.QComplex := ((999999188644895711534192153759 : Int)/10^30,(-1273856173309933118190885385 : Int)/10^30)
theorem v3180_pa_checked : Scalar.distance (sourceCoefficient 41 65 1 0) v3180_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3180_pb : Scalar.QComplex := ((-549640293496383703988913 : Int)/10^30,(-431477162853295676242941138 : Int)/10^30)
theorem v3180_pb_checked : Scalar.distance (sourceCoefficient 41 65 1 1) v3180_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3180_pg : Scalar.QComplex := ((-93086353500765802621089 : Int)/10^30,(118578722267312793286 : Int)/10^30)
theorem v3180_pg_checked : Scalar.distance (sourceCoefficient 41 65 1 2) v3180_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3180_mb : Scalar.QComplex := ((-921985447372549130419570 : Int)/10^30,(-431476527879810057952067846 : Int)/10^30)
theorem v3180_mb_checked : Scalar.distance (sourceCoefficient 41 65 3 1) v3180_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3180_mg : Scalar.QComplex := ((-93086216512365408474516 : Int)/10^30,(198908008732465588992 : Int)/10^30)
theorem v3180_mg_checked : Scalar.distance (sourceCoefficient 41 65 3 2) v3180_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3180_upper : Scalar.QComplex := ((999995500703380577715113072929 : Int)/10^30,(-2999762156434156402642570346 : Int)/10^30)
theorem v3180_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 65 5) 1) 14) v3180_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3180 : Material (41 : Basis) (65 : Basis) where
  plus := ![v3180_pa,v3180_pb,v3180_pg]
  minus := ![(Primitive.Addresses.material3180 1).one,v3180_mb,v3180_mg]
  upper := v3180_upper
  lower := (Primitive.Addresses.material3180 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3180_pa_checked.trans (by decide +kernel)
    · exact v3180_pb_checked.trans (by decide +kernel)
    · exact v3180_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 65 Primitive.Addresses.material3180
    · exact v3180_mb_checked.trans (by decide +kernel)
    · exact v3180_mg_checked.trans (by decide +kernel)
  upper_error := v3180_upper_checked
  lower_error := reuse_lower_error 41 65 Primitive.Addresses.material3180

def v3181_pa : Scalar.QComplex := ((999999166086204405247559107086 : Int)/10^30,(-1291443725362157001230585565 : Int)/10^30)
theorem v3181_pa_checked : Scalar.distance (sourceCoefficient 41 66 1 0) v3181_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3181_pb : Scalar.QComplex := ((-557228925591702776191598 : Int)/10^30,(-431477152250325076511065858 : Int)/10^30)
theorem v3181_pb_checked : Scalar.distance (sourceCoefficient 41 66 1 1) v3181_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3181_pg : Scalar.QComplex := ((-93086351307075864062538 : Int)/10^30,(120215884562065132520 : Int)/10^30)
theorem v3181_pg_checked : Scalar.distance (sourceCoefficient 41 66 1 2) v3181_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3181_mb : Scalar.QComplex := ((-929574067492387568415152 : Int)/10^30,(-431476510728195687232496328 : Int)/10^30)
theorem v3181_mb_checked : Scalar.distance (sourceCoefficient 41 66 3 1) v3181_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3181_mg : Scalar.QComplex := ((-93086212905878961408299 : Int)/10^30,(200545168524571967027 : Int)/10^30)
theorem v3181_mg_checked : Scalar.distance (sourceCoefficient 41 66 3 2) v3181_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3181_upper : Scalar.QComplex := ((999995447790203558069407938281 : Int)/10^30,(-3017349643357532796724090317 : Int)/10^30)
theorem v3181_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 66 5) 1) 14) v3181_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3181 : Material (41 : Basis) (66 : Basis) where
  plus := ![v3181_pa,v3181_pb,v3181_pg]
  minus := ![(Primitive.Addresses.material3181 1).one,v3181_mb,v3181_mg]
  upper := v3181_upper
  lower := (Primitive.Addresses.material3181 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3181_pa_checked.trans (by decide +kernel)
    · exact v3181_pb_checked.trans (by decide +kernel)
    · exact v3181_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 66 Primitive.Addresses.material3181
    · exact v3181_mb_checked.trans (by decide +kernel)
    · exact v3181_mg_checked.trans (by decide +kernel)
  upper_error := v3181_upper_checked
  lower_error := reuse_lower_error 41 66 Primitive.Addresses.material3181

def v3182_pa : Scalar.QComplex := ((999999127530828942235524878905 : Int)/10^30,(-1320960855178182221375421809 : Int)/10^30)
theorem v3182_pa_checked : Scalar.distance (sourceCoefficient 41 67 1 0) v3182_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3182_pb : Scalar.QComplex := ((-569964901268516368504142 : Int)/10^30,(-431477134055444718323915848 : Int)/10^30)
theorem v3182_pb_checked : Scalar.distance (sourceCoefficient 41 67 1 1) v3182_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3182_pg : Scalar.QComplex := ((-93086347549914177963597 : Int)/10^30,(122963528546835941481 : Int)/10^30)
theorem v3182_pg_checked : Scalar.distance (sourceCoefficient 41 67 1 2) v3182_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3182_mb : Scalar.QComplex := ((-942310022725653071282855 : Int)/10^30,(-431476481542748701791909661 : Int)/10^30)
theorem v3182_mb_checked : Scalar.distance (sourceCoefficient 41 67 3 1) v3182_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3182_mg : Scalar.QComplex := ((-93086206777625664706440 : Int)/10^30,(203292808244008028103 : Int)/10^30)
theorem v3182_mg_checked : Scalar.distance (sourceCoefficient 41 67 3 2) v3182_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3182_upper : Scalar.QComplex := ((999995358290997229399857628840 : Int)/10^30,(-3046866662668180148714465588 : Int)/10^30)
theorem v3182_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 67 5) 1) 14) v3182_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3182 : Material (41 : Basis) (67 : Basis) where
  plus := ![v3182_pa,v3182_pb,v3182_pg]
  minus := ![(Primitive.Addresses.material3182 1).one,v3182_mb,v3182_mg]
  upper := v3182_upper
  lower := (Primitive.Addresses.material3182 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3182_pa_checked.trans (by decide +kernel)
    · exact v3182_pb_checked.trans (by decide +kernel)
    · exact v3182_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 67 Primitive.Addresses.material3182
    · exact v3182_mb_checked.trans (by decide +kernel)
    · exact v3182_mg_checked.trans (by decide +kernel)
  upper_error := v3182_upper_checked
  lower_error := reuse_lower_error 41 67 Primitive.Addresses.material3182

def v3183_pa : Scalar.QComplex := ((999999061386805023304918856349 : Int)/10^30,(-1370118793739674376680404948 : Int)/10^30)
theorem v3183_pa_checked : Scalar.distance (sourceCoefficient 41 68 1 0) v3183_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3183_pb : Scalar.QComplex := ((-591175442282020528026212 : Int)/10^30,(-431477102641126461061677259 : Int)/10^30)
theorem v3183_pb_checked : Scalar.distance (sourceCoefficient 41 68 1 1) v3183_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3183_pg : Scalar.QComplex := ((-93086341082715457207779 : Int)/10^30,(127539465068114789912 : Int)/10^30)
theorem v3183_pg_checked : Scalar.distance (sourceCoefficient 41 68 1 2) v3183_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3183_mb : Scalar.QComplex := ((-963520528732361634220535 : Int)/10^30,(-431476431824700534167290404 : Int)/10^30)
theorem v3183_mb_checked : Scalar.distance (sourceCoefficient 41 68 3 1) v3183_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3183_mg : Scalar.QComplex := ((-93086196361602226651030 : Int)/10^30,(207868737480555354836 : Int)/10^30)
theorem v3183_mg_checked : Scalar.distance (sourceCoefficient 41 68 3 2) v3183_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3183_upper : Scalar.QComplex := ((999995207304929440437619263906 : Int)/10^30,(-3096024413856112568678674775 : Int)/10^30)
theorem v3183_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 68 5) 1) 14) v3183_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3183 : Material (41 : Basis) (68 : Basis) where
  plus := ![v3183_pa,v3183_pb,v3183_pg]
  minus := ![(Primitive.Addresses.material3183 1).one,v3183_mb,v3183_mg]
  upper := v3183_upper
  lower := (Primitive.Addresses.material3183 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3183_pa_checked.trans (by decide +kernel)
    · exact v3183_pb_checked.trans (by decide +kernel)
    · exact v3183_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 68 Primitive.Addresses.material3183
    · exact v3183_mb_checked.trans (by decide +kernel)
    · exact v3183_mg_checked.trans (by decide +kernel)
  upper_error := v3183_upper_checked
  lower_error := reuse_lower_error 41 68 Primitive.Addresses.material3183

def v3184_pa : Scalar.QComplex := ((999999031509708852105493142349 : Int)/10^30,(-1391754160878402032299383238 : Int)/10^30)
theorem v3184_pa_checked : Scalar.distance (sourceCoefficient 41 69 1 0) v3184_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3184_pb : Scalar.QComplex := ((-600510614657598683745541 : Int)/10^30,(-431477088374493024894519003 : Int)/10^30)
theorem v3184_pb_checked : Scalar.distance (sourceCoefficient 41 69 1 1) v3184_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3184_pg : Scalar.QComplex := ((-93086338153206369846865 : Int)/10^30,(129553423916892159663 : Int)/10^30)
theorem v3184_pg_checked : Scalar.distance (sourceCoefficient 41 69 1 2) v3184_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3184_mb : Scalar.QComplex := ((-972855685320566365963489 : Int)/10^30,(-431476409502239090552138359 : Int)/10^30)
theorem v3184_mb_checked : Scalar.distance (sourceCoefficient 41 69 3 1) v3184_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3184_mg : Scalar.QComplex := ((-93086191694138448924772 : Int)/10^30,(209882693051409400521 : Int)/10^30)
theorem v3184_mg_checked : Scalar.distance (sourceCoefficient 41 69 3 2) v3184_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3184_upper : Scalar.QComplex := ((999995140087196831394098170595 : Int)/10^30,(-3117659697206344777417100701 : Int)/10^30)
theorem v3184_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 69 5) 1) 14) v3184_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3184 : Material (41 : Basis) (69 : Basis) where
  plus := ![v3184_pa,v3184_pb,v3184_pg]
  minus := ![(Primitive.Addresses.material3184 1).one,v3184_mb,v3184_mg]
  upper := v3184_upper
  lower := (Primitive.Addresses.material3184 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3184_pa_checked.trans (by decide +kernel)
    · exact v3184_pb_checked.trans (by decide +kernel)
    · exact v3184_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 69 Primitive.Addresses.material3184
    · exact v3184_mb_checked.trans (by decide +kernel)
    · exact v3184_mg_checked.trans (by decide +kernel)
  upper_error := v3184_upper_checked
  lower_error := reuse_lower_error 41 69 Primitive.Addresses.material3184

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
