import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceCurrentPrincipal
import Mathlib.Topology.Instances.Matrix

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumMixedEffective
open PreparationVacuumOriginalGreenFeedback PreparationVacuumMixedPrincipal
open scoped Matrix BigOperators Topology

def blockIndices : List (Fin 289) := [9,10,15,16,19,20,21,22,27,28,31,32,33,34,39,40,43,44,45,46,51,52,55,56,57,58,59,60,61,62,63,64,65,66,67,69,70,72,73,75,76,79,80,82,83,85,86]
def complementIndices : List (Fin 289) := [9,10,15,16,19,20,21,22,27,28,31,32,33,34,39,40,43,44,45,46,51,52,55,56,57,58,59,60,61,62,63,64,65,66,67,69,70,72,73,75,76,79,80,82,86]
def blockFlag (i : Fin 289) : Bool:=blockIndices.contains i
def complementFlag (i : Fin 289) : Bool:=complementIndices.contains i
def blockProjection : Matrix (Fin 289) (Fin 289) ℂ:=projectionMatrix blockFlag
def complementProjection : Matrix (Fin 289) (Fin 289) ℂ:=projectionMatrix complementFlag

def selectedRows (flag : Fin 289→Bool) (terms : List SourceTerm) : List SourceTerm:=
  terms.filter (fun a=>flag a.row)

private theorem term_left (flag : Fin 289→Bool) (a : SourceTerm) (p : Fin 4→ℂ) :
    projectionMatrix flag*a.matrix p=(if flag a.row then a.matrix p else 0) :=by
  ext i j
  simp only [projectionMatrix,Matrix.diagonal_mul,SourceTerm.matrix,Matrix.single_apply ]
  by_cases h : a.row=i
  · subst i
    split_ifs <;> simp_all
  · split_ifs <;> simp_all

theorem selectedRows_generated (flag : Fin 289→Bool) (terms : List SourceTerm) (p : Fin 4→ℂ) :
    sourceMatrix (selectedRows flag terms) p=projectionMatrix flag*sourceMatrix terms p :=by
  induction terms with
  | nil=>simp [selectedRows,sourceMatrix]
  | cons a rest ih=>
    simp only [selectedRows,List.filter_cons] at ih ⊢
    split_ifs with h
    · rw [sourceMatrix_cons,ih,sourceMatrix_cons,mul_add,term_left,if_pos h]
    · rw [ih,sourceMatrix_cons,mul_add,term_left,if_neg h,zero_add]

def complementOriginTerms : List SourceTerm:=selectedRows complementFlag
  (columnTerms complementFlag (originTerms activeTerms))

private def complementInverseTermsAtoms : List SourceAtom := [
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-125/1632:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨(-75/272:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨(75/272:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨(185/2448:ℚ),0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,(-125/272:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,(125/272:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-44167/448800:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(24583/448800:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-3/275:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(6/275:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,(-1341/5984:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,(-1409/5984:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,(1341/5984:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,(1409/5984:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨(-185/2448:ℚ),0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-18/275:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(3/275:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,(3/88:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,(-3/88:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-6/275:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,(5/88:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,(-5/88:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-1/32:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(1/48:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨(-5/144:ℚ),0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨(-5/72:ℚ),0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-1/480:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(1/480:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,(1/80:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-6077/328032:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(38377/328032:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(85/4824:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-305/4824:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(1045/18224:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,(71/272:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨(-2495/20502:ℚ),0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨(-355/2448:ℚ),0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨(-445/9648:ℚ),0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-4037/328032:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(175/4824:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-155/4824:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-2965/54672:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,(-71/272:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨(5/144:ℚ),0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨(4565/41004:ℚ),0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨(355/2448:ℚ),0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨(115/3216:ℚ),0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(65/402:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-5/603:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(5/536:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨(-25/804:ℚ),0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(95/1206:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(25/1608:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨(-125/2412:ℚ),0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-1/96:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨(5/72:ℚ),0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-4961/109344:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨(3185/27336:ℚ),0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨(395/9648:ℚ),0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(4699/96480:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(5101/96480:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(65/2412:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-115/2412:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨(-25/9648:ℚ),0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,(-1/80:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨(-25/1608:ℚ),0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨(-125/4824:ℚ),0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(1/100:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨(-1/12:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨(1/48:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨(-1/48:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-6877/36720:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨(355/408:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-5/216:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(5/864:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-5/864:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨(-355/408:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨(355/816:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨(-355/816:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-390215/7216704:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-103495/2405568:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(227525/7216704:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(398375/7216704:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-15925/82008:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-25/136:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-25/2412:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-1775/7344:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-25/432:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-1975/28944:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-25/108:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(25/136:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(25/432:ℚ)⟩⟩)]
private def complementInverseTermsCodes : List ℕ := [
  240120,242881,242974,243434,244815,246656,246841,266800,268365,268458,270114,271219,272324,272508,400206,400299,400576,400669,
  404619,404994,405179,405548,405733,426795,426886,427164,427257,431218,431585,431768,432135,432318,506560,506652,506935,507028,
  511353,511538,511906,512089,533149,533241,533524,533619,537944,538129,538497,538680,560302,561499,563984,565641,586986,587998,
  589654,589747,590208,590388,718797,720389,720482,720759,720852,722141,723246,723788,724351,724536,724905,745386,746978,747078,
  747355,747448,748737,749842,750395,750948,751133,751502,826743,826843,827127,827220,828509,830718,831270,853332,853432,853716,
  853811,855100,857309,857861,879454,880466,882122,882215,882676,883132,905947,907174,909628,911315,1037761,1040549,1040642,1040919,
  1041012,1041105,1042486,1042936,1044327,1044521,1044881,1064350,1067138,1067238,1067515,1067608,1067701,1069082,1069543,1070924,1071100,1071478,
  1146903,1147003,1147287,1147380,1147473,1150694,1151246,1173492,1173592,1173876,1173971,1174064,1177285,1177837,1197290,1200081,1200181,1200465,
  1200560,1200656,1202022,1202464,1203877,1204040,1204430,1223970,1225565,1225665,1225949,1226044,1227336,1228426,1228960,1229545,1229717,1230098,
  1358038,1359050,1360739,1360832,1361109,1361202,1361260,1362084,1362215,1362399,1362767,1362951,1384627,1385639,1387328,1387419,1387697,1387790,
  1387884,1388691,1388803,1388987,1389355,1389539,1467093,1467185,1467447,1467540,1468569,1468753,1469121,1469305,1493682,1493774,1494036,1494131,
  1495158,1495342,1495710,1495894,1517568,1518580,1520236,1520364,1520827,1521012,1521288,1521656,1521749,1521934,1522301,1522486,1543027,1544622,
  1544722,1546378,1547511,1548616,1548800,1570740,1574004,1574193,1574469,1574837,1574930,1575115,1575482,1575667,1596111,1598902,1599002,1599462,
  1600871,1602712,1602900,1623824,1625020,1651516,1653768,1653957,1654233,1654601,1654694,1654879,1655246,1655431,1676427,1676530,1680911,1681285,
  1681469,1681838,1682022,1704140,1704251,1705888,1731832,1731943,1732384,1759524,1759635,1760120,1760309,1760585,1760953,1761046,1761231,1761598,
  1761783,1782786,1782881,1783161,1783256,1786151,1786243,1786521,1786614,1786709,1786898,1787174,1787269,1787542,1787639,1787824,1788193,1788378,
  1835963,1836056,1836338,1836433,1839327,1839419,1839697,1839790,1839886,1840075,1840351,1840445,1840719,1840816,1840999,1841370,1841553,1862084,
  1863679,1863780,1864062,1864157,1865449,1866568,1867683,1867868,1868237,1915260,1916856,1916957,1918613,1919744,1920860,1921046,1921415,1942316,
  1942407,1942690,1942785,1945679,1945771,1946049,1946142,1946237,1946426,1946702,1946798,1947070,1947169,1947354,1947719,1947904,1995493,1995582,
  1995865,1995960,1998855,1998947,1999225,1999318,1999414,1999603,1999879,1999974,2000247,2000346,2000529,2000896,2001079,2023209,2023310,2023590,
  2023685,2024978,2027213,2027399,2027768,2102409,2103635,2107809,2127872,2130663,2130764,2131046,2131141,2131237,2132632,2134483,2134674,2135037,
  2181049,2183849,2183932,2184392,2185812,2187666,2187846,2188219,2290193,2290294,2290574,2290669,2290766,2294013,2294203,2294568]
def complementInverseTerms : List SourceTerm := decodeTerms complementInverseTermsAtoms complementInverseTermsCodes

def complementInverse : Matrix (Fin 289) (Fin 289) ℂ:=sourceMatrix complementInverseTerms 0

theorem complementOrigin_generated : sourceMatrix complementOriginTerms 0=
    complementProjection*activeKernel 0*complementProjection :=by
  rw [complementOriginTerms,selectedRows_generated,columnTerms_value,originTerms_generated]
  simp only [mul_assoc]
  rfl

private theorem inverse_left_certificate :
    fastNormalizeTerms (productTerms complementInverseTerms complementOriginTerms++
      negativeTerms (projectionTerms complementFlag))=[] :=by decide +kernel
private theorem inverse_right_certificate :
    fastNormalizeTerms (productTerms complementOriginTerms complementInverseTerms++
      negativeTerms (projectionTerms complementFlag))=[] :=by decide +kernel
private theorem inverse_left_support_certificate :
    fastNormalizeTerms (productTerms (projectionTerms complementFlag) complementInverseTerms++
      negativeTerms complementInverseTerms)=[] :=by decide +kernel
private theorem inverse_right_support_certificate :
    fastNormalizeTerms (productTerms complementInverseTerms (projectionTerms complementFlag)++
      negativeTerms complementInverseTerms)=[] :=by decide +kernel

theorem complementInverse_left : complementInverse*(complementProjection*activeKernel 0*complementProjection)=complementProjection :=by
  have h:=normalization_equal _ _ inverse_left_certificate 0
  rw [productTerms_value,complementOrigin_generated,projectionTerms_value] at h
  exact h

theorem complementInverse_right : (complementProjection*activeKernel 0*complementProjection)*complementInverse=complementProjection :=by
  have h:=normalization_equal _ _ inverse_right_certificate 0
  rw [productTerms_value,complementOrigin_generated,projectionTerms_value] at h
  exact h

theorem complementInverse_left_support : complementProjection*complementInverse=complementInverse :=by
  have h:=normalization_equal _ _ inverse_left_support_certificate 0
  rw [productTerms_value,projectionTerms_value] at h
  exact h

theorem complementInverse_right_support : complementInverse*complementProjection=complementInverse :=by
  have h:=normalization_equal _ _ inverse_right_support_certificate 0
  rw [productTerms_value,projectionTerms_value] at h
  exact h

theorem complementProjection_square : complementProjection*complementProjection=complementProjection :=by
  rw [complementProjection,projectionMatrix,Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> norm_num

def complementKernel (p : Fin 4→ℂ) : Matrix (Fin 289) (Fin 289) ℂ:=
  complementProjection*activeKernel p*complementProjection+(1-complementProjection)
def complementOriginInverse : Matrix (Fin 289) (Fin 289) ℂ:=complementInverse+(1-complementProjection)

private theorem padded_inverse {R : Type*} [Ring R] (K B Q : R)
    (pair : K*B=Q) (support : K*Q=K) (read : Q*B=B) (square : Q*Q=Q) :
    (K+(1-Q))*(B+(1-Q))=1 :=by
  calc
    _=K*B+K-K*Q+B-Q*B+1-Q-Q+Q*Q:=by noncomm_ring
    _=1:=by rw [pair,support,read,square];noncomm_ring

theorem complementOriginInverse_right : complementKernel 0*complementOriginInverse=1 :=by
  apply padded_inverse _ _ _ complementInverse_right _ complementInverse_left_support complementProjection_square
  rw [mul_assoc,complementProjection_square]

theorem complementOriginInverse_left : complementOriginInverse*complementKernel 0=1 :=by
  apply padded_inverse _ _ _ complementInverse_left complementInverse_right_support _ complementProjection_square
  simp only [←mul_assoc,complementProjection_square]

theorem complementOrigin_determinant : (complementKernel 0).det≠0 :=by
  have h:=congrArg Matrix.det complementOriginInverse_right
  rw [Matrix.det_mul,Matrix.det_one] at h
  intro zero
  rw [zero,zero_mul] at h
  exact zero_ne_one h

end LowEnergy.PreparationVacuumMixedEffective
