module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0167
public import BecknerOnofri.EntropyScalarCertificate.Bessel0168
public import BecknerOnofri.EntropyScalarCertificate.Bessel0572
public import BecknerOnofri.EntropyScalarCertificate.Bessel0573
public import BecknerOnofri.EntropyScalarCertificate.Brackets0067
public import BecknerOnofri.EntropyScalarCertificate.Logs0134
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1072
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (6699627428249844811981537004597272325313/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6699627428249844811981537004597272325313/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (1343506475001134305688493081621841069577/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1343506475001134305688493081621841069577/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (6708579901627758170212001206353238836599/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6708579901627758170212001206353238836599/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨7,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨15,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0067.bracket1072 BracketBatch0067.bracket1073 (6708579901627758170212001206353238836599/10000000000000000000000000000000000000000) (5301570311980588501194728985073690939/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0067.bracket1072 BracketBatch0067.bracket1073
  (6708579901627758170212001206353238836599/10000000000000000000000000000000000000000) (5301570311980588501194728985073690939/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1072
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1073
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (3358766187502835764221232704054602673941/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3358766187502835764221232704054602673941/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (6735485653093952945415946012763346546031/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6735485653093952945415946012763346546031/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (13453018028099624473858411420872551893913/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (13453018028099624473858411420872551893913/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨23,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨31,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0067.bracket1073 BracketBatch0067.bracket1074 (13453018028099624473858411420872551893913/20000000000000000000000000000000000000000) (42747159935970107866314090403499207951/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0067.bracket1073 BracketBatch0067.bracket1074
  (13453018028099624473858411420872551893913/20000000000000000000000000000000000000000) (42747159935970107866314090403499207951/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1073
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1074
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (1683871413273488236353986503190836636507/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1683871413273488236353986503190836636507/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (337674379248158312330127723259137921819/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (337674379248158312330127723259137921819/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (1686121654757139899002312559743263122801/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1686121654757139899002312559743263122801/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨39,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨47,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0067.bracket1074 BracketBatch0067.bracket1075 (1686121654757139899002312559743263122801/2500000000000000000000000000000000000000) (86167875209973465840741860794060678029/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0067.bracket1074 BracketBatch0067.bracket1075
  (1686121654757139899002312559743263122801/2500000000000000000000000000000000000000) (86167875209973465840741860794060678029/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1074
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1075
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (6753487584963166246602554465182758436377/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6753487584963166246602554465182758436377/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (6771538495953825621741919654066942794251/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6771538495953825621741919654066942794251/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (3381256520229247967086118529812425307657/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3381256520229247967086118529812425307657/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨55,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨63,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0067.bracket1075 BracketBatch0067.bracket1076 (3381256520229247967086118529812425307657/5000000000000000000000000000000000000000) (43422908001049302533112490824180354129/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0067.bracket1075 BracketBatch0067.bracket1076
  (3381256520229247967086118529812425307657/5000000000000000000000000000000000000000) (43422908001049302533112490824180354129/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1075
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1076
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (846442311994228202717739956758367849281/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (846442311994228202717739956758367849281/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (3394819357166266138545735013485285087603/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3394819357166266138545735013485285087603/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (6780588605143178949416694840518756484727/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6780588605143178949416694840518756484727/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨71,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨79,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0067.bracket1076 BracketBatch0067.bracket1077 (6780588605143178949416694840518756484727/10000000000000000000000000000000000000000) (87528167406946414573555567900446958027/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0067.bracket1076 BracketBatch0067.bracket1077
  (6780588605143178949416694840518756484727/10000000000000000000000000000000000000000) (87528167406946414573555567900446958027/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1076
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1077
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (6789638714332532277091470026970570175203/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6789638714332532277091470026970570175203/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (136155771426530227096731503760193629611/200000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (136155771426530227096731503760193629611/200000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (13597427285659043631928045214980251655753/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (13597427285659043631928045214980251655753/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨87,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨95,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0067.bracket1077 BracketBatch0067.bracket1078 (13597427285659043631928045214980251655753/20000000000000000000000000000000000000000) (22053738686767726346626130087404211451/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0067.bracket1077 BracketBatch0067.bracket1078
  (13597427285659043631928045214980251655753/20000000000000000000000000000000000000000) (22053738686767726346626130087404211451/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1077
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1078
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (6807788571326511354836575188009681480547/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6807788571326511354836575188009681480547/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (273039536046345757930809357783444600589/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (273039536046345757930809357783444600589/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (1704222121560644412888351141574474561909/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1704222121560644412888351141574474561909/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨103,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨111,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0067.bracket1078 BracketBatch0067.bracket1079 (1704222121560644412888351141574474561909/2500000000000000000000000000000000000000) (2778318859705413274284452132531156201/312500000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0067.bracket1078 BracketBatch0067.bracket1079
  (1704222121560644412888351141574474561909/2500000000000000000000000000000000000000) (2778318859705413274284452132531156201/312500000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1078
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1079
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (3412994200579321974135116972293057507361/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3412994200579321974135116972293057507361/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0168.rows BesselBatch0168.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (3422119270541501278561612051224150726097/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3422119270541501278561612051224150726097/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (3417556735560411626348364511758604116729/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3417556735560411626348364511758604116729/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨119,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0134.rows ScalarLogs0134.accepted ⟨127,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0067.bracket1079 BracketBatch0067.bracket1080 (3417556735560411626348364511758604116729/5000000000000000000000000000000000000000) (11200242419093493049906709389221584299/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0067.bracket1079 BracketBatch0067.bracket1080
  (3417556735560411626348364511758604116729/5000000000000000000000000000000000000000) (11200242419093493049906709389221584299/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1079
