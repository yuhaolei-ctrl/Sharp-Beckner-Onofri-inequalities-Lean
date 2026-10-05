import BecknerOnofri.EntropyScalarCertificate.Bessel0075
import BecknerOnofri.EntropyScalarCertificate.Bessel0076
import BecknerOnofri.EntropyScalarCertificate.Bessel0526
import BecknerOnofri.EntropyScalarCertificate.Bessel0527
import BecknerOnofri.EntropyScalarCertificate.Brackets0030
import BecknerOnofri.EntropyScalarCertificate.Logs0060
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0480
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (385771083020266094489106755164860522659/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (385771083020266094489106755164860522659/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (1545156523989819568998904839896647327349/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1545156523989819568998904839896647327349/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (617648171214176789391066372111217883597/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (617648171214176789391066372111217883597/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0030.bracket0480 BracketBatch0030.bracket0481 (617648171214176789391066372111217883597/4000000000000000000000000000000000000000) (106228718626848465865837875438954437/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0030.bracket0480 BracketBatch0030.bracket0481
  (617648171214176789391066372111217883597/4000000000000000000000000000000000000000) (106228718626848465865837875438954437/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0480
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0481
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (772578261994909784499452419948323663673/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (772578261994909784499452419948323663673/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (193403613947771834071471614003432525897/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (193403613947771834071471614003432525897/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (1546192717785997120785338875962053767261/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1546192717785997120785338875962053767261/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0030.bracket0481 BracketBatch0030.bracket0482 (1546192717785997120785338875962053767261/10000000000000000000000000000000000000000) (213580566508145796480014596083075501/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0030.bracket0481 BracketBatch0030.bracket0482
  (1546192717785997120785338875962053767261/10000000000000000000000000000000000000000) (213580566508145796480014596083075501/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0481
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0482
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (1547228911582174672571772912027460207173/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1547228911582174672571772912027460207173/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (309860299029732872406112824919529621511/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (309860299029732872406112824919529621511/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (387066300841354879325292129578138539341/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (387066300841354879325292129578138539341/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0030.bracket0482 BracketBatch0030.bracket0483 (387066300841354879325292129578138539341/2500000000000000000000000000000000000000) (429416319753328527167829411303856559/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0030.bracket0482 BracketBatch0030.bracket0483
  (387066300841354879325292129578138539341/2500000000000000000000000000000000000000) (429416319753328527167829411303856559/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0482
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0483
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (48415671723395761313455128893676503361/312500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (48415671723395761313455128893676503361/312500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (310274854995993272107162871747022020803/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (310274854995993272107162871747022020803/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (3100675770128630722566378483332758211567/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3100675770128630722566378483332758211567/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0030.bracket0483 BracketBatch0030.bracket0484 (3100675770128630722566378483332758211567/20000000000000000000000000000000000000000) (86336091736791575551573941788508479/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0030.bracket0483 BracketBatch0030.bracket0484
  (3100675770128630722566378483332758211567/20000000000000000000000000000000000000000) (86336091736791575551573941788508479/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0483
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0484
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (387843568744991590133953589683777526003/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (387843568744991590133953589683777526003/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (31068945027338033746114331881815655633/200000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (31068945027338033746114331881815655633/200000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (1552410763173434023920765476412946442831/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1552410763173434023920765476412946442831/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0030.bracket0484 BracketBatch0030.bracket0485 (1552410763173434023920765476412946442831/10000000000000000000000000000000000000000) (86790714761604708850578560841379689/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0030.bracket0484 BracketBatch0030.bracket0485
  (1552410763173434023920765476412946442831/10000000000000000000000000000000000000000) (86790714761604708850578560841379689/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0484
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0485
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (1553447251366901687305716594090782781647/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1553447251366901687305716594090782781647/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (1555520424600434904127480647799284856789/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1555520424600434904127480647799284856789/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (777241918991834147858299310472516909609/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (777241918991834147858299310472516909609/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0030.bracket0485 BracketBatch0030.bracket0486 (777241918991834147858299310472516909609/5000000000000000000000000000000000000000) (218117844579886298126645421720955569/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0030.bracket0485 BracketBatch0030.bracket0486
  (777241918991834147858299310472516909609/5000000000000000000000000000000000000000) (218117844579886298126645421720955569/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0485
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0486
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (777760212300217452063740323899642428393/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (777760212300217452063740323899642428393/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (194699224371459295265990648214879023617/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (194699224371459295265990648214879023617/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (1556557109786054633127702916759158522861/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1556557109786054633127702916759158522861/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0030.bracket0486 BracketBatch0030.bracket0487 (1556557109786054633127702916759158522861/10000000000000000000000000000000000000000) (6851981700122934003960554853399157/156250000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0030.bracket0486 BracketBatch0030.bracket0487
  (1556557109786054633127702916759158522861/10000000000000000000000000000000000000000) (6851981700122934003960554853399157/156250000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0486
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0487
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (1557593794971674362127925185719032188933/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1557593794971674362127925185719032188933/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (779833681385936224401914757926321736449/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (779833681385936224401914757926321736449/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (3117261157743546810931754701571675661831/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3117261157743546810931754701571675661831/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0060.rows ScalarLogs0060.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0030.bracket0487 BracketBatch0030.bracket0488 (3117261157743546810931754701571675661831/20000000000000000000000000000000000000000) (11020675421385000576682442753215171/250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0030.bracket0487 BracketBatch0030.bracket0488
  (3117261157743546810931754701571675661831/20000000000000000000000000000000000000000) (11020675421385000576682442753215171/250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0487
