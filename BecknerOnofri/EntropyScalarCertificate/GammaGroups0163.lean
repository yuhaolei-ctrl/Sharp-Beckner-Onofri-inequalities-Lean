import BecknerOnofri.EntropyScalarCertificate.Bessel0203
import BecknerOnofri.EntropyScalarCertificate.Bessel0204
import BecknerOnofri.EntropyScalarCertificate.Bessel0205
import BecknerOnofri.EntropyScalarCertificate.Bessel0590
import BecknerOnofri.EntropyScalarCertificate.Bessel0591
import BecknerOnofri.EntropyScalarCertificate.Brackets0081
import BecknerOnofri.EntropyScalarCertificate.Brackets0082
import BecknerOnofri.EntropyScalarCertificate.Logs0163
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1304
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (3387068297806127444555142997410161394123/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3387068297806127444555142997410161394123/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (6801387437169944226207080730314487051531/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6801387437169944226207080730314487051531/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (13575524032782199115317366725134809839777/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (13575524032782199115317366725134809839777/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0081.bracket1304 BracketBatch0081.bracket1305 (13575524032782199115317366725134809839777/10000000000000000000000000000000000000000) (88765294984167772237478441991261196971/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0081.bracket1304 BracketBatch0081.bracket1305
  (13575524032782199115317366725134809839777/10000000000000000000000000000000000000000) (88765294984167772237478441991261196971/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1304
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1305
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (13602774874339888452414161460628974103059/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (13602774874339888452414161460628974103059/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (2731548493692099880273457869426508264489/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2731548493692099880273457869426508264489/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (851891166962512120430670337742547357047/625000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (851891166962512120430670337742547357047/625000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0081.bracket1305 BracketBatch0081.bracket1306 (851891166962512120430670337742547357047/625000000000000000000000000000000000000) (55870562748629749389578631127709562309/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0081.bracket1305 BracketBatch0081.bracket1306
  (851891166962512120430670337742547357047/625000000000000000000000000000000000000) (55870562748629749389578631127709562309/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1305
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1306
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (6828871234230249700683644673566270661221/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6828871234230249700683644673566270661221/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (3428295769665671103557432553054710437387/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3428295769665671103557432553054710437387/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (2737092554712318381559701955935138307199/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2737092554712318381559701955935138307199/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0081.bracket1306 BracketBatch0081.bracket1307 (2737092554712318381559701955935138307199/2000000000000000000000000000000000000000) (225063994098530666636107037088624965501/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0081.bracket1306 BracketBatch0081.bracket1307
  (2737092554712318381559701955935138307199/2000000000000000000000000000000000000000) (225063994098530666636107037088624965501/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1306
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1307
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (2742636615732536882845946042443768349909/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2742636615732536882845946042443768349909/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (13769103954945646276669667487664213930771/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (13769103954945646276669667487664213930771/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (6870571758402082672724849424970763920079/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6870571758402082672724849424970763920079/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0081.bracket1307 BracketBatch0081.bracket1308 (6870571758402082672724849424970763920079/5000000000000000000000000000000000000000) (56664654344905722634809001932056869877/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0081.bracket1307 BracketBatch0081.bracket1308
  (6870571758402082672724849424970763920079/5000000000000000000000000000000000000000) (56664654344905722634809001932056869877/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1307
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1308
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (860568997184102892291854217979013370673/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (860568997184102892291854217979013370673/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (6912756247923272167773148673538199779567/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6912756247923272167773148673538199779567/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (13797308225396095306107982417370306744951/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (13797308225396095306107982417370306744951/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0081.bracket1308 BracketBatch0081.bracket1309 (13797308225396095306107982417370306744951/10000000000000000000000000000000000000000) (28533284249732844172994582471681424467/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0081.bracket1308 BracketBatch0081.bracket1309
  (13797308225396095306107982417370306744951/10000000000000000000000000000000000000000) (28533284249732844172994582471681424467/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1308
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1309
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (13825512495846544335546297347076399559131/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (13825512495846544335546297347076399559131/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (13882416252160320289748005184328668911069/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (13882416252160320289748005184328668911069/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (138539643740034323126471512657025342351/100000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (138539643740034323126471512657025342351/100000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0081.bracket1309 BracketBatch0081.bracket1310 (138539643740034323126471512657025342351/100000000000000000000000000000000000000) (459774239435273245588016370575852726649/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0081.bracket1309 BracketBatch0081.bracket1310
  (138539643740034323126471512657025342351/100000000000000000000000000000000000000) (459774239435273245588016370575852726649/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1309
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1310
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (6941208126080160144874002592164334455533/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6941208126080160144874002592164334455533/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (13939822930767673703487593871582102260789/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (13939822930767673703487593871582102260789/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (5564447836585598798647119811182154234371/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5564447836585598798647119811182154234371/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0081.bracket1310 BracketBatch0081.bracket1311 (5564447836585598798647119811182154234371/4000000000000000000000000000000000000000) (231521312960142315018603590431715681447/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0081.bracket1310 BracketBatch0081.bracket1311
  (5564447836585598798647119811182154234371/4000000000000000000000000000000000000000) (231521312960142315018603590431715681447/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1310
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1311
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0204.rows BesselBatch0204.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (6969911465383836851743796935791051130393/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6969911465383836851743796935791051130393/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (2799548079714946163108923864027042603637/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2799548079714946163108923864027042603637/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (27937563329342404519032213191717315278971/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (27937563329342404519032213191717315278971/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0163.rows ScalarLogs0163.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0081.bracket1311 BracketBatch0082.bracket1312 (27937563329342404519032213191717315278971/20000000000000000000000000000000000000000) (466338029713944950633463525307699058383/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0081.bracket1311 BracketBatch0082.bracket1312
  (27937563329342404519032213191717315278971/20000000000000000000000000000000000000000) (466338029713944950633463525307699058383/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1311
