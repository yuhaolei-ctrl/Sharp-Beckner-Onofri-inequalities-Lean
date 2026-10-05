import BecknerOnofri.EntropyScalarCertificate.Bessel0086
import BecknerOnofri.EntropyScalarCertificate.Bessel0087
import BecknerOnofri.EntropyScalarCertificate.Bessel0532
import BecknerOnofri.EntropyScalarCertificate.Brackets0034
import BecknerOnofri.EntropyScalarCertificate.Brackets0035
import BecknerOnofri.EntropyScalarCertificate.Logs0069
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0552
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (1692799794935603514353457655922661847483/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1692799794935603514353457655922661847483/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (847443413729356712464206628900968659707/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (847443413729356712464206628900968659707/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (3387686622394316939281870913724599166897/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3387686622394316939281870913724599166897/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0034.bracket0552 BracketBatch0034.bracket0553 (3387686622394316939281870913724599166897/20000000000000000000000000000000000000000) (305465448293890783941857060509679271/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0034.bracket0552 BracketBatch0034.bracket0553
  (3387686622394316939281870913724599166897/20000000000000000000000000000000000000000) (305465448293890783941857060509679271/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0552
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0553
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (1694886827458713424928413257801937319411/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1694886827458713424928413257801937319411/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (1696974076964515201096679756163168321981/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1696974076964515201096679756163168321981/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (211991306526451789126568313372819102587/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (211991306526451789126568313372819102587/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0034.bracket0553 BracketBatch0034.bracket0554 (211991306526451789126568313372819102587/1250000000000000000000000000000000000000) (122776661482878820154025594326380837/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0034.bracket0553 BracketBatch0034.bracket0554
  (211991306526451789126568313372819102587/1250000000000000000000000000000000000000) (122776661482878820154025594326380837/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0553
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0554
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (848487038482257600548339878081584160989/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (848487038482257600548339878081584160989/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (849530771877244253746403512247351158801/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (849530771877244253746403512247351158801/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (169801781035950185429474339032893531979/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (169801781035950185429474339032893531979/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0034.bracket0554 BracketBatch0034.bracket0555 (169801781035950185429474339032893531979/1000000000000000000000000000000000000000) (616846460650266110530226821177309257/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0034.bracket0554 BracketBatch0034.bracket0555
  (169801781035950185429474339032893531979/1000000000000000000000000000000000000000) (616846460650266110530226821177309257/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0554
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0555
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (1699061543754488507492807024494702317599/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1699061543754488507492807024494702317599/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (850574614065137241167308110753534334367/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (850574614065137241167308110753534334367/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (3400210771884762989827423246001770986333/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3400210771884762989827423246001770986333/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0034.bracket0555 BracketBatch0034.bracket0556 (3400210771884762989827423246001770986333/20000000000000000000000000000000000000000) (619820382770132700991458374337655477/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0034.bracket0555 BracketBatch0034.bracket0556
  (3400210771884762989827423246001770986333/20000000000000000000000000000000000000000) (619820382770132700991458374337655477/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0555
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0556
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (1701149228130274482334616221507068668731/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1701149228130274482334616221507068668731/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (425809282598419000925739896482049534551/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (425809282598419000925739896482049534551/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (680877271704790097207515161487053361387/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (680877271704790097207515161487053361387/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0034.bracket0556 BracketBatch0034.bracket0557 (680877271704790097207515161487053361387/4000000000000000000000000000000000000000) (62280510028407216888407431291739321/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0034.bracket0556 BracketBatch0034.bracket0557
  (680877271704790097207515161487053361387/4000000000000000000000000000000000000000) (62280510028407216888407431291739321/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0556
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0557
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (1703237130393676003702959585928198138201/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1703237130393676003702959585928198138201/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (213165656355832244515057748580722617269/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (213165656355832244515057748580722617269/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (3408562381240333959823421574573979076353/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3408562381240333959823421574573979076353/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0034.bracket0557 BracketBatch0034.bracket0558 (3408562381240333959823421574573979076353/20000000000000000000000000000000000000000) (125160127947504003746671353761121021/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0034.bracket0557 BracketBatch0034.bracket0558
  (3408562381240333959823421574573979076353/20000000000000000000000000000000000000000) (125160127947504003746671353761121021/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0557
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0558
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (1705325250846657956120461988645780938149/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1705325250846657956120461988645780938149/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (1707413589791347497429839300331980625241/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1707413589791347497429839300331980625241/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (341273884063800545355030128897776156339/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (341273884063800545355030128897776156339/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0034.bracket0558 BracketBatch0034.bracket0559 (341273884063800545355030128897776156339/2000000000000000000000000000000000000000) (78600878463910374973854999308842499/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0034.bracket0558 BracketBatch0034.bracket0559
  (341273884063800545355030128897776156339/2000000000000000000000000000000000000000) (78600878463910374973854999308842499/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0558
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0559
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (853706794895673748714919650165990312619/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (853706794895673748714919650165990312619/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0087.rows BesselBatch0087.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (1709502147530034325972389668380491899389/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1709502147530034325972389668380491899389/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (3416915737321381823402228968712472524627/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3416915737321381823402228968712472524627/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0069.rows ScalarLogs0069.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0034.bracket0559 BracketBatch0035.bracket0560 (3416915737321381823402228968712472524627/20000000000000000000000000000000000000000) (631824290821553165026165669033157717/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0034.bracket0559 BracketBatch0035.bracket0560
  (3416915737321381823402228968712472524627/20000000000000000000000000000000000000000) (631824290821553165026165669033157717/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0559
