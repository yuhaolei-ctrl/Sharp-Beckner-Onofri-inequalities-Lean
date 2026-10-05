import BecknerOnofri.EntropyScalarCertificate.Bessel0032
import BecknerOnofri.EntropyScalarCertificate.Bessel0033
import BecknerOnofri.EntropyScalarCertificate.Bessel0505
import BecknerOnofri.EntropyScalarCertificate.Brackets0013
import BecknerOnofri.EntropyScalarCertificate.Logs0026
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0208
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (985758586095068866069174580735844753119/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (985758586095068866069174580735844753119/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (987787908324940817560041833282608306069/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (987787908324940817560041833282608306069/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (493386623605002420907304103504613264797/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (493386623605002420907304103504613264797/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0013.bracket0208 BracketBatch0013.bracket0209 (493386623605002420907304103504613264797/5000000000000000000000000000000000000000) (2880768771063087926305827960027907/400000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0013.bracket0208 BracketBatch0013.bracket0209
  (493386623605002420907304103504613264797/5000000000000000000000000000000000000000) (2880768771063087926305827960027907/400000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0208
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0209
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (493893954162470408780020916641304153033/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (493893954162470408780020916641304153033/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (49490867587154671982611513659428808463/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (49490867587154671982611513659428808463/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (988802630034017128606136053235592237663/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (988802630034017128606136053235592237663/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0013.bracket0209 BracketBatch0013.bracket0210 (988802630034017128606136053235592237663/10000000000000000000000000000000000000000) (9076602395469647554907036606413447/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0013.bracket0209 BracketBatch0013.bracket0210
  (988802630034017128606136053235592237663/10000000000000000000000000000000000000000) (9076602395469647554907036606413447/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0209
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0210
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (989817351743093439652230273188576169257/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (989817351743093439652230273188576169257/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (991846916609530155838712767324260827189/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (991846916609530155838712767324260827189/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (990832134176311797745471520256418498223/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (990832134176311797745471520256418498223/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0013.bracket0210 BracketBatch0013.bracket0211 (990832134176311797745471520256418498223/10000000000000000000000000000000000000000) (7321006783286277349772467883573049/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0013.bracket0210 BracketBatch0013.bracket0211
  (990832134176311797745471520256418498223/10000000000000000000000000000000000000000) (7321006783286277349772467883573049/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0210
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0211
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0032.rows BesselBatch0032.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (495923458304765077919356383662130413593/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (495923458304765077919356383662130413593/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (39755064127373538271415335868919601877/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (39755064127373538271415335868919601877/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (1985723519793868612624096164047250874111/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1985723519793868612624096164047250874111/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0013.bracket0211 BracketBatch0013.bracket0212 (1985723519793868612624096164047250874111/20000000000000000000000000000000000000000) (7381098029320116515754818473589241/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0013.bracket0211 BracketBatch0013.bracket0212
  (1985723519793868612624096164047250874111/20000000000000000000000000000000000000000) (7381098029320116515754818473589241/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0211
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0212
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (496938301592169228392691698361495023461/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (496938301592169228392691698361495023461/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (995906411727690093248849028345648803853/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (995906411727690093248849028345648803853/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (79591320596481142001369297002745554031/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (79591320596481142001369297002745554031/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0013.bracket0212 BracketBatch0013.bracket0213 (79591320596481142001369297002745554031/800000000000000000000000000000000000000) (14883114317157355411435370879149899/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0013.bracket0212 BracketBatch0013.bracket0213
  (79591320596481142001369297002745554031/800000000000000000000000000000000000000) (14883114317157355411435370879149899/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0212
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0213
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (19918128234553801864976980566912976077/200000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (19918128234553801864976980566912976077/200000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (498968171249920634567936510073415443429/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (498968171249920634567936510073415443429/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (498460688556882840596180512123119922677/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (498460688556882840596180512123119922677/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0013.bracket0213 BracketBatch0013.bracket0214 (498460688556882840596180512123119922677/5000000000000000000000000000000000000000) (37511928391674363284880229212631077/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0013.bracket0213 BracketBatch0013.bracket0214
  (498460688556882840596180512123119922677/5000000000000000000000000000000000000000) (37511928391674363284880229212631077/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0213
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0214
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (199587268499968253827174604029366177371/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (199587268499968253827174604029366177371/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (249991598940283208676206309016454181949/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (249991598940283208676206309016454181949/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (1997902738260974103840698256212647614651/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1997902738260974103840698256212647614651/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0013.bracket0214 BracketBatch0013.bracket0215 (1997902738260974103840698256212647614651/20000000000000000000000000000000000000000) (75635850990338305467252661384709649/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0013.bracket0214 BracketBatch0013.bracket0215
  (1997902738260974103840698256212647614651/20000000000000000000000000000000000000000) (75635850990338305467252661384709649/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0214
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0215
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (999966395761132834704825236065816727793/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (999966395761132834704825236065816727793/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0033.rows BesselBatch0033.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (500998285885995239954746492824349543833/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (500998285885995239954746492824349543833/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0505.rows BesselBatch0505.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (2001962967533123314614318221714515815459/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2001962967533123314614318221714515815459/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0026.rows ScalarLogs0026.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0013.bracket0215 BracketBatch0013.bracket0216 (2001962967533123314614318221714515815459/20000000000000000000000000000000000000000) (38125784671468237669053678049847279/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0013.bracket0215 BracketBatch0013.bracket0216
  (2001962967533123314614318221714515815459/20000000000000000000000000000000000000000) (38125784671468237669053678049847279/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0215
