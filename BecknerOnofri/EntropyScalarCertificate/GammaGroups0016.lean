import BecknerOnofri.EntropyScalarCertificate.Bessel0020
import BecknerOnofri.EntropyScalarCertificate.Bessel0021
import BecknerOnofri.EntropyScalarCertificate.Bessel0498
import BecknerOnofri.EntropyScalarCertificate.Bessel0499
import BecknerOnofri.EntropyScalarCertificate.Brackets0008
import BecknerOnofri.EntropyScalarCertificate.Logs0016
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0128
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (823782580419332035289823198470970233309/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (823782580419332035289823198470970233309/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (825803042903142743052911779848633888869/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (825803042903142743052911779848633888869/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (824792811661237389171367489159802061089/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (824792811661237389171367489159802061089/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0008.bracket0128 BracketBatch0008.bracket0129 (824792811661237389171367489159802061089/10000000000000000000000000000000000000000) (35082100055075761515546221665417847/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0008.bracket0128 BracketBatch0008.bracket0129
  (824792811661237389171367489159802061089/10000000000000000000000000000000000000000) (35082100055075761515546221665417847/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0128
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0129
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (412901521451571371526455889924316944433/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (412901521451571371526455889924316944433/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (827823606030502636503740479381451316923/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (827823606030502636503740479381451316923/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0498.rows BesselBatch0498.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (1653626648933645379556652259230085205789/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1653626648933645379556652259230085205789/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0008.bracket0129 BracketBatch0008.bracket0130 (1653626648933645379556652259230085205789/20000000000000000000000000000000000000000) (17714816383041539371453785539045099/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0008.bracket0129 BracketBatch0008.bracket0130
  (1653626648933645379556652259230085205789/20000000000000000000000000000000000000000) (17714816383041539371453785539045099/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0129
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0130
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (20695590150762565912593511984536282923/250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (20695590150762565912593511984536282923/250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (207461067513825728016887101983158985899/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (207461067513825728016887101983158985899/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (414416969021451387142822221828521815129/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (414416969021451387142822221828521815129/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0008.bracket0130 BracketBatch0008.bracket0131 (414416969021451387142822221828521815129/5000000000000000000000000000000000000000) (4472464451959536631806060941266863/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0008.bracket0130 BracketBatch0008.bracket0131
  (414416969021451387142822221828521815129/5000000000000000000000000000000000000000) (4472464451959536631806060941266863/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0130
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0131
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (829844270055302912067548407932635943593/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (829844270055302912067548407932635943593/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (831865035231503828274877727211179836191/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (831865035231503828274877727211179836191/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (207713663160850842542803266892976972473/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (207713663160850842542803266892976972473/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0008.bracket0131 BracketBatch0008.bracket0132 (207713663160850842542803266892976972473/2500000000000000000000000000000000000000) (9033090274824156105185777129195041/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0008.bracket0131 BracketBatch0008.bracket0132
  (207713663160850842542803266892976972473/2500000000000000000000000000000000000000) (9033090274824156105185777129195041/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0131
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0132
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (207966258807875957068719431802794959047/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (207966258807875957068719431802794959047/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (83388590181313488845808435827272757547/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (83388590181313488845808435827272757547/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (832875468522319358366481042741953705829/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (832875468522319358366481042741953705829/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0008.bracket0132 BracketBatch0008.bracket0133 (832875468522319358366481042741953705829/10000000000000000000000000000000000000000) (2280473858971810247543600441894151/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0008.bracket0132 BracketBatch0008.bracket0133
  (832875468522319358366481042741953705829/10000000000000000000000000000000000000000) (2280473858971810247543600441894151/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0132
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0133
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (833885901813134888458084358272727575467/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (833885901813134888458084358272727575467/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (835906870054295023562482958338448893663/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (835906870054295023562482958338448893663/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (166979277186742991202056731661117646913/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (166979277186742991202056731661117646913/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0008.bracket0133 BracketBatch0008.bracket0134 (166979277186742991202056731661117646913/2000000000000000000000000000000000000000) (36845390106208027352111101139190559/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0008.bracket0133 BracketBatch0008.bracket0134
  (166979277186742991202056731661117646913/2000000000000000000000000000000000000000) (36845390106208027352111101139190559/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0133
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0134
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0020.rows BesselBatch0020.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (41795343502714751178124147916922444683/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (41795343502714751178124147916922444683/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (418963970104576387536224513628523297203/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (418963970104576387536224513628523297203/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (836917405131723899317465992797747744033/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (836917405131723899317465992797747744033/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0008.bracket0134 BracketBatch0008.bracket0135 (836917405131723899317465992797747744033/10000000000000000000000000000000000000000) (37205798776224524247025010770494549/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0008.bracket0134 BracketBatch0008.bracket0135
  (836917405131723899317465992797747744033/10000000000000000000000000000000000000000) (37205798776224524247025010770494549/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0134
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0135
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (837927940209152775072449027257046594403/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (837927940209152775072449027257046594403/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (26248409766623327439150042277679611309/312500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (26248409766623327439150042277679611309/312500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (1677877052741099253125250380142794156291/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1677877052741099253125250380142794156291/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0016.rows ScalarLogs0016.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0008.bracket0135 BracketBatch0008.bracket0136 (1677877052741099253125250380142794156291/20000000000000000000000000000000000000000) (18784410186865671850072264408189269/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0008.bracket0135 BracketBatch0008.bracket0136
  (1677877052741099253125250380142794156291/20000000000000000000000000000000000000000) (18784410186865671850072264408189269/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0135
