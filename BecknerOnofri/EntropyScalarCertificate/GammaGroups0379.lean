import BecknerOnofri.EntropyScalarCertificate.Bessel0473
import BecknerOnofri.EntropyScalarCertificate.Bessel0474
import BecknerOnofri.EntropyScalarCertificate.Bessel0475
import BecknerOnofri.EntropyScalarCertificate.Bessel0725
import BecknerOnofri.EntropyScalarCertificate.Bessel0726
import BecknerOnofri.EntropyScalarCertificate.Brackets0189
import BecknerOnofri.EntropyScalarCertificate.Brackets0190
import BecknerOnofri.EntropyScalarCertificate.Logs0379
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3032
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (1690441974513328205861693966971234057860033/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1690441974513328205861693966971234057860033/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (1696168030116595835069116378895144845020113/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1696168030116595835069116378895144845020113/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (1693305002314962020465405172933189451440073/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1693305002314962020465405172933189451440073/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0189.bracket3032 BracketBatch0189.bracket3033 (1693305002314962020465405172933189451440073/10000000000000000000000000000000000000000) (1729875944445294499273990619800686523317/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0189.bracket3032 BracketBatch0189.bracket3033
  (1693305002314962020465405172933189451440073/10000000000000000000000000000000000000000) (1729875944445294499273990619800686523317/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3032
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3033
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0473.rows BesselBatch0473.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (169616803011659583506911637889514484502011/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (169616803011659583506911637889514484502011/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (1701933038543558188685287892736726923488901/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1701933038543558188685287892736726923488901/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (3398101068660154023754404271631871768509011/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3398101068660154023754404271631871768509011/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0189.bracket3033 BracketBatch0189.bracket3034 (3398101068660154023754404271631871768509011/20000000000000000000000000000000000000000) (6924642787162521518872481438383196436927/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0189.bracket3033 BracketBatch0189.bracket3034
  (3398101068660154023754404271631871768509011/20000000000000000000000000000000000000000) (6924642787162521518872481438383196436927/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3033
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3034
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (850966519271779094342643946368363461744449/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (850966519271779094342643946368363461744449/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (853868699314292557317046493290498963470649/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (853868699314292557317046493290498963470649/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0725.rows BesselBatch0725.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (852417609293035825829845219829431212607549/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (852417609293035825829845219829431212607549/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0189.bracket3034 BracketBatch0189.bracket3035 (852417609293035825829845219829431212607549/5000000000000000000000000000000000000000) (6929797876550619666219925457244723565571/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0189.bracket3034 BracketBatch0189.bracket3035
  (852417609293035825829845219829431212607549/5000000000000000000000000000000000000000) (6929797876550619666219925457244723565571/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3034
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3035
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (341547479725717022926818597316199585388259/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (341547479725717022926818597316199585388259/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (1713581514669530979488954233796966812708173/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1713581514669530979488954233796966812708173/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (855329728324529023530761805094491184912367/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (855329728324529023530761805094491184912367/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0189.bracket3035 BracketBatch0189.bracket3036 (855329728324529023530761805094491184912367/5000000000000000000000000000000000000000) (173374228304522723971229498534545830727/250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0189.bracket3035 BracketBatch0189.bracket3036
  (855329728324529023530761805094491184912367/5000000000000000000000000000000000000000) (173374228304522723971229498534545830727/250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3035
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3036
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (171358151466953097948895423379696681270817/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (171358151466953097948895423379696681270817/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (1719465796521608972916959164526881040298189/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1719465796521608972916959164526881040298189/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (3433047311191139952405913398323847853006359/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3433047311191139952405913398323847853006359/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0189.bracket3036 BracketBatch0189.bracket3037 (3433047311191139952405913398323847853006359/20000000000000000000000000000000000000000) (1388031328155457103786572125582375672771/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0189.bracket3036 BracketBatch0189.bracket3037
  (3433047311191139952405913398323847853006359/20000000000000000000000000000000000000000) (1388031328155457103786572125582375672771/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3036
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3037
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (859732898260804486458479582263440520149093/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (859732898260804486458479582263440520149093/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (1725390659693207639111486307982604906197821/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1725390659693207639111486307982604906197821/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (3444856456214816612028445472509485946496007/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3444856456214816612028445472509485946496007/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0189.bracket3037 BracketBatch0189.bracket3038 (3444856456214816612028445472509485946496007/20000000000000000000000000000000000000000) (1389072097910149085218311055346504275989/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0189.bracket3037 BracketBatch0189.bracket3038
  (3444856456214816612028445472509485946496007/20000000000000000000000000000000000000000) (1389072097910149085218311055346504275989/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3037
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3038
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (862695329846603819555743153991302453098909/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (862695329846603819555743153991302453098909/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (346271305088739335754721096442229875893787/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (346271305088739335754721096442229875893787/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (3456747185136904317885091790193754285666753/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3456747185136904317885091790193754285666753/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0189.bracket3038 BracketBatch0189.bracket3039 (3456747185136904317885091790193754285666753/20000000000000000000000000000000000000000) (1737645191549452240585996586296575901831/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0189.bracket3038 BracketBatch0189.bracket3039
  (3456747185136904317885091790193754285666753/20000000000000000000000000000000000000000) (1737645191549452240585996586296575901831/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3038
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3039
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0474.rows BesselBatch0474.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (432839131360924169693401370552787344867233/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (432839131360924169693401370552787344867233/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0475.rows BesselBatch0475.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (868681910441635185984045297143770698635709/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (868681910441635185984045297143770698635709/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0726.rows BesselBatch0726.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (69374406926539341014833921529973815534807/400000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (69374406926539341014833921529973815534807/400000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0379.rows ScalarLogs0379.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0189.bracket3039 BracketBatch0190.bracket3040 (69374406926539341014833921529973815534807/400000000000000000000000000000000000000) (695581755889871897075078613038536381727/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0189.bracket3039 BracketBatch0190.bracket3040
  (69374406926539341014833921529973815534807/400000000000000000000000000000000000000) (695581755889871897075078613038536381727/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3039
