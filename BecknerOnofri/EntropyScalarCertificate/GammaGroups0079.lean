import BecknerOnofri.EntropyScalarCertificate.Bessel0098
import BecknerOnofri.EntropyScalarCertificate.Bessel0099
import BecknerOnofri.EntropyScalarCertificate.Bessel0100
import BecknerOnofri.EntropyScalarCertificate.Bessel0538
import BecknerOnofri.EntropyScalarCertificate.Brackets0039
import BecknerOnofri.EntropyScalarCertificate.Brackets0040
import BecknerOnofri.EntropyScalarCertificate.Logs0079
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0632
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (465118273384115635207315572974821858631/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (465118273384115635207315572974821858631/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (931289225522921996335411386754191377147/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (931289225522921996335411386754191377147/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (1861525772291153266750042532703835094409/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1861525772291153266750042532703835094409/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0039.bracket0632 BracketBatch0039.bracket0633 (1861525772291153266750042532703835094409/10000000000000000000000000000000000000000) (441650590955432183071327746317543259/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0039.bracket0632 BracketBatch0039.bracket0633
  (1861525772291153266750042532703835094409/10000000000000000000000000000000000000000) (441650590955432183071327746317543259/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0632
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0633
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (1862578451045843992670822773508382754291/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1862578451045843992670822773508382754291/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (1864684050188912037108998834342776184383/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1864684050188912037108998834342776184383/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (1863631250617378014889910803925579469337/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1863631250617378014889910803925579469337/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0039.bracket0633 BracketBatch0039.bracket0634 (1863631250617378014889910803925579469337/10000000000000000000000000000000000000000) (887199572140025630955479225889569331/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0039.bracket0633 BracketBatch0039.bracket0634
  (1863631250617378014889910803925579469337/10000000000000000000000000000000000000000) (887199572140025630955479225889569331/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0633
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0634
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (93234202509445601855449941717138809219/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (93234202509445601855449941717138809219/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (466697472820232800153783260139715484309/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (466697472820232800153783260139715484309/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (233217121341865202357758242181352382601/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (233217121341865202357758242181352382601/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0039.bracket0634 BracketBatch0039.bracket0635 (233217121341865202357758242181352382601/1250000000000000000000000000000000000000) (222777733907149429235897658219294079/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0039.bracket0634 BracketBatch0039.bracket0635
  (233217121341865202357758242181352382601/1250000000000000000000000000000000000000) (222777733907149429235897658219294079/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0634
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0635
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (1866789891280931200615133040558861937233/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1866789891280931200615133040558861937233/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (1868895974637349780996292471748527555957/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1868895974637349780996292471748527555957/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (373568586591828098161142551230738949319/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (373568586591828098161142551230738949319/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0039.bracket0635 BracketBatch0039.bracket0636 (373568586591828098161142551230738949319/2000000000000000000000000000000000000000) (447517650862452116998724603135158191/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0039.bracket0635 BracketBatch0039.bracket0636
  (373568586591828098161142551230738949319/2000000000000000000000000000000000000000) (447517650862452116998724603135158191/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0635
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0636
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (934447987318674890498146235874263777977/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (934447987318674890498146235874263777977/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (1871002300573800139563105032208309913129/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1871002300573800139563105032208309913129/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (3739898275211149920559397503956837469083/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3739898275211149920559397503956837469083/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0039.bracket0636 BracketBatch0039.bracket0637 (3739898275211149920559397503956837469083/20000000000000000000000000000000000000000) (898972699813804667920910307774295921/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0039.bracket0636 BracketBatch0039.bracket0637
  (3739898275211149920559397503956837469083/20000000000000000000000000000000000000000) (898972699813804667920910307774295921/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0636
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0637
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (935501150286900069781552516104154956563/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (935501150286900069781552516104154956563/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (187310886940609899364766792000368988441/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (187310886940609899364766792000368988441/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (117003474061871847912836654756624993673/625000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (117003474061871847912836654756624993673/625000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0039.bracket0637 BracketBatch0039.bracket0638 (117003474061871847912836654756624993673/625000000000000000000000000000000000000) (180584631863342046103100996895666719/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0039.bracket0637 BracketBatch0039.bracket0638
  (117003474061871847912836654756624993673/625000000000000000000000000000000000000) (180584631863342046103100996895666719/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0637
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0638
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (1873108869406098993647667920003689884407/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1873108869406098993647667920003689884407/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (1875215681450247709472214492818196096319/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1875215681450247709472214492818196096319/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (1874162275428173351559941206410942990363/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1874162275428173351559941206410942990363/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0039.bracket0638 BracketBatch0039.bracket0639 (1874162275428173351559941206410942990363/10000000000000000000000000000000000000000) (453443354845799866789352169401441/5000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0039.bracket0638 BracketBatch0039.bracket0639
  (1874162275428173351559941206410942990363/10000000000000000000000000000000000000000) (453443354845799866789352169401441/5000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0638
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0639
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0099.rows BesselBatch0099.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (468803920362561927368053623204549024079/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (468803920362561927368053623204549024079/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0100.rows BesselBatch0100.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (1877322737022432595369227023022133670033/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1877322737022432595369227023022133670033/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (3752538418472680304841441515840329766349/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3752538418472680304841441515840329766349/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0079.rows ScalarLogs0079.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0039.bracket0639 BracketBatch0040.bracket0640 (3752538418472680304841441515840329766349/20000000000000000000000000000000000000000) (227715845108258871710385657911055569/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0039.bracket0639 BracketBatch0040.bracket0640
  (3752538418472680304841441515840329766349/20000000000000000000000000000000000000000) (227715845108258871710385657911055569/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0639
