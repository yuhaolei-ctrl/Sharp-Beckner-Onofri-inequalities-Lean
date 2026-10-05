import BecknerOnofri.EntropyScalarCertificate.Bessel0320
import BecknerOnofri.EntropyScalarCertificate.Bessel0321
import BecknerOnofri.EntropyScalarCertificate.Bessel0648
import BecknerOnofri.EntropyScalarCertificate.Bessel0649
import BecknerOnofri.EntropyScalarCertificate.Brackets0128
import BecknerOnofri.EntropyScalarCertificate.Logs0256
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2048
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (237922455614913670604839187026199215079/40000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (237922455614913670604839187026199215079/40000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (29807947864323083598022182869716996717899/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (29807947864323083598022182869716996717899/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (29774127408093646211813540623995949301387/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (29774127408093646211813540623995949301387/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0128.bracket2048 BracketBatch0128.bracket2049 (29774127408093646211813540623995949301387/5000000000000000000000000000000000000000) (261124425933823480372338557238398980161/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0128.bracket2048 BracketBatch0128.bracket2049
  (29774127408093646211813540623995949301387/5000000000000000000000000000000000000000) (261124425933823480372338557238398980161/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2048
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2049
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (11923179145729233439208873147886798687159/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (11923179145729233439208873147886798687159/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (29875905507179214813853067653900291860919/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (29875905507179214813853067653900291860919/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (119367706743004596823750501047234577157633/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (119367706743004596823750501047234577157633/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0128.bracket2049 BracketBatch0128.bracket2050 (119367706743004596823750501047234577157633/20000000000000000000000000000000000000000) (2091887760479789758554471279590533815621/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0128.bracket2049 BracketBatch0128.bracket2050
  (119367706743004596823750501047234577157633/20000000000000000000000000000000000000000) (2091887760479789758554471279590533815621/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2049
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2050
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (11950362202871685925541227061560116744367/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (11950362202871685925541227061560116744367/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (59888364209832893069914622299304519515773/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (59888364209832893069914622299304519515773/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (14955021903023915337202594700888137904701/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (14955021903023915337202594700888137904701/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0128.bracket2050 BracketBatch0128.bracket2051 (14955021903023915337202594700888137904701/2500000000000000000000000000000000000000) (2094787616575763280130067938852501458999/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0128.bracket2050 BracketBatch0128.bracket2051
  (14955021903023915337202594700888137904701/2500000000000000000000000000000000000000) (2094787616575763280130067938852501458999/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2050
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2051
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (5988836420983289306991462229930451951577/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5988836420983289306991462229930451951577/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (60025559805816586027338037461591963137457/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (60025559805816586027338037461591963137457/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (119913924015649479097252659760896482653227/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (119913924015649479097252659760896482653227/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0128.bracket2051 BracketBatch0128.bracket2052 (119913924015649479097252659760896482653227/20000000000000000000000000000000000000000) (209769501155839283641984185450021289341/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0128.bracket2051 BracketBatch0128.bracket2052
  (119913924015649479097252659760896482653227/20000000000000000000000000000000000000000) (209769501155839283641984185450021289341/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2051
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2052
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (30012779902908293013669018730795981568727/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (30012779902908293013669018730795981568727/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (60163402335327367639270622171820685853351/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (60163402335327367639270622171820685853351/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (24037792428228790733321731926682529798161/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (24037792428228790733321731926682529798161/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0128.bracket2052 BracketBatch0128.bracket2053 (24037792428228790733321731926682529798161/4000000000000000000000000000000000000000) (210060998148671773348468656096559878133/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0128.bracket2052 BracketBatch0128.bracket2053
  (24037792428228790733321731926682529798161/4000000000000000000000000000000000000000) (210060998148671773348468656096559878133/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2052
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2053
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (15040850583831841909817655542955171463337/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (15040850583831841909817655542955171463337/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (60301896374152373178006196285814915229223/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (60301896374152373178006196285814915229223/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (120465298709479740817276818457635601082571/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (120465298709479740817276818457635601082571/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0128.bracket2053 BracketBatch0128.bracket2054 (120465298709479740817276818457635601082571/20000000000000000000000000000000000000000) (262941570335173515152300623538961084553/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0128.bracket2053 BracketBatch0128.bracket2054
  (120465298709479740817276818457635601082571/20000000000000000000000000000000000000000) (262941570335173515152300623538961084553/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2053
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2054
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (3015094818707618658900309814290745761461/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3015094818707618658900309814290745761461/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (30220523270676764946158697406002147556593/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (30220523270676764946158697406002147556593/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (60371471457752951535161795548909605171203/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (60371471457752951535161795548909605171203/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0128.bracket2054 BracketBatch0128.bracket2055 (60371471457752951535161795548909605171203/10000000000000000000000000000000000000000) (1053231395863574830263643725584871762579/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0128.bracket2054 BracketBatch0128.bracket2055
  (60371471457752951535161795548909605171203/10000000000000000000000000000000000000000) (1053231395863574830263643725584871762579/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2054
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2055
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (60441046541353529892317394812004295113183/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (60441046541353529892317394812004295113183/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0321.rows BesselBatch0321.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (12116171499956052095671381904280789397951/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (12116171499956052095671381904280789397951/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0649.rows BesselBatch0649.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (60510952020566895185337152166704121051469/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (60510952020566895185337152166704121051469/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0256.rows ScalarLogs0256.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0128.bracket2055 BracketBatch0128.bracket2056 (60510952020566895185337152166704121051469/10000000000000000000000000000000000000000) (421880141095071458009534999188915368969/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0128.bracket2055 BracketBatch0128.bracket2056
  (60510952020566895185337152166704121051469/10000000000000000000000000000000000000000) (421880141095071458009534999188915368969/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2055
