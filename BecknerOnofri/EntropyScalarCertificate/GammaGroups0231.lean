import BecknerOnofri.EntropyScalarCertificate.Bessel0288
import BecknerOnofri.EntropyScalarCertificate.Bessel0289
import BecknerOnofri.EntropyScalarCertificate.Bessel0290
import BecknerOnofri.EntropyScalarCertificate.Bessel0633
import BecknerOnofri.EntropyScalarCertificate.Brackets0115
import BecknerOnofri.EntropyScalarCertificate.Brackets0116
import BecknerOnofri.EntropyScalarCertificate.Logs0231
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1848
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (23327424261769358312477959881013185749931/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (23327424261769358312477959881013185749931/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (23420142811193859592734797072351257703301/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (23420142811193859592734797072351257703301/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (2921722942060201119075797309585277715827/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2921722942060201119075797309585277715827/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0115.bracket1848 BracketBatch0115.bracket1849 (2921722942060201119075797309585277715827/1250000000000000000000000000000000000000) (961027021691020505174042142704282365537/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0115.bracket1848 BracketBatch0115.bracket1849
  (2921722942060201119075797309585277715827/1250000000000000000000000000000000000000) (961027021691020505174042142704282365537/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1848
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1849
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (11710071405596929796367398536175628851649/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (11710071405596929796367398536175628851649/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (11756847855083653712799499611895209460921/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (11756847855083653712799499611895209460921/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (2346691926068058350916689814807083831257/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2346691926068058350916689814807083831257/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0115.bracket1849 BracketBatch0115.bracket1850 (2346691926068058350916689814807083831257/1000000000000000000000000000000000000000) (965327647988038710539627471919992031111/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0115.bracket1849 BracketBatch0115.bracket1850
  (2346691926068058350916689814807083831257/1000000000000000000000000000000000000000) (965327647988038710539627471919992031111/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1849
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1850
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (23513695710167307425598999223790418921839/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (23513695710167307425598999223790418921839/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (23608094170873138546299915117778867696627/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (23608094170873138546299915117778867696627/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (23560894940520222985949457170784643309233/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (23560894940520222985949457170784643309233/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0115.bracket1850 BracketBatch0115.bracket1851 (23560894940520222985949457170784643309233/10000000000000000000000000000000000000000) (38786226861136705306662511281205135137/400000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0115.bracket1850 BracketBatch0115.bracket1851
  (23560894940520222985949457170784643309233/10000000000000000000000000000000000000000) (38786226861136705306662511281205135137/400000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1850
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1851
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (1475505885679571159143744694861179231039/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1475505885679571159143744694861179231039/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (11851674799830966454402005245219712293133/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (11851674799830966454402005245219712293133/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (4731144377053507145510392560821829228289/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4731144377053507145510392560821829228289/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0115.bracket1851 BracketBatch0115.bracket1852 (4731144377053507145510392560821829228289/2000000000000000000000000000000000000000) (243502833066869919076714821277080075923/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0115.bracket1851 BracketBatch0115.bracket1852
  (4731144377053507145510392560821829228289/2000000000000000000000000000000000000000) (243502833066869919076714821277080075923/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1851
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1852
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (23703349599661932908804010490439424586263/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (23703349599661932908804010490439424586263/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (2379947360128525909667735602738897717679/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2379947360128525909667735602738897717679/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (47502823200947192005481366517828401763053/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (47502823200947192005481366517828401763053/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0115.bracket1852 BracketBatch0115.bracket1853 (47502823200947192005481366517828401763053/20000000000000000000000000000000000000000) (489197436380387820353619695600876760001/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0115.bracket1852 BracketBatch0115.bracket1853
  (47502823200947192005481366517828401763053/20000000000000000000000000000000000000000) (489197436380387820353619695600876760001/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1852
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1853
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (23799473601285259096677356027388977176787/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (23799473601285259096677356027388977176787/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (1493529873952766644163540828998400798701/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1493529873952766644163540828998400798701/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (47695951584529525403294009291363389956003/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (47695951584529525403294009291363389956003/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0115.bracket1853 BracketBatch0115.bracket1854 (47695951584529525403294009291363389956003/20000000000000000000000000000000000000000) (245701634551255717815759055168840576911/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0115.bracket1853 BracketBatch0115.bracket1854
  (47695951584529525403294009291363389956003/20000000000000000000000000000000000000000) (245701634551255717815759055168840576911/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1853
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1854
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (23896477983244266306616653263974412779213/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (23896477983244266306616653263974412779213/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (1499648422516045552101217775497407581303/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1499648422516045552101217775497407581303/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (47890852743500995140236137671932934080061/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (47890852743500995140236137671932934080061/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0115.bracket1854 BracketBatch0115.bracket1855 (47890852743500995140236137671932934080061/20000000000000000000000000000000000000000) (123405822060017466966801471056128348417/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0115.bracket1854 BracketBatch0115.bracket1855
  (47890852743500995140236137671932934080061/20000000000000000000000000000000000000000) (123405822060017466966801471056128348417/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1854
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1855
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0289.rows BesselBatch0289.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (4798874952051345766723896881591704260169/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4798874952051345766723896881591704260169/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0290.rows BesselBatch0290.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (4818635231769276790136360850186585045761/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4818635231769276790136360850186585045761/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (961751018382062255686025773177828930593/400000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (961751018382062255686025773177828930593/400000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0231.rows ScalarLogs0231.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0115.bracket1855 BracketBatch0116.bracket1856 (961751018382062255686025773177828930593/400000000000000000000000000000000000000) (495857619096206210204053177169145819247/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0115.bracket1855 BracketBatch0116.bracket1856
  (961751018382062255686025773177828930593/400000000000000000000000000000000000000) (495857619096206210204053177169145819247/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1855
