import BecknerOnofri.EntropyScalarCertificate.Bessel0076
import BecknerOnofri.EntropyScalarCertificate.Bessel0077
import BecknerOnofri.EntropyScalarCertificate.Bessel0527
import BecknerOnofri.EntropyScalarCertificate.Brackets0030
import BecknerOnofri.EntropyScalarCertificate.Brackets0031
import BecknerOnofri.EntropyScalarCertificate.Logs0061
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0488
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (311933472554374489760765903170528694579/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (311933472554374489760765903170528694579/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (1561741128292425835312573547588893366573/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1561741128292425835312573547588893366573/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (780352122766074571029100765860384209867/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (780352122766074571029100765860384209867/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0030.bracket0488 BracketBatch0030.bracket0489 (780352122766074571029100765860384209867/5000000000000000000000000000000000000000) (221568138719950507940629692388856439/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0030.bracket0488 BracketBatch0030.bracket0489
  (780352122766074571029100765860384209867/5000000000000000000000000000000000000000) (221568138719950507940629692388856439/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0488
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0489
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (156174112829242583531257354758889336657/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (156174112829242583531257354758889336657/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (1563815091824875724023595176251974581293/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1563815091824875724023595176251974581293/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (3125556220117301559336168723840867947863/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3125556220117301559336168723840867947863/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0030.bracket0489 BracketBatch0030.bracket0490 (3125556220117301559336168723840867947863/20000000000000000000000000000000000000000) (27840914670834733684643631084941971/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0030.bracket0489 BracketBatch0030.bracket0490
  (3125556220117301559336168723840867947863/20000000000000000000000000000000000000000) (27840914670834733684643631084941971/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0489
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0490
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (156381509182487572402359517625197458129/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (156381509182487572402359517625197458129/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (782944626830454048165597615198568706061/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (782944626830454048165597615198568706061/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (782426086371445955088697601662277998353/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (782426086371445955088697601662277998353/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0030.bracket0490 BracketBatch0030.bracket0491 (782426086371445955088697601662277998353/5000000000000000000000000000000000000000) (55972764117776883372870468876159471/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0030.bracket0490 BracketBatch0030.bracket0491
  (782426086371445955088697601662277998353/5000000000000000000000000000000000000000) (55972764117776883372870468876159471/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0490
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0491
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (1565889253660908096331195230397137412119/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1565889253660908096331195230397137412119/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (313592722818470792145844199871726309671/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (313592722818470792145844199871726309671/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (1566926433876631028530208114877884480237/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1566926433876631028530208114877884480237/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0030.bracket0491 BracketBatch0030.bracket0492 (1566926433876631028530208114877884480237/10000000000000000000000000000000000000000) (112529684076852092787711219451091079/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0030.bracket0491 BracketBatch0030.bracket0492
  (1566926433876631028530208114877884480237/10000000000000000000000000000000000000000) (112529684076852092787711219451091079/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0491
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0492
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0076.rows BesselBatch0076.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (24499431470193030636394078114978617943/156250000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (24499431470193030636394078114978617943/156250000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (785019086705594800574080120370520705531/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (785019086705594800574080120370520705531/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (1569000893751771780938690620049836479707/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1569000893751771780938690620049836479707/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0030.bracket0492 BracketBatch0030.bracket0493 (1569000893751771780938690620049836479707/10000000000000000000000000000000000000000) (452464529104356145881141041937183601/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0030.bracket0492 BracketBatch0030.bracket0493
  (1569000893751771780938690620049836479707/10000000000000000000000000000000000000000) (452464529104356145881141041937183601/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0492
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0493
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (1570038173411189601148160240741041411059/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1570038173411189601148160240741041411059/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (314422586381907365111035690370671356331/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (314422586381907365111035690370671356331/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (1571075552660363213351669346297199096357/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1571075552660363213351669346297199096357/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0030.bracket0493 BracketBatch0030.bracket0494 (1571075552660363213351669346297199096357/10000000000000000000000000000000000000000) (14213109863843208009728620771496309/312500000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0030.bracket0493 BracketBatch0030.bracket0494
  (1571075552660363213351669346297199096357/10000000000000000000000000000000000000000) (14213109863843208009728620771496309/312500000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0493
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0494
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (393028232977384206388794612963339195413/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (393028232977384206388794612963339195413/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (1574187889879663214817633075521242653649/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1574187889879663214817633075521242653649/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (3146300821789200040372811527374599435301/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3146300821789200040372811527374599435301/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0030.bracket0494 BracketBatch0030.bracket0495 (3146300821789200040372811527374599435301/20000000000000000000000000000000000000000) (457183720267728606508804670395550781/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0030.bracket0494 BracketBatch0030.bracket0495
  (3146300821789200040372811527374599435301/20000000000000000000000000000000000000000) (457183720267728606508804670395550781/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0494
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0495
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (787093944939831607408816537760621326823/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (787093944939831607408816537760621326823/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (315252609522796474366119839856353422167/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (315252609522796474366119839856353422167/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (3150450937493645586648232274803009764481/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3150450937493645586648232274803009764481/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0061.rows ScalarLogs0061.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0030.bracket0495 BracketBatch0031.bracket0496 (3150450937493645586648232274803009764481/20000000000000000000000000000000000000000) (459557167357563828446788779119518133/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0030.bracket0495 BracketBatch0031.bracket0496
  (3150450937493645586648232274803009764481/20000000000000000000000000000000000000000) (459557167357563828446788779119518133/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0495
