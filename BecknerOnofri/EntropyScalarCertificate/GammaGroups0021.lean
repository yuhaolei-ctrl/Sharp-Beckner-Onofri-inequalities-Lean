module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0026
public import BecknerOnofri.EntropyScalarCertificate.Bessel0027
public import BecknerOnofri.EntropyScalarCertificate.Bessel0502
public import BecknerOnofri.EntropyScalarCertificate.Brackets0010
public import BecknerOnofri.EntropyScalarCertificate.Brackets0011
public import BecknerOnofri.EntropyScalarCertificate.Logs0021
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0168
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (904682096617393489093346995165317505571/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (904682096617393489093346995165317505571/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (906706783577411746659032219340079633151/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (906706783577411746659032219340079633151/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (905694440097402617876189607252698569361/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (905694440097402617876189607252698569361/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0010.bracket0168 BracketBatch0010.bracket0169 (905694440097402617876189607252698569361/10000000000000000000000000000000000000000) (51098823143717658914320199456267903/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0010.bracket0168 BracketBatch0010.bracket0169
  (905694440097402617876189607252698569361/10000000000000000000000000000000000000000) (51098823143717658914320199456267903/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0168
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0169
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (226676695894352936664758054835019908287/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (226676695894352936664758054835019908287/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (908731581392311220810678435112988720019/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (908731581392311220810678435112988720019/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (1815438364969722967469710654453068353167/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1815438364969722967469710654453068353167/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0010.bracket0169 BracketBatch0010.bracket0170 (1815438364969722967469710654453068353167/20000000000000000000000000000000000000000) (51558416289497271078894016218084513/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0010.bracket0169 BracketBatch0010.bracket0170
  (1815438364969722967469710654453068353167/20000000000000000000000000000000000000000) (51558416289497271078894016218084513/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0169
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0170
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (56795723837019451300667402194561795001/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (56795723837019451300667402194561795001/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (455378245159444628894950583875469870371/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (455378245159444628894950583875469870371/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (909744035855600239300289801431964230379/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (909744035855600239300289801431964230379/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0010.bracket0170 BracketBatch0010.bracket0171 (909744035855600239300289801431964230379/10000000000000000000000000000000000000000) (52021083761239246872457734143776601/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0010.bracket0170 BracketBatch0010.bracket0171
  (909744035855600239300289801431964230379/10000000000000000000000000000000000000000) (52021083761239246872457734143776601/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0170
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0171
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (910756490318889257789901167750939740739/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (910756490318889257789901167750939740739/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (912781510614019666441146247696814906629/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (912781510614019666441146247696814906629/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (227942250116613615528880926930969330921/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (227942250116613615528880926930969330921/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0010.bracket0171 BracketBatch0010.bracket0172 (227942250116613615528880926930969330921/2500000000000000000000000000000000000000) (13121709826472304616466593225690377/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0010.bracket0171 BracketBatch0010.bracket0172
  (227942250116613615528880926930969330921/2500000000000000000000000000000000000000) (13121709826472304616466593225690377/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0171
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0172
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0026.rows BesselBatch0026.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (456390755307009833220573123848407453313/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (456390755307009833220573123848407453313/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (914806642534652905748938348539839354719/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (914806642534652905748938348539839354719/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (365517630629734514438016919247330852269/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (365517630629734514438016919247330852269/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0010.bracket0172 BracketBatch0010.bracket0173 (365517630629734514438016919247330852269/4000000000000000000000000000000000000000) (52955696701815190187255566707827609/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0010.bracket0172 BracketBatch0010.bracket0173
  (365517630629734514438016919247330852269/4000000000000000000000000000000000000000) (52955696701815190187255566707827609/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0172
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0173
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (228701660633663226437234587134959838679/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (228701660633663226437234587134959838679/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (36673275453512650900118408989476181819/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (36673275453512650900118408989476181819/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (1831638528872469178251898573276743900191/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1831638528872469178251898573276743900191/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0010.bracket0173 BracketBatch0010.bracket0174 (1831638528872469178251898573276743900191/20000000000000000000000000000000000000000) (13356917439703584702919919318161491/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0010.bracket0173 BracketBatch0010.bracket0174
  (1831638528872469178251898573276743900191/20000000000000000000000000000000000000000) (13356917439703584702919919318161491/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0173
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0174
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (14325498224028379257858753511514133523/156250000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (14325498224028379257858753511514133523/156250000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (14357144410634595142051566689589906517/156250000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (14357144410634595142051566689589906517/156250000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (717066065866574359997758005027601001/7812500000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (717066065866574359997758005027601001/7812500000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0010.bracket0174 BracketBatch0010.bracket0175 (717066065866574359997758005027601001/7812500000000000000000000000000000000) (3368923269882489387832317856572211/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0010.bracket0174 BracketBatch0010.bracket0175
  (717066065866574359997758005027601001/7812500000000000000000000000000000000) (3368923269882489387832317856572211/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0174
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0175
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (183771448456122817818260053626750803417/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (183771448456122817818260053626750803417/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0027.rows BesselBatch0027.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (920882710620227891422206393833401180289/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (920882710620227891422206393833401180289/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0502.rows BesselBatch0502.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (919869976450420990256753330983577598687/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (919869976450420990256753330983577598687/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0021.rows ScalarLogs0021.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0010.bracket0175 BracketBatch0011.bracket0176 (919869976450420990256753330983577598687/10000000000000000000000000000000000000000) (54381018252407652333479379745151039/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0010.bracket0175 BracketBatch0011.bracket0176
  (919869976450420990256753330983577598687/10000000000000000000000000000000000000000) (54381018252407652333479379745151039/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0175
