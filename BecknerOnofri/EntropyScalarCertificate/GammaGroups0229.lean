module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0286
public import BecknerOnofri.EntropyScalarCertificate.Bessel0287
public import BecknerOnofri.EntropyScalarCertificate.Bessel0632
public import BecknerOnofri.EntropyScalarCertificate.Brackets0114
public import BecknerOnofri.EntropyScalarCertificate.Brackets0115
public import BecknerOnofri.EntropyScalarCertificate.Logs0229
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1832
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (21948942472679908784597018169865422408849/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (21948942472679908784597018169865422408849/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (2753711582209441886813346071482286014011/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2753711582209441886813346071482286014011/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (43978635130355443879103786741723710520937/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (43978635130355443879103786741723710520937/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0114.bracket1832 BracketBatch0114.bracket1833 (43978635130355443879103786741723710520937/20000000000000000000000000000000000000000) (447878360056249880286975871650600502379/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0114.bracket1832 BracketBatch0114.bracket1833
  (43978635130355443879103786741723710520937/20000000000000000000000000000000000000000) (447878360056249880286975871650600502379/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1832
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1833
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (4405938531535107018901353714371657622417/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4405938531535107018901353714371657622417/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (22111121143009067934480840977077624422461/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (22111121143009067934480840977077624422461/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (22070406900342301514493804774467956267273/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (22070406900342301514493804774467956267273/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0114.bracket1833 BracketBatch0114.bracket1834 (22070406900342301514493804774467956267273/10000000000000000000000000000000000000000) (449824823058284094113762005450785680039/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0114.bracket1833 BracketBatch0114.bracket1834
  (22070406900342301514493804774467956267273/10000000000000000000000000000000000000000) (449824823058284094113762005450785680039/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1833
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1834
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (11055560571504533967240420488538812211229/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (11055560571504533967240420488538812211229/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (22193236528887529027866062163735257219229/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (22193236528887529027866062163735257219229/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (44304357671896596962346903140812881641687/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (44304357671896596962346903140812881641687/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0114.bracket1834 BracketBatch0114.bracket1835 (44304357671896596962346903140812881641687/20000000000000000000000000000000000000000) (225891613512257019657245595812283117533/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0114.bracket1834 BracketBatch0114.bracket1835
  (44304357671896596962346903140812881641687/20000000000000000000000000000000000000000) (225891613512257019657245595812283117533/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1834
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1835
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (11096618264443764513933031081867628609613/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (11096618264443764513933031081867628609613/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (22276047554975928315946593531194842121817/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (22276047554975928315946593531194842121817/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (44469284083863457343812655694930099341043/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (44469284083863457343812655694930099341043/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0114.bracket1835 BracketBatch0114.bracket1836 (44469284083863457343812655694930099341043/20000000000000000000000000000000000000000) (113438418382365522519065069733515882369/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0114.bracket1835 BracketBatch0114.bracket1836
  (44469284083863457343812655694930099341043/20000000000000000000000000000000000000000) (113438418382365522519065069733515882369/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1835
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1836
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0286.rows BesselBatch0286.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (11138023777487964157973296765597421060907/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (11138023777487964157973296765597421060907/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (22359563103206754007010808456834505081109/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (22359563103206754007010808456834505081109/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (44635610658182682322957401988029347202923/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (44635610658182682322957401988029347202923/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0114.bracket1836 BracketBatch0114.bracket1837 (44635610658182682322957401988029347202923/20000000000000000000000000000000000000000) (455736265181993637044617852307884270501/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0114.bracket1836 BracketBatch0114.bracket1837
  (44635610658182682322957401988029347202923/20000000000000000000000000000000000000000) (455736265181993637044617852307884270501/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1836
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1837
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (11179781551603377003505404228417252540553/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (11179781551603377003505404228417252540553/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (4488758440131929318456472049108742005491/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4488758440131929318456472049108742005491/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (44803355303866400599293168702378215108561/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (44803355303866400599293168702378215108561/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0114.bracket1837 BracketBatch0114.bracket1838 (44803355303866400599293168702378215108561/20000000000000000000000000000000000000000) (457731105639076126790699814577705299057/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0114.bracket1837 BracketBatch0114.bracket1838
  (44803355303866400599293168702378215108561/20000000000000000000000000000000000000000) (457731105639076126790699814577705299057/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1837
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1838
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (5610948050164911648070590061385927506863/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5610948050164911648070590061385927506863/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (22528744022513378768081835517007210577249/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (22528744022513378768081835517007210577249/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (44972536223173025360364195762550920604701/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (44972536223173025360364195762550920604701/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0114.bracket1838 BracketBatch0114.bracket1839 (44972536223173025360364195762550920604701/20000000000000000000000000000000000000000) (45973829961986102556762284829770257737/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0114.bracket1838 BracketBatch0114.bracket1839
  (44972536223173025360364195762550920604701/20000000000000000000000000000000000000000) (45973829961986102556762284829770257737/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1838
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1839
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (11264372011256689384040917758503605288623/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (11264372011256689384040917758503605288623/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (11307213947536168372132738776368712752469/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (11307213947536168372132738776368712752469/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (5642896489698214439043414133718079510273/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5642896489698214439043414133718079510273/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0229.rows ScalarLogs0229.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0114.bracket1839 BracketBatch0115.bracket1840 (5642896489698214439043414133718079510273/2500000000000000000000000000000000000000) (923515905840199475702450563133963381973/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0114.bracket1839 BracketBatch0115.bracket1840
  (5642896489698214439043414133718079510273/2500000000000000000000000000000000000000) (923515905840199475702450563133963381973/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1839
