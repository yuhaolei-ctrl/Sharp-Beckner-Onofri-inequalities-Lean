module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0186
public import BecknerOnofri.EntropyScalarCertificate.Bessel0187
public import BecknerOnofri.EntropyScalarCertificate.Bessel0582
public import BecknerOnofri.EntropyScalarCertificate.Brackets0074
public import BecknerOnofri.EntropyScalarCertificate.Brackets0075
public import BecknerOnofri.EntropyScalarCertificate.Logs0149
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1192
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (1164569441374335280882660910098795611469/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1164569441374335280882660910098795611469/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (9343790552201279661054789123151011162113/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9343790552201279661054789123151011162113/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (3732069216639192381623215280788275210773/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3732069216639192381623215280788275210773/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0074.bracket1192 BracketBatch0074.bracket1193 (3732069216639192381623215280788275210773/4000000000000000000000000000000000000000) (102411366849139322274700088896590448969/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0074.bracket1192 BracketBatch0074.bracket1193
  (3732069216639192381623215280788275210773/4000000000000000000000000000000000000000) (102411366849139322274700088896590448969/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1192
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1193
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (934379055220127966105478912315101116211/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (934379055220127966105478912315101116211/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (9371149248997874614086187270830468367379/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9371149248997874614086187270830468367379/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (18714939801199154275140976393981479529489/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (18714939801199154275140976393981479529489/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0074.bracket1193 BracketBatch0074.bracket1194 (18714939801199154275140976393981479529489/20000000000000000000000000000000000000000) (103126787404425898806002248416966653713/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0074.bracket1193 BracketBatch0074.bracket1194
  (18714939801199154275140976393981479529489/20000000000000000000000000000000000000000) (103126787404425898806002248416966653713/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1193
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1194
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (585696828062367163380386704426904272961/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (585696828062367163380386704426904272961/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (9398632788027644972737387092474438716031/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9398632788027644972737387092474438716031/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (18769782037025519586823574363304907083407/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (18769782037025519586823574363304907083407/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0074.bracket1194 BracketBatch0074.bracket1195 (18769782037025519586823574363304907083407/20000000000000000000000000000000000000000) (207693571240019450736520115347337335283/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0074.bracket1194 BracketBatch0074.bracket1195
  (18769782037025519586823574363304907083407/20000000000000000000000000000000000000000) (207693571240019450736520115347337335283/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1194
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1195
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (2349658197006911243184346773118609679007/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2349658197006911243184346773118609679007/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (4713121175567478638079020585156978722287/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4713121175567478638079020585156978722287/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (9412437569581301124447714131394198080301/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9412437569581301124447714131394198080301/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0074.bracket1195 BracketBatch0074.bracket1196 (9412437569581301124447714131394198080301/10000000000000000000000000000000000000000) (104571394064920445929900516144556231611/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0074.bracket1195 BracketBatch0074.bracket1196
  (9412437569581301124447714131394198080301/10000000000000000000000000000000000000000) (104571394064920445929900516144556231611/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1195
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1196
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0186.rows BesselBatch0186.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (9426242351134957276158041170313957444571/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9426242351134957276158041170313957444571/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (9453979135617927163401782558588876800111/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9453979135617927163401782558588876800111/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (9440110743376442219779911864451417122341/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9440110743376442219779911864451417122341/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0074.bracket1196 BracketBatch0074.bracket1197 (9440110743376442219779911864451417122341/10000000000000000000000000000000000000000) (210601291288112601914313468055274924611/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0074.bracket1196 BracketBatch0074.bracket1197
  (9440110743376442219779911864451417122341/10000000000000000000000000000000000000000) (210601291288112601914313468055274924611/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1196
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1197
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (2363494783904481790850445639647219200027/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2363494783904481790850445639647219200027/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (2370461088621504775625990977944303800349/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2370461088621504775625990977944303800349/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (591744484065748320809554577198940375047/625000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (591744484065748320809554577198940375047/625000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0074.bracket1197 BracketBatch0074.bracket1198 (591744484065748320809554577198940375047/625000000000000000000000000000000000000) (53017286801584125752028988286090553149/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0074.bracket1197 BracketBatch0074.bracket1198
  (591744484065748320809554577198940375047/625000000000000000000000000000000000000) (53017286801584125752028988286090553149/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1197
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1198
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (9481844354486019102503963911777215201393/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9481844354486019102503963911777215201393/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (2377459809180700479036985950782560574877/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2377459809180700479036985950782560574877/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (18991683591208821018651907714907457500901/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (18991683591208821018651907714907457500901/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0074.bracket1198 BracketBatch0074.bracket1199 (18991683591208821018651907714907457500901/20000000000000000000000000000000000000000) (21354740074024541658452076902060765853/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0074.bracket1198 BracketBatch0074.bracket1199
  (18991683591208821018651907714907457500901/20000000000000000000000000000000000000000) (21354740074024541658452076902060765853/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1198
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1199
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (1901967847344560383229588760626048459901/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1901967847344560383229588760626048459901/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (9537965027553979639458460020168674569021/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9537965027553979639458460020168674569021/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (9523902132138390777803201911649458434263/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9523902132138390777803201911649458434263/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0149.rows ScalarLogs0149.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0074.bracket1199 BracketBatch0075.bracket1200 (9523902132138390777803201911649458434263/10000000000000000000000000000000000000000) (26879465774265062145053302562235941267/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0074.bracket1199 BracketBatch0075.bracket1200
  (9523902132138390777803201911649458434263/10000000000000000000000000000000000000000) (26879465774265062145053302562235941267/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1199
