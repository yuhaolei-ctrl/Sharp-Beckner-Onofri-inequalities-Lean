module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0202
public import BecknerOnofri.EntropyScalarCertificate.Bessel0203
public import BecknerOnofri.EntropyScalarCertificate.Bessel0590
public import BecknerOnofri.EntropyScalarCertificate.Brackets0081
public import BecknerOnofri.EntropyScalarCertificate.Logs0162
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1296
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (1312822504344378289824329689949634340707/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1312822504344378289824329689949634340707/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (1647404868253672402296298887665978814223/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1647404868253672402296298887665978814223/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (13153731994736581058306844000412086960427/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (13153731994736581058306844000412086960427/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0081.bracket1296 BracketBatch0081.bracket1297 (13153731994736581058306844000412086960427/10000000000000000000000000000000000000000) (3356833989566303416327297659232661431/80000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0081.bracket1296 BracketBatch0081.bracket1297
  (13153731994736581058306844000412086960427/10000000000000000000000000000000000000000) (3356833989566303416327297659232661431/80000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1296
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1297
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (13179238946029379218370391101327830513781/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (13179238946029379218370391101327830513781/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (3307666683617696485847212220300869203789/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3307666683617696485847212220300869203789/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (26409905680500165161759239982531307328937/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (26409905680500165161759239982531307328937/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0081.bracket1297 BracketBatch0081.bracket1298 (26409905680500165161759239982531307328937/20000000000000000000000000000000000000000) (84509773194515975476467344697619648107/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0081.bracket1297 BracketBatch0081.bracket1298
  (26409905680500165161759239982531307328937/20000000000000000000000000000000000000000) (84509773194515975476467344697619648107/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1297
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1298
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (13230666734470785943388848881203476815153/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (13230666734470785943388848881203476815153/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (6641257236537662856203659679760780986527/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6641257236537662856203659679760780986527/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (26513181207546111655796168240725038788207/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (26513181207546111655796168240725038788207/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0081.bracket1298 BracketBatch0081.bracket1299 (26513181207546111655796168240725038788207/20000000000000000000000000000000000000000) (212758352409430388642496792401397329307/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0081.bracket1298 BracketBatch0081.bracket1299
  (26513181207546111655796168240725038788207/20000000000000000000000000000000000000000) (212758352409430388642496792401397329307/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1298
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1299
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (13282514473075325712407319359521561973051/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (13282514473075325712407319359521561973051/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (666739417277484762785968258120416518671/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (666739417277484762785968258120416518671/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (26617302818625020968126684521929892346471/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (26617302818625020968126684521929892346471/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0081.bracket1299 BracketBatch0081.bracket1300 (26617302818625020968126684521929892346471/20000000000000000000000000000000000000000) (214254014530213105028125509452081049139/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0081.bracket1299 BracketBatch0081.bracket1300
  (26617302818625020968126684521929892346471/20000000000000000000000000000000000000000) (214254014530213105028125509452081049139/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1299
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1300
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (13334788345549695255719365162408330373417/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (13334788345549695255719365162408330373417/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (1673436832235865482467568007824619546627/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1673436832235865482467568007824619546627/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (26722283003436619115459909225005286746433/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (26722283003436619115459909225005286746433/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0081.bracket1300 BracketBatch0081.bracket1301 (26722283003436619115459909225005286746433/20000000000000000000000000000000000000000) (8630462137573625599171318574201097511/200000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0081.bracket1300 BracketBatch0081.bracket1301
  (26722283003436619115459909225005286746433/20000000000000000000000000000000000000000) (8630462137573625599171318574201097511/200000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1300
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1301
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (13387494657886923859740544062596956373013/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (13387494657886923859740544062596956373013/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (6720319920667319107225866966232798987487/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6720319920667319107225866966232798987487/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (26828134499221562074192277995062554347987/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (26828134499221562074192277995062554347987/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0081.bracket1301 BracketBatch0081.bracket1302 (26828134499221562074192277995062554347987/20000000000000000000000000000000000000000) (434562210897711138190958644050328156599/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0081.bracket1301 BracketBatch0081.bracket1302
  (26828134499221562074192277995062554347987/20000000000000000000000000000000000000000) (434562210897711138190958644050328156599/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1301
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1302
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (13440639841334638214451733932465597974971/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (13440639841334638214451733932465597974971/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (3373557613861804257296587226435218265619/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3373557613861804257296587226435218265619/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (26934870296781855243638082838206471037447/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (26934870296781855243638082838206471037447/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0081.bracket1302 BracketBatch0081.bracket1303 (26934870296781855243638082838206471037447/20000000000000000000000000000000000000000) (437625618273193158712721923659077153409/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0081.bracket1302 BracketBatch0081.bracket1303
  (26934870296781855243638082838206471037447/20000000000000000000000000000000000000000) (437625618273193158712721923659077153409/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1302
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1303
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (13494230455447217029186348905740873062473/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (13494230455447217029186348905740873062473/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0203.rows BesselBatch0203.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (2709654638244901955644114397928129115299/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2709654638244901955644114397928129115299/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (3380312955833965850925865111922689829871/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3380312955833965850925865111922689829871/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0162.rows ScalarLogs0162.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0081.bracket1303 BracketBatch0081.bracket1304 (3380312955833965850925865111922689829871/2500000000000000000000000000000000000000) (440713610783186952981798200761481440733/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0081.bracket1303 BracketBatch0081.bracket1304
  (3380312955833965850925865111922689829871/2500000000000000000000000000000000000000) (440713610783186952981798200761481440733/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1303
