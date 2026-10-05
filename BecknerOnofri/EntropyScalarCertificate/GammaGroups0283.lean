module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0353
public import BecknerOnofri.EntropyScalarCertificate.Bessel0354
public import BecknerOnofri.EntropyScalarCertificate.Bessel0355
public import BecknerOnofri.EntropyScalarCertificate.Bessel0665
public import BecknerOnofri.EntropyScalarCertificate.Bessel0666
public import BecknerOnofri.EntropyScalarCertificate.Brackets0141
public import BecknerOnofri.EntropyScalarCertificate.Brackets0142
public import BecknerOnofri.EntropyScalarCertificate.Logs0283
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2264
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (2362297845857416324225345207443933302091/200000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2362297845857416324225345207443933302091/200000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (59331572058943398505444085107232298311503/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (59331572058943398505444085107232298311503/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (59194509102689403305538857646665315431889/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (59194509102689403305538857646665315431889/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0141.bracket2264 BracketBatch0141.bracket2265 (59194509102689403305538857646665315431889/5000000000000000000000000000000000000000) (746298281769661181904098324139922629529/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0141.bracket2264 BracketBatch0141.bracket2265
  (59194509102689403305538857646665315431889/5000000000000000000000000000000000000000) (746298281769661181904098324139922629529/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2264
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2265
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (118663144117886797010888170214464596623003/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (118663144117886797010888170214464596623003/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (59608285117832072346081383246127316392121/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (59608285117832072346081383246127316392121/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (47575942870710188340610187341343845881449/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (47575942870710188340610187341343845881449/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0141.bracket2265 BracketBatch0141.bracket2266 (47575942870710188340610187341343845881449/4000000000000000000000000000000000000000) (23370096530243200579076183533277238037/78125000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0141.bracket2265 BracketBatch0141.bracket2266
  (47575942870710188340610187341343845881449/4000000000000000000000000000000000000000) (23370096530243200579076183533277238037/78125000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2265
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2266
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (119216570235664144692162766492254632784239/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (119216570235664144692162766492254632784239/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (935744095409728363670175380814679208147/78125000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (935744095409728363670175380814679208147/78125000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (47798362889621875048389043047306714285411/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (47798362889621875048389043047306714285411/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0141.bracket2266 BracketBatch0141.bracket2267 (47798362889621875048389043047306714285411/4000000000000000000000000000000000000000) (1498791132076996917690190272074216174721/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0141.bracket2266 BracketBatch0141.bracket2267
  (47798362889621875048389043047306714285411/4000000000000000000000000000000000000000) (1498791132076996917690190272074216174721/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2266
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2267
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (119775244212445230549782448744278938642813/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (119775244212445230549782448744278938642813/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (120339241015737827014792287339776746797743/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (120339241015737827014792287339776746797743/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (60028621307045764391143684021013921360139/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (60028621307045764391143684021013921360139/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0141.bracket2267 BracketBatch0141.bracket2268 (60028621307045764391143684021013921360139/5000000000000000000000000000000000000000) (750955782611506864313717313495463540501/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0141.bracket2267 BracketBatch0141.bracket2268
  (60028621307045764391143684021013921360139/5000000000000000000000000000000000000000) (750955782611506864313717313495463540501/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2267
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2268
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (6016962050786891350739614366988837339887/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6016962050786891350739614366988837339887/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (30227159261959547739519361297411586944019/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (30227159261959547739519361297411586944019/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (30155984757947002246608716566177886821727/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (30155984757947002246608716566177886821727/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0141.bracket2268 BracketBatch0141.bracket2269 (30155984757947002246608716566177886821727/2500000000000000000000000000000000000000) (3010095236758675439027128965277600519501/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0141.bracket2268 BracketBatch0141.bracket2269
  (30155984757947002246608716566177886821727/2500000000000000000000000000000000000000) (3010095236758675439027128965277600519501/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2268
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2269
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (120908637047838190958077445189646347776073/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (120908637047838190958077445189646347776073/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (121483510180321159079484727686358026274081/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (121483510180321159079484727686358026274081/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (121196073614079675018781086438002187025077/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (121196073614079675018781086438002187025077/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0141.bracket2269 BracketBatch0141.bracket2270 (121196073614079675018781086438002187025077/10000000000000000000000000000000000000000) (75409971716170184030913657652159627487/250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0141.bracket2269 BracketBatch0141.bracket2270
  (121196073614079675018781086438002187025077/10000000000000000000000000000000000000000) (75409971716170184030913657652159627487/250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2269
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2270
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (60741755090160579539742363843179013137039/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (60741755090160579539742363843179013137039/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (122063939789529956273821446679897066810707/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (122063939789529956273821446679897066810707/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (48709489993970223070661234873251018616957/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (48709489993970223070661234873251018616957/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0141.bracket2270 BracketBatch0141.bracket2271 (48709489993970223070661234873251018616957/4000000000000000000000000000000000000000) (604546863052027399117736146542577435279/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0141.bracket2270 BracketBatch0141.bracket2271
  (48709489993970223070661234873251018616957/4000000000000000000000000000000000000000) (604546863052027399117736146542577435279/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2270
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2271
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0354.rows BesselBatch0354.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (7628996236845622267113840417493566675669/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (7628996236845622267113840417493566675669/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0355.rows BesselBatch0355.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (6132500339654984390125203869952162021731/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6132500339654984390125203869952162021731/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0666.rows BesselBatch0666.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (61178486645657411019081381019735076811331/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (61178486645657411019081381019735076811331/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0283.rows ScalarLogs0283.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0141.bracket2271 BracketBatch0142.bracket2272 (61178486645657411019081381019735076811331/5000000000000000000000000000000000000000) (3029101869395287280867104517284697241947/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0141.bracket2271 BracketBatch0142.bracket2272
  (61178486645657411019081381019735076811331/5000000000000000000000000000000000000000) (3029101869395287280867104517284697241947/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2271
