module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0347
public import BecknerOnofri.EntropyScalarCertificate.Bessel0348
public import BecknerOnofri.EntropyScalarCertificate.Bessel0662
public import BecknerOnofri.EntropyScalarCertificate.Bessel0663
public import BecknerOnofri.EntropyScalarCertificate.Brackets0139
public import BecknerOnofri.EntropyScalarCertificate.Logs0278
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2224
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (24931543165659732602185602357899805167531/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (24931543165659732602185602357899805167531/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (100114989755245022795120947945106507682133/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (100114989755245022795120947945106507682133/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (199841162417883953203863357376705728352257/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (199841162417883953203863357376705728352257/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0139.bracket2224 BracketBatch0139.bracket2225 (199841162417883953203863357376705728352257/20000000000000000000000000000000000000000) (55207298227415633544261220322468034713/200000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0139.bracket2224 BracketBatch0139.bracket2225
  (199841162417883953203863357376705728352257/20000000000000000000000000000000000000000) (55207298227415633544261220322468034713/200000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2224
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2225
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (10011498975524502279512094794510650768213/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10011498975524502279512094794510650768213/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (4020275781422789407909300482815006608793/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4020275781422789407909300482815006608793/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (40124376858162951598570692003096334580391/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (40124376858162951598570692003096334580391/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0139.bracket2225 BracketBatch0139.bracket2226 (40124376858162951598570692003096334580391/4000000000000000000000000000000000000000) (2765510818341742087075222320692271391377/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0139.bracket2225 BracketBatch0139.bracket2226
  (40124376858162951598570692003096334580391/4000000000000000000000000000000000000000) (2765510818341742087075222320692271391377/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2225
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2226
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (50253447267784867598866256035187582609911/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (50253447267784867598866256035187582609911/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (100901923906517919211305843866187610723361/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (100901923906517919211305843866187610723361/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (201408818442087654409038355936562775943183/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (201408818442087654409038355936562775943183/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0139.bracket2226 BracketBatch0139.bracket2227 (201408818442087654409038355936562775943183/20000000000000000000000000000000000000000) (173167413987902084317391976823034826723/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0139.bracket2226 BracketBatch0139.bracket2227
  (201408818442087654409038355936562775943183/20000000000000000000000000000000000000000) (173167413987902084317391976823034826723/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2226
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2227
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0347.rows BesselBatch0347.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (50450961953258959605652921933093805361679/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (50450961953258959605652921933093805361679/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (12662514420180553764794129601637230193009/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (12662514420180553764794129601637230193009/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (20220203926796234932965888067928545226743/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (20220203926796234932965888067928545226743/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0139.bracket2227 BracketBatch0139.bracket2228 (20220203926796234932965888067928545226743/2000000000000000000000000000000000000000) (2775868500996599261837188108602517851349/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0139.bracket2227 BracketBatch0139.bracket2228
  (20220203926796234932965888067928545226743/2000000000000000000000000000000000000000) (2775868500996599261837188108602517851349/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2227
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2228
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (101300115361444430118353036813097841544069/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (101300115361444430118353036813097841544069/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (50850753498005269776014769817100074498873/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (50850753498005269776014769817100074498873/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (40600324471490993934076515289459598108363/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (40600324471490993934076515289459598108363/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0139.bracket2228 BracketBatch0139.bracket2229 (40600324471490993934076515289459598108363/4000000000000000000000000000000000000000) (2781080625107350620722267386775077128597/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0139.bracket2228 BracketBatch0139.bracket2229
  (40600324471490993934076515289459598108363/4000000000000000000000000000000000000000) (2781080625107350620722267386775077128597/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2228
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2229
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (101701506996010539552029539634200148997743/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (101701506996010539552029539634200148997743/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (102106137520327196932653480406157682201779/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (102106137520327196932653480406157682201779/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (101903822258168868242341510020178915599761/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (101903822258168868242341510020178915599761/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0139.bracket2229 BracketBatch0139.bracket2230 (101903822258168868242341510020178915599761/10000000000000000000000000000000000000000) (2786315173324982719207610732714155860499/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0139.bracket2229 BracketBatch0139.bracket2230
  (101903822258168868242341510020178915599761/10000000000000000000000000000000000000000) (2786315173324982719207610732714155860499/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2229
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2230
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (6381633595020449808290842525384855137611/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6381633595020449808290842525384855137611/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (102514046271393268994583084756250008885241/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (102514046271393268994583084756250008885241/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (204620183791720465927236565162407691087017/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (204620183791720465927236565162407691087017/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0139.bracket2230 BracketBatch0139.bracket2231 (204620183791720465927236565162407691087017/20000000000000000000000000000000000000000) (1395786162427619608222747589722508700241/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0139.bracket2230 BracketBatch0139.bracket2231
  (204620183791720465927236565162407691087017/20000000000000000000000000000000000000000) (1395786162427619608222747589722508700241/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2230
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2231
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (51257023135696634497291542378125004442619/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (51257023135696634497291542378125004442619/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0348.rows BesselBatch0348.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (12865659153229643886023164402001826118013/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (12865659153229643886023164402001826118013/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (102719659748615210041384199986132308914671/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (102719659748615210041384199986132308914671/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0278.rows ScalarLogs0278.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0139.bracket2231 BracketBatch0139.bracket2232 (102719659748615210041384199986132308914671/10000000000000000000000000000000000000000) (1398426130476014675443165239101192760267/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0139.bracket2231 BracketBatch0139.bracket2232
  (102719659748615210041384199986132308914671/10000000000000000000000000000000000000000) (1398426130476014675443165239101192760267/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2231
