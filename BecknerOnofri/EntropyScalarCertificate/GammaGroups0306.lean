module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0382
public import BecknerOnofri.EntropyScalarCertificate.Bessel0383
public import BecknerOnofri.EntropyScalarCertificate.Bessel0680
public import BecknerOnofri.EntropyScalarCertificate.Brackets0153
public import BecknerOnofri.EntropyScalarCertificate.Logs0306
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2448
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (5839283152636681043635962258848657112319/200000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5839283152636681043635962258848657112319/200000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (292641735396465038946101608368113783540163/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (292641735396465038946101608368113783540163/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (584605893028299091127899721310546639156113/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (584605893028299091127899721310546639156113/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0153.bracket2448 BracketBatch0153.bracket2449 (584605893028299091127899721310546639156113/20000000000000000000000000000000000000000) (4258601017674911712738743024597450359967/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0153.bracket2448 BracketBatch0153.bracket2449
  (584605893028299091127899721310546639156113/20000000000000000000000000000000000000000) (4258601017674911712738743024597450359967/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2448
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2449
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (914505423113953246706567526150355573563/31250000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (914505423113953246706567526150355573563/31250000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (73330619899903336463106413841742508638203/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (73330619899903336463106413841742508638203/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (146491053749019596199631815933770954523243/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (146491053749019596199631815933770954523243/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0153.bracket2449 BracketBatch0153.bracket2450 (146491053749019596199631815933770954523243/5000000000000000000000000000000000000000) (4261949605174191876060927916910963935613/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0153.bracket2449 BracketBatch0153.bracket2450
  (146491053749019596199631815933770954523243/5000000000000000000000000000000000000000) (4261949605174191876060927916910963935613/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2449
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2450
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (293322479599613345852425655366970034552809/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (293322479599613345852425655366970034552809/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (36750801560986190868422328962784305080083/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (36750801560986190868422328962784305080083/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (587328892087502872799804287069244475193473/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (587328892087502872799804287069244475193473/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0153.bracket2450 BracketBatch0153.bracket2451 (587328892087502872799804287069244475193473/20000000000000000000000000000000000000000) (853061293732269764934090020879180304023/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0153.bracket2450 BracketBatch0153.bracket2451
  (587328892087502872799804287069244475193473/20000000000000000000000000000000000000000) (853061293732269764934090020879180304023/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2450
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2451
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (294006412487889526947378631702274440640661/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (294006412487889526947378631702274440640661/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (147346778258396254028140611453520374144557/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (147346778258396254028140611453520374144557/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (23547998760187281400146394184372607557191/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (23547998760187281400146394184372607557191/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0153.bracket2451 BracketBatch0153.bracket2452 (23547998760187281400146394184372607557191/800000000000000000000000000000000000000) (533583955846317139846749517948204537931/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0153.bracket2451 BracketBatch0153.bracket2452
  (23547998760187281400146394184372607557191/800000000000000000000000000000000000000) (533583955846317139846749517948204537931/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2451
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2452
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (294693556516792508056281222907040748289111/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (294693556516792508056281222907040748289111/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (59076786870633419406798515177967014091727/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (59076786870633419406798515177967014091727/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (295038745434979802545136899398437909373873/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (295038745434979802545136899398437909373873/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0153.bracket2452 BracketBatch0153.bracket2453 (295038745434979802545136899398437909373873/10000000000000000000000000000000000000000) (106801129459992676898971073821802762433/250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0153.bracket2452 BracketBatch0153.bracket2453
  (295038745434979802545136899398437909373873/10000000000000000000000000000000000000000) (106801129459992676898971073821802762433/250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2452
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2453
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (36922991794145887129249071986229383807329/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (36922991794145887129249071986229383807329/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (296077568877696270104196042285001793724211/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (296077568877696270104196042285001793724211/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (591461503230863367138188618174836864182843/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (591461503230863367138188618174836864182843/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0153.bracket2453 BracketBatch0153.bracket2454 (591461503230863367138188618174836864182843/20000000000000000000000000000000000000000) (4275427102712955991969569384348225483067/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0153.bracket2453 BracketBatch0153.bracket2454
  (591461503230863367138188618174836864182843/20000000000000000000000000000000000000000) (4275427102712955991969569384348225483067/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2453
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2454
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (18504848054856016881512252642812612107763/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18504848054856016881512252642812612107763/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (3709681039842860122224625983554963829429/125000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3709681039842860122224625983554963829429/125000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (9263313313517579373158845640146857813727/312500000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9263313313517579373158845640146857813727/312500000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0153.bracket2454 BracketBatch0153.bracket2455 (9263313313517579373158845640146857813727/312500000000000000000000000000000000000) (4278817459142904903726966547468226200001/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0153.bracket2454 BracketBatch0153.bracket2455
  (9263313313517579373158845640146857813727/312500000000000000000000000000000000000) (4278817459142904903726966547468226200001/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2454
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2455
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (296774483187428809777970078684397106354317/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (296774483187428809777970078684397106354317/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0383.rows BesselBatch0383.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (14873735029917144037612427731657511456107/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (14873735029917144037612427731657511456107/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (594249183785771690530218633317547335476457/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (594249183785771690530218633317547335476457/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0306.rows ScalarLogs0306.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0153.bracket2455 BracketBatch0153.bracket2456 (594249183785771690530218633317547335476457/20000000000000000000000000000000000000000) (856443257478620243232509502224138201669/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0153.bracket2455 BracketBatch0153.bracket2456
  (594249183785771690530218633317547335476457/20000000000000000000000000000000000000000) (856443257478620243232509502224138201669/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2455
