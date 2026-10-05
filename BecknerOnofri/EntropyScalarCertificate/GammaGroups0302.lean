module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0377
public import BecknerOnofri.EntropyScalarCertificate.Bessel0378
public import BecknerOnofri.EntropyScalarCertificate.Bessel0677
public import BecknerOnofri.EntropyScalarCertificate.Bessel0678
public import BecknerOnofri.EntropyScalarCertificate.Brackets0151
public import BecknerOnofri.EntropyScalarCertificate.Logs0302
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2416
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (271830510113823452340872809618551811793419/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (271830510113823452340872809618551811793419/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (54483474969274219229236688547864398946851/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (54483474969274219229236688547864398946851/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (272123942480097274243528126178936903263837/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (272123942480097274243528126178936903263837/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0151.bracket2416 BracketBatch0151.bracket2417 (272123942480097274243528126178936903263837/10000000000000000000000000000000000000000) (2077824191549364137342564811472803819091/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0151.bracket2416 BracketBatch0151.bracket2417
  (272123942480097274243528126178936903263837/10000000000000000000000000000000000000000) (2077824191549364137342564811472803819091/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2416
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2417
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (68104343711592774036545860684830498683563/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (68104343711592774036545860684830498683563/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (273006791339863326234576651812959461310189/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (273006791339863326234576651812959461310189/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (545424166186234422380760094552281456044441/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (545424166186234422380760094552281456044441/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0151.bracket2417 BracketBatch0151.bracket2418 (545424166186234422380760094552281456044441/20000000000000000000000000000000000000000) (1039687332292096636543259910215320398929/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0151.bracket2417 BracketBatch0151.bracket2418
  (545424166186234422380760094552281456044441/20000000000000000000000000000000000000000) (1039687332292096636543259910215320398929/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2417
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2418
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (136503395669931663117288325906479730655093/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (136503395669931663117288325906479730655093/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (136799388136223986319290653128705356701321/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (136799388136223986319290653128705356701321/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (136651391903077824718289489517592543678207/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (136651391903077824718289489517592543678207/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0151.bracket2418 BracketBatch0151.bracket2419 (136651391903077824718289489517592543678207/5000000000000000000000000000000000000000) (4161857416143829537337968894953716170171/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0151.bracket2418 BracketBatch0151.bracket2419
  (136651391903077824718289489517592543678207/5000000000000000000000000000000000000000) (4161857416143829537337968894953716170171/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2418
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2419
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (273598776272447972638581306257410713402639/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (273598776272447972638581306257410713402639/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (137096673233966777188872908612920674039713/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (137096673233966777188872908612920674039713/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (109558424548076305403265424696650412296413/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (109558424548076305403265424696650412296413/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0151.bracket2419 BracketBatch0151.bracket2420 (109558424548076305403265424696650412296413/4000000000000000000000000000000000000000) (4164972674974725623608489957126360530253/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0151.bracket2419 BracketBatch0151.bracket2420
  (109558424548076305403265424696650412296413/4000000000000000000000000000000000000000) (4164972674974725623608489957126360530253/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2419
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2420
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (274193346467933554377745817225841348079423/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (274193346467933554377745817225841348079423/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (274790518897382941258595164098804522105907/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (274790518897382941258595164098804522105907/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (54898386536531649563634098132464587018533/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (54898386536531649563634098132464587018533/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0151.bracket2420 BracketBatch0151.bracket2421 (54898386536531649563634098132464587018533/2000000000000000000000000000000000000000) (1042023784201460679952752946640676664783/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0151.bracket2420 BracketBatch0151.bracket2421
  (54898386536531649563634098132464587018533/2000000000000000000000000000000000000000) (1042023784201460679952752946640676664783/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2420
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2421
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (17174407431086433828662197756175282631619/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17174407431086433828662197756175282631619/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (2753903106807279849088022290919122437101/100000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2753903106807279849088022290919122437101/100000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (137545207394527731541849348297679191454001/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (137545207394527731541849348297679191454001/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0151.bracket2421 BracketBatch0151.bracket2422 (137545207394527731541849348297679191454001/5000000000000000000000000000000000000000) (834244966595727967462676905366281387287/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0151.bracket2421 BracketBatch0151.bracket2422
  (137545207394527731541849348297679191454001/5000000000000000000000000000000000000000) (834244966595727967462676905366281387287/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2421
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2422
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (275390310680727984908802229091912243710097/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (275390310680727984908802229091912243710097/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (275992739088405441649176731874934535354991/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (275992739088405441649176731874934535354991/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (2153840038160677447492105316276745230723/78125000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2153840038160677447492105316276745230723/78125000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0151.bracket2422 BracketBatch0151.bracket2423 (2153840038160677447492105316276745230723/78125000000000000000000000000000000000) (521795224379109280077475549589002699213/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0151.bracket2422 BracketBatch0151.bracket2423
  (2153840038160677447492105316276745230723/78125000000000000000000000000000000000) (521795224379109280077475549589002699213/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2422
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2423
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (68998184772101360412294182968733633838747/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (68998184772101360412294182968733633838747/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (276597821543014515491720048034096802536133/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (276597821543014515491720048034096802536133/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (552590560631419957140896779909031337891121/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (552590560631419957140896779909031337891121/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0302.rows ScalarLogs0302.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0151.bracket2423 BracketBatch0151.bracket2424 (552590560631419957140896779909031337891121/20000000000000000000000000000000000000000) (522188256838528047003588234687369158029/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0151.bracket2423 BracketBatch0151.bracket2424
  (552590560631419957140896779909031337891121/20000000000000000000000000000000000000000) (522188256838528047003588234687369158029/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2423
