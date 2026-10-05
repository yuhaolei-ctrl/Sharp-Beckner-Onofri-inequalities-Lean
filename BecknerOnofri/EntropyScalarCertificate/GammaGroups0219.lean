module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0273
public import BecknerOnofri.EntropyScalarCertificate.Bessel0274
public import BecknerOnofri.EntropyScalarCertificate.Bessel0275
public import BecknerOnofri.EntropyScalarCertificate.Bessel0625
public import BecknerOnofri.EntropyScalarCertificate.Bessel0626
public import BecknerOnofri.EntropyScalarCertificate.Brackets0109
public import BecknerOnofri.EntropyScalarCertificate.Brackets0110
public import BecknerOnofri.EntropyScalarCertificate.Logs0219
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1752
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (20519259994439846722826210038255653377199/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (20519259994439846722826210038255653377199/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (20533061874934165029925527259613735537803/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (20533061874934165029925527259613735537803/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (20526160934687005876375868648934694457501/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (20526160934687005876375868648934694457501/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0109.bracket1752 BracketBatch0109.bracket1753 (20526160934687005876375868648934694457501/10000000000000000000000000000000000000000) (827827513588706013146842732309167910317/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0109.bracket1752 BracketBatch0109.bracket1753
  (20526160934687005876375868648934694457501/10000000000000000000000000000000000000000) (827827513588706013146842732309167910317/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1752
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1753
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0273.rows BesselBatch0273.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (102665309374670825149627636298068677689/50000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (102665309374670825149627636298068677689/50000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (4109377005413529941016624500905021386179/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4109377005413529941016624500905021386179/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (8215989380400362947001729952827768493739/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8215989380400362947001729952827768493739/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0109.bracket1753 BracketBatch0109.bracket1754 (8215989380400362947001729952827768493739/4000000000000000000000000000000000000000) (51782724952563225916860065836842509459/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0109.bracket1753 BracketBatch0109.bracket1754
  (8215989380400362947001729952827768493739/4000000000000000000000000000000000000000) (51782724952563225916860065836842509459/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1753
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1754
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (5136721256766912426270780626131276732723/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5136721256766912426270780626131276732723/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (1285045593813124810543954369837465632177/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1285045593813124810543954369837465632177/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (10276903632019411668446598105481139261431/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (10276903632019411668446598105481139261431/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0109.bracket1754 BracketBatch0109.bracket1755 (10276903632019411668446598105481139261431/5000000000000000000000000000000000000000) (829220498472258480770487957589204199091/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0109.bracket1754 BracketBatch0109.bracket1755
  (10276903632019411668446598105481139261431/5000000000000000000000000000000000000000) (829220498472258480770487957589204199091/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1754
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1755
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (20560729501009996968703269917399450114829/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (20560729501009996968703269917399450114829/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (10287297673540574801504396494613452985987/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10287297673540574801504396494613452985987/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (41135324848091146571712062906626356086803/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (41135324848091146571712062906626356086803/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0109.bracket1755 BracketBatch0109.bracket1756 (41135324848091146571712062906626356086803/20000000000000000000000000000000000000000) (414959106310003437166484692955764506139/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0109.bracket1755 BracketBatch0109.bracket1756
  (41135324848091146571712062906626356086803/20000000000000000000000000000000000000000) (414959106310003437166484692955764506139/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1755
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1756
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (20574595347081149603008792989226905971971/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (20574595347081149603008792989226905971971/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (20588482615751844872229922102332058134213/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (20588482615751844872229922102332058134213/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (5145384745354124309404839386444870513273/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5145384745354124309404839386444870513273/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0109.bracket1756 BracketBatch0109.bracket1757 (5145384745354124309404839386444870513273/2500000000000000000000000000000000000000) (830616743024436844079744324634186786881/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0109.bracket1756 BracketBatch0109.bracket1757
  (5145384745354124309404839386444870513273/2500000000000000000000000000000000000000) (830616743024436844079744324634186786881/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1756
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1757
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (2058848261575184487222992210233205813421/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2058848261575184487222992210233205813421/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (20602391357644164877292193601695168643651/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (20602391357644164877292193601695168643651/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (41190873973396009749522115704027226777861/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (41190873973396009749522115704027226777861/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0109.bracket1757 BracketBatch0109.bracket1758 (41190873973396009749522115704027226777861/20000000000000000000000000000000000000000) (207829022757088571918284986361816693017/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0109.bracket1757 BracketBatch0109.bracket1758
  (41190873973396009749522115704027226777861/20000000000000000000000000000000000000000) (207829022757088571918284986361816693017/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1757
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1758
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (321912364963190076207690525026487010057/156250000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (321912364963190076207690525026487010057/156250000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (20616321623532089358173468475271520667337/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (20616321623532089358173468475271520667337/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (8243742596235250847093132415393337862197/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8243742596235250847093132415393337862197/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0109.bracket1758 BracketBatch0109.bracket1759 (8243742596235250847093132415393337862197/4000000000000000000000000000000000000000) (832016257977197037508566832459434476087/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0109.bracket1758 BracketBatch0109.bracket1759
  (8243742596235250847093132415393337862197/4000000000000000000000000000000000000000) (832016257977197037508566832459434476087/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1758
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1759
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0274.rows BesselBatch0274.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (10308160811766044679086734237635760333667/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10308160811766044679086734237635760333667/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (10315136732171025478591992485161807311869/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10315136732171025478591992485161807311869/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (644478048248033442427460210087423988923/312500000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (644478048248033442427460210087423988923/312500000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0219.rows ScalarLogs0219.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0109.bracket1759 BracketBatch0110.bracket1760 (644478048248033442427460210087423988923/312500000000000000000000000000000000000) (832717245219040969348221742231247173429/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0109.bracket1759 BracketBatch0110.bracket1760
  (644478048248033442427460210087423988923/312500000000000000000000000000000000000) (832717245219040969348221742231247173429/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1759
