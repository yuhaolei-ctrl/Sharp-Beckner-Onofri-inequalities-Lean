module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0357
public import BecknerOnofri.EntropyScalarCertificate.Bessel0358
public import BecknerOnofri.EntropyScalarCertificate.Bessel0667
public import BecknerOnofri.EntropyScalarCertificate.Bessel0668
public import BecknerOnofri.EntropyScalarCertificate.Brackets0143
public import BecknerOnofri.EntropyScalarCertificate.Logs0286
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2288
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (132866396167759306279707235400332422950607/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (132866396167759306279707235400332422950607/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (26712474733422281139553605283566324501501/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (26712474733422281139553605283566324501501/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (4162949528669854874648050965908813210283/312500000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4162949528669854874648050965908813210283/312500000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0143.bracket2288 BracketBatch0143.bracket2289 (4162949528669854874648050965908813210283/312500000000000000000000000000000000000) (785641308845297790341516122719480757541/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0143.bracket2288 BracketBatch0143.bracket2289
  (4162949528669854874648050965908813210283/312500000000000000000000000000000000000) (785641308845297790341516122719480757541/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2288
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2289
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (66781186833555702848884013208915811253751/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (66781186833555702848884013208915811253751/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (67132878753424824534502429801853325314359/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (67132878753424824534502429801853325314359/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (13391406558698052738338644301076913656811/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (13391406558698052738338644301076913656811/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0143.bracket2289 BracketBatch0143.bracket2290 (13391406558698052738338644301076913656811/1000000000000000000000000000000000000000) (1574782639162245370460880333217690764307/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0143.bracket2289 BracketBatch0143.bracket2290
  (13391406558698052738338644301076913656811/1000000000000000000000000000000000000000) (1574782639162245370460880333217690764307/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2289
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2290
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (26853151501369929813800971920741330125743/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (26853151501369929813800971920741330125743/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (134976666503218312568848336921330680798883/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (134976666503218312568848336921330680798883/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (134621212005033980818926598262518665713799/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (134621212005033980818926598262518665713799/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0143.bracket2290 BracketBatch0143.bracket2291 (134621212005033980818926598262518665713799/10000000000000000000000000000000000000000) (394575469809344155257966241570747479779/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0143.bracket2290 BracketBatch0143.bracket2291
  (134621212005033980818926598262518665713799/10000000000000000000000000000000000000000) (394575469809344155257966241570747479779/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2290
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2291
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (843604165645114453555302105758316754993/62500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (843604165645114453555302105758316754993/62500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (135695222027653517637844399577041774875297/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (135695222027653517637844399577041774875297/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (270671888530871830206692736498372455674177/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (270671888530871830206692736498372455674177/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0143.bracket2291 BracketBatch0143.bracket2292 (270671888530871830206692736498372455674177/20000000000000000000000000000000000000000) (3163681053393427711884180126006373721043/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0143.bracket2291 BracketBatch0143.bracket2292
  (270671888530871830206692736498372455674177/20000000000000000000000000000000000000000) (3163681053393427711884180126006373721043/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2291
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2292
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (67847611013826758818922199788520887437647/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (67847611013826758818922199788520887437647/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (8526346754740153604693986383595828449869/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8526346754740153604693986383595828449869/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (136058385051747987656474090857287515036599/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (136058385051747987656474090857287515036599/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0143.bracket2292 BracketBatch0143.bracket2293 (136058385051747987656474090857287515036599/10000000000000000000000000000000000000000) (792699386376639002711781706455839751443/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0143.bracket2292 BracketBatch0143.bracket2293
  (136058385051747987656474090857287515036599/10000000000000000000000000000000000000000) (792699386376639002711781706455839751443/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2292
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2293
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (136421548075842457675103782137533255197901/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (136421548075842457675103782137533255197901/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (68577885669517278050051770086902886643213/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (68577885669517278050051770086902886643213/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (273577319414877013775207322311339028484327/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (273577319414877013775207322311339028484327/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0143.bracket2293 BracketBatch0143.bracket2294 (273577319414877013775207322311339028484327/20000000000000000000000000000000000000000) (1588976811083122040910358938184584509881/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0143.bracket2293 BracketBatch0143.bracket2294
  (273577319414877013775207322311339028484327/20000000000000000000000000000000000000000) (1588976811083122040910358938184584509881/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2293
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2294
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (137155771339034556100103540173805773286423/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (137155771339034556100103540173805773286423/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (68949010638845347616809155553007348009817/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (68949010638845347616809155553007348009817/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (275053792616725251333721851279820469306057/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (275053792616725251333721851279820469306057/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0143.bracket2294 BracketBatch0143.bracket2295 (275053792616725251333721851279820469306057/20000000000000000000000000000000000000000) (796287418928015934554466615277951985629/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0143.bracket2294 BracketBatch0143.bracket2295
  (275053792616725251333721851279820469306057/20000000000000000000000000000000000000000) (796287418928015934554466615277951985629/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2294
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2295
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (137898021277690695233618311106014696019631/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (137898021277690695233618311106014696019631/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (554593720790241767192194498971220891629/40000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (554593720790241767192194498971220891629/40000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (276546451475251137031666935848819918926881/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (276546451475251137031666935848819918926881/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0286.rows ScalarLogs0286.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0143.bracket2295 BracketBatch0143.bracket2296 (276546451475251137031666935848819918926881/20000000000000000000000000000000000000000) (399048262941537995053311330923959755321/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0143.bracket2295 BracketBatch0143.bracket2296
  (276546451475251137031666935848819918926881/20000000000000000000000000000000000000000) (399048262941537995053311330923959755321/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2295
