module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0356
public import BecknerOnofri.EntropyScalarCertificate.Bessel0357
public import BecknerOnofri.EntropyScalarCertificate.Bessel0667
public import BecknerOnofri.EntropyScalarCertificate.Brackets0142
public import BecknerOnofri.EntropyScalarCertificate.Brackets0143
public import BecknerOnofri.EntropyScalarCertificate.Logs0285
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2280
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (127551738587011838729297107887399700020023/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (127551738587011838729297107887399700020023/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (128192457266986142877385617262382614894953/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (128192457266986142877385617262382614894953/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (7992006120437436925208835160930697341093/625000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7992006120437436925208835160930697341093/625000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0142.bracket2280 BracketBatch0142.bracket2281 (7992006120437436925208835160930697341093/625000000000000000000000000000000000000) (771976220165088364808719062828839264893/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0142.bracket2280 BracketBatch0142.bracket2281
  (7992006120437436925208835160930697341093/625000000000000000000000000000000000000) (771976220165088364808719062828839264893/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2280
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2281
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (2563849145339722857547712345247652297899/200000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2563849145339722857547712345247652297899/200000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (64419858069009224437878639026025274992097/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (64419858069009224437878639026025274992097/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (32129021675625573969142861914304145609893/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (32129021675625573969142861914304145609893/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0142.bracket2281 BracketBatch0142.bracket2282 (32129021675625573969142861914304145609893/2500000000000000000000000000000000000000) (38682630682898941623504310338435149691/125000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0142.bracket2281 BracketBatch0142.bracket2282
  (32129021675625573969142861914304145609893/2500000000000000000000000000000000000000) (38682630682898941623504310338435149691/125000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2281
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2282
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (128839716138018448875757278052050549984191/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (128839716138018448875757278052050549984191/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (25898723163287353918398581135142045959529/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (25898723163287353918398581135142045959529/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (64583332988613804616937545931940194945459/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (64583332988613804616937545931940194945459/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0142.bracket2282 BracketBatch0142.bracket2283 (64583332988613804616937545931940194945459/5000000000000000000000000000000000000000) (310135161309825823155946606455526307013/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0142.bracket2282 BracketBatch0142.bracket2283
  (64583332988613804616937545931940194945459/5000000000000000000000000000000000000000) (310135161309825823155946606455526307013/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2282
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2283
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (64746807908218384795996452837855114898821/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (64746807908218384795996452837855114898821/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (2603085179862726368100604262891172306497/200000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2603085179862726368100604262891172306497/200000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (64911968702393271999255779705067211280623/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (64911968702393271999255779705067211280623/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0142.bracket2283 BracketBatch0142.bracket2284 (64911968702393271999255779705067211280623/5000000000000000000000000000000000000000) (621625739380699950416978154404485207783/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0142.bracket2283 BracketBatch0142.bracket2284
  (64911968702393271999255779705067211280623/5000000000000000000000000000000000000000) (621625739380699950416978154404485207783/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2283
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2284
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0356.rows BesselBatch0356.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (130154258993136318405030213144558615324847/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (130154258993136318405030213144558615324847/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (130821750487324761113853887939823810584537/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (130821750487324761113853887939823810584537/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (32622001185057634939860512635547803238673/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (32622001185057634939860512635547803238673/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0142.bracket2284 BracketBatch0142.bracket2285 (32622001185057634939860512635547803238673/2500000000000000000000000000000000000000) (622988410253963011704376181342510214453/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0142.bracket2284 BracketBatch0142.bracket2285
  (32622001185057634939860512635547803238673/2500000000000000000000000000000000000000) (622988410253963011704376181342510214453/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2284
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2285
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (65410875243662380556926943969911905292267/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (65410875243662380556926943969911905292267/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (131496197301947007032598897931324663595173/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (131496197301947007032598897931324663595173/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (262317947789271768146452785871148474179707/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (262317947789271768146452785871148474179707/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0142.bracket2285 BracketBatch0142.bracket2286 (262317947789271768146452785871148474179707/20000000000000000000000000000000000000000) (780448006464313074911832445010342400323/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0142.bracket2285 BracketBatch0142.bracket2286
  (262317947789271768146452785871148474179707/20000000000000000000000000000000000000000) (780448006464313074911832445010342400323/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2285
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2286
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (13149619730194700703259889793132466359517/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (13149619730194700703259889793132466359517/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (13217770868085109306374805066548740940423/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (13217770868085109306374805066548740940423/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (1318369529913990500481734742984060364997/100000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1318369529913990500481734742984060364997/100000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0142.bracket2286 BracketBatch0142.bracket2287 (1318369529913990500481734742984060364997/100000000000000000000000000000000000000) (782169743705980889176975847484745186791/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0142.bracket2286 BracketBatch0142.bracket2287
  (1318369529913990500481734742984060364997/100000000000000000000000000000000000000) (782169743705980889176975847484745186791/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2286
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2287
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (132177708680851093063748050665487409404227/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (132177708680851093063748050665487409404227/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0357.rows BesselBatch0357.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (13286639616775930627970723540033242295061/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (13286639616775930627970723540033242295061/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0667.rows BesselBatch0667.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (265044104848610399343455286065819832354837/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (265044104848610399343455286065819832354837/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0285.rows ScalarLogs0285.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0142.bracket2287 BracketBatch0143.bracket2288 (265044104848610399343455286065819832354837/20000000000000000000000000000000000000000) (3135603256886531901122057127980002370487/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0142.bracket2287 BracketBatch0143.bracket2288
  (265044104848610399343455286065819832354837/20000000000000000000000000000000000000000) (3135603256886531901122057127980002370487/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2287
