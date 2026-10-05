module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0283
public import BecknerOnofri.EntropyScalarCertificate.Bessel0284
public import BecknerOnofri.EntropyScalarCertificate.Bessel0285
public import BecknerOnofri.EntropyScalarCertificate.Bessel0630
public import BecknerOnofri.EntropyScalarCertificate.Bessel0631
public import BecknerOnofri.EntropyScalarCertificate.Brackets0113
public import BecknerOnofri.EntropyScalarCertificate.Brackets0114
public import BecknerOnofri.EntropyScalarCertificate.Logs0227
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1816
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (2144765407263705292821964024954379433761/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2144765407263705292821964024954379433761/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (10731462553878903177752817319992535386691/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10731462553878903177752817319992535386691/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (2681911198774678705232829680595554069437/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2681911198774678705232829680595554069437/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0113.bracket1816 BracketBatch0113.bracket1817 (2681911198774678705232829680595554069437/1250000000000000000000000000000000000000) (34962984446733581874906071855310818169/400000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0113.bracket1816 BracketBatch0113.bracket1817
  (2681911198774678705232829680595554069437/1250000000000000000000000000000000000000) (34962984446733581874906071855310818169/400000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1816
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1817
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0283.rows BesselBatch0283.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (21462925107757806355505634639985070773379/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (21462925107757806355505634639985070773379/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (21478220952757811832549478935382444218891/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (21478220952757811832549478935382444218891/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (4294114606051561818805511357536751499227/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4294114606051561818805511357536751499227/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0113.bracket1817 BracketBatch0113.bracket1818 (4294114606051561818805511357536751499227/2000000000000000000000000000000000000000) (218706393895580899570415155142475455593/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0113.bracket1817 BracketBatch0113.bracket1818
  (4294114606051561818805511357536751499227/2000000000000000000000000000000000000000) (218706393895580899570415155142475455593/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1817
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1818
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (2684777619094726479068684866922805527361/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2684777619094726479068684866922805527361/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (4298708333727527627508869270565889807573/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4298708333727527627508869270565889807573/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0630.rows BesselBatch0630.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (42971762621395449970093825288211893256753/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (42971762621395449970093825288211893256753/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0113.bracket1818 BracketBatch0113.bracket1819 (42971762621395449970093825288211893256753/20000000000000000000000000000000000000000) (875577444728841650297391913656116936443/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0113.bracket1818 BracketBatch0113.bracket1819
  (42971762621395449970093825288211893256753/20000000000000000000000000000000000000000) (875577444728841650297391913656116936443/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1818
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1819
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (10746770834318819068772173176414724518931/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10746770834318819068772173176414724518931/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (10754443658294341157318817691119733509809/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10754443658294341157318817691119733509809/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (1075060724630658011304549543376722901437/500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1075060724630658011304549543376722901437/500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0113.bracket1819 BracketBatch0113.bracket1820 (1075060724630658011304549543376722901437/500000000000000000000000000000000000000) (438165110063195979852134950025835871047/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0113.bracket1819 BracketBatch0113.bracket1820
  (1075060724630658011304549543376722901437/500000000000000000000000000000000000000) (438165110063195979852134950025835871047/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1819
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1820
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (4301777463317736462927527076447893403923/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4301777463317736462927527076447893403923/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (1076212897899695192963073154178567440561/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1076212897899695192963073154178567440561/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (8606629054916517234779819693162163166167/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8606629054916517234779819693162163166167/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0113.bracket1820 BracketBatch0113.bracket1821 (8606629054916517234779819693162163166167/4000000000000000000000000000000000000000) (877083903296533278513505796615164034981/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0113.bracket1820 BracketBatch0113.bracket1821
  (8606629054916517234779819693162163166167/4000000000000000000000000000000000000000) (877083903296533278513505796615164034981/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1820
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1821
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (21524257957993903859261463083571348811217/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (21524257957993903859261463083571348811217/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (21539653654428562377675342784180926426247/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (21539653654428562377675342784180926426247/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (5382988951552808279617100733469034404683/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5382988951552808279617100733469034404683/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0113.bracket1821 BracketBatch0113.bracket1822 (5382988951552808279617100733469034404683/2500000000000000000000000000000000000000) (438919247881946359088191750666058844961/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0113.bracket1821 BracketBatch0113.bracket1822
  (5382988951552808279617100733469034404683/2500000000000000000000000000000000000000) (438919247881946359088191750666058844961/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1821
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1822
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (5384913413607140594418835696045231606561/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5384913413607140594418835696045231606561/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (215550744676609587406616936799755645031/100000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (215550744676609587406616936799755645031/100000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (673355126907648767474016194752445170771/312500000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (673355126907648767474016194752445170771/312500000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0113.bracket1822 BracketBatch0113.bracket1823 (673355126907648767474016194752445170771/312500000000000000000000000000000000000) (878593999056173648475188876344433538329/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0113.bracket1822 BracketBatch0113.bracket1823
  (673355126907648767474016194752445170771/312500000000000000000000000000000000000) (878593999056173648475188876344433538329/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1822
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1823
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0284.rows BesselBatch0284.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (21555074467660958740661693679975564503097/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (21555074467660958740661693679975564503097/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0285.rows BesselBatch0285.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (10785260229826589875723619583765391123739/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10785260229826589875723619583765391123739/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0631.rows BesselBatch0631.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (1725023797092565539684357313900253870023/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1725023797092565539684357313900253870023/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0227.rows ScalarLogs0227.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0113.bracket1823 BracketBatch0114.bracket1824 (1725023797092565539684357313900253870023/800000000000000000000000000000000000000) (879350414704163631324665989603609234243/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0113.bracket1823 BracketBatch0114.bracket1824
  (1725023797092565539684357313900253870023/800000000000000000000000000000000000000) (879350414704163631324665989603609234243/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1823
