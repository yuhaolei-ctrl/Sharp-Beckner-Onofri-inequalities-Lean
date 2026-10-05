module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0205
public import BecknerOnofri.EntropyScalarCertificate.Bessel0206
public import BecknerOnofri.EntropyScalarCertificate.Bessel0591
public import BecknerOnofri.EntropyScalarCertificate.Bessel0592
public import BecknerOnofri.EntropyScalarCertificate.Brackets0082
public import BecknerOnofri.EntropyScalarCertificate.Logs0164
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1312
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (6998870199287365407772309660067606509091/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6998870199287365407772309660067606509091/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (14056176686568079314047081301651390465297/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (14056176686568079314047081301651390465297/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (28053917085142810129591700621786603483479/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (28053917085142810129591700621786603483479/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0082.bracket1312 BracketBatch0082.bracket1313 (28053917085142810129591700621786603483479/20000000000000000000000000000000000000000) (234830389304809039460476010769930178791/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0082.bracket1312 BracketBatch0082.bracket1313
  (28053917085142810129591700621786603483479/20000000000000000000000000000000000000000) (234830389304809039460476010769930178791/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1312
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1313
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (7028088343284039657023540650825695232647/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (7028088343284039657023540650825695232647/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (1411513999398897609270343322610009410003/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1411513999398897609270343322610009410003/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (7042829170139263851687628631937871141331/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7042829170139263851687628631937871141331/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0082.bracket1313 BracketBatch0082.bracket1314 (7042829170139263851687628631937871141331/5000000000000000000000000000000000000000) (59126400755312198837042886509136839009/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0082.bracket1313 BracketBatch0082.bracket1314
  (7042829170139263851687628631937871141331/5000000000000000000000000000000000000000) (59126400755312198837042886509136839009/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1313
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1314
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (14115139993988976092703433226100094100027/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (14115139993988976092703433226100094100027/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (885914918289417177798357700528398879503/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (885914918289417177798357700528398879503/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (1131591147464786037499086257382179046883/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1131591147464786037499086257382179046883/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0082.bracket1314 BracketBatch0082.bracket1315 (1131591147464786037499086257382179046883/800000000000000000000000000000000000000) (119097412800890102861053377421757671311/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0082.bracket1314 BracketBatch0082.bracket1315
  (1131591147464786037499086257382179046883/800000000000000000000000000000000000000) (119097412800890102861053377421757671311/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1314
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1315
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (2834927738526134968954744641690876414409/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2834927738526134968954744641690876414409/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (14234681331262965942685004289994794394503/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (14234681331262965942685004289994794394503/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (7102330005973410196864681874612294116637/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7102330005973410196864681874612294116637/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0082.bracket1315 BracketBatch0082.bracket1316 (7102330005973410196864681874612294116637/5000000000000000000000000000000000000000) (239898229577931783182622078734702354569/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0082.bracket1315 BracketBatch0082.bracket1316
  (7102330005973410196864681874612294116637/5000000000000000000000000000000000000000) (239898229577931783182622078734702354569/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1315
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1316
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (28469362662525931885370008579989588789/20000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (28469362662525931885370008579989588789/20000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (14295276640188172665434040022367811610073/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (14295276640188172665434040022367811610073/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (28529957971451138608119044312362606004573/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (28529957971451138608119044312362606004573/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0082.bracket1316 BracketBatch0082.bracket1317 (28529957971451138608119044312362606004573/20000000000000000000000000000000000000000) (241615990476612426411358862790580944599/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0082.bracket1316 BracketBatch0082.bracket1317
  (28529957971451138608119044312362606004573/20000000000000000000000000000000000000000) (241615990476612426411358862790580944599/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1316
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1317
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (1429527664018817266543404002236781161007/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1429527664018817266543404002236781161007/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (897277095995812859956153138665195243757/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (897277095995812859956153138665195243757/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (14325855088060589212366245120505467755091/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (14325855088060589212366245120505467755091/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0082.bracket1317 BracketBatch0082.bracket1318 (14325855088060589212366245120505467755091/10000000000000000000000000000000000000000) (243348286880664231099215336086670368189/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0082.bracket1317 BracketBatch0082.bracket1318
  (14325855088060589212366245120505467755091/10000000000000000000000000000000000000000) (243348286880664231099215336086670368189/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1317
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1318
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0205.rows BesselBatch0205.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (14356433535933005759298450218643123900109/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (14356433535933005759298450218643123900109/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (3596806354346087099130552329040271952127/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3596806354346087099130552329040271952127/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (28743658953317354155820659534804211708617/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (28743658953317354155820659534804211708617/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0082.bracket1318 BracketBatch0082.bracket1319 (28743658953317354155820659534804211708617/20000000000000000000000000000000000000000) (98342884955788241961819094524675519187/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0082.bracket1318 BracketBatch0082.bracket1319
  (28743658953317354155820659534804211708617/20000000000000000000000000000000000000000) (98342884955788241961819094524675519187/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1318
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1319
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (2877445083476869679304441863232217561701/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2877445083476869679304441863232217561701/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0206.rows BesselBatch0206.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (7209080563040421426275986486792047142039/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7209080563040421426275986486792047142039/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0591.rows BesselBatch0591.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (28805386543465191249074182289745182092583/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (28805386543465191249074182289745182092583/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0164.rows ScalarLogs0164.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0082.bracket1319 BracketBatch0082.bracket1320 (28805386543465191249074182289745182092583/20000000000000000000000000000000000000000) (493483997657683881734046971319755645957/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0082.bracket1319 BracketBatch0082.bracket1320
  (28805386543465191249074182289745182092583/20000000000000000000000000000000000000000) (493483997657683881734046971319755645957/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1319
