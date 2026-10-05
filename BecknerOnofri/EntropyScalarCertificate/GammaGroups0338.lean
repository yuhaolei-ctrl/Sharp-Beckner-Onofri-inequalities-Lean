module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0422
public import BecknerOnofri.EntropyScalarCertificate.Bessel0423
public import BecknerOnofri.EntropyScalarCertificate.Bessel0700
public import BecknerOnofri.EntropyScalarCertificate.Brackets0169
public import BecknerOnofri.EntropyScalarCertificate.Logs0338
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2704
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (719647387108959140255560685747116003503189/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (719647387108959140255560685747116003503189/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (361899948474482608055377722220957924426157/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (361899948474482608055377722220957924426157/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (1443447284057924356366316130189031852355503/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1443447284057924356366316130189031852355503/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0169.bracket2704 BracketBatch0169.bracket2705 (1443447284057924356366316130189031852355503/20000000000000000000000000000000000000000) (5578407869855530444218453482195227668997/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0169.bracket2704 BracketBatch0169.bracket2705
  (1443447284057924356366316130189031852355503/20000000000000000000000000000000000000000) (5578407869855530444218453482195227668997/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2704
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2705
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (723799896948965216110755444441915848852311/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (723799896948965216110755444441915848852311/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (728000692234771048588653712378349962324229/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (728000692234771048588653712378349962324229/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (72590029459186813234970457841013290558827/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (72590029459186813234970457841013290558827/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0169.bracket2705 BracketBatch0169.bracket2706 (72590029459186813234970457841013290558827/1000000000000000000000000000000000000000) (1396681442754094620232021524647442300571/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0169.bracket2705 BracketBatch0169.bracket2706
  (72590029459186813234970457841013290558827/1000000000000000000000000000000000000000) (1396681442754094620232021524647442300571/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2705
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2706
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (364000346117385524294326856189174981162113/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (364000346117385524294326856189174981162113/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (366125310039695773031549461790506331149819/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (366125310039695773031549461790506331149819/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (182531414039270324331469079494920328077983/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (182531414039270324331469079494920328077983/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0169.bracket2706 BracketBatch0169.bracket2707 (182531414039270324331469079494920328077983/2500000000000000000000000000000000000000) (5595086223739188537673953160254191554347/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0169.bracket2706 BracketBatch0169.bracket2707
  (182531414039270324331469079494920328077983/2500000000000000000000000000000000000000) (5595086223739188537673953160254191554347/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2706
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2707
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (146450124015878309212619784716202532459927/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (146450124015878309212619784716202532459927/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (46034409220494536080598536226511650410537/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (46034409220494536080598536226511650410537/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (1468801167607304123352675503205199068868227/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1468801167607304123352675503205199068868227/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0169.bracket2707 BracketBatch0169.bracket2708 (1468801167607304123352675503205199068868227/20000000000000000000000000000000000000000) (5603489551254119434896163127624721232733/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0169.bracket2707 BracketBatch0169.bracket2708
  (1468801167607304123352675503205199068868227/20000000000000000000000000000000000000000) (5603489551254119434896163127624721232733/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2707
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2708
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (736550547527912577289576579624186406568589/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (736550547527912577289576579624186406568589/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (46306335134199825801598174690221828825469/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (46306335134199825801598174690221828825469/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (1477451909675109790115147374667735667776093/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1477451909675109790115147374667735667776093/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0169.bracket2708 BracketBatch0169.bracket2709 (1477451909675109790115147374667735667776093/20000000000000000000000000000000000000000) (561193607746189513451970742926697049181/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0169.bracket2708 BracketBatch0169.bracket2709
  (1477451909675109790115147374667735667776093/20000000000000000000000000000000000000000) (561193607746189513451970742926697049181/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2708
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2709
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (740901362147197212825570795043549261207501/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (740901362147197212825570795043549261207501/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (745303972636652903644513547946261555686093/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (745303972636652903644513547946261555686093/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (743102667391925058235042171494905408446797/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (743102667391925058235042171494905408446797/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0169.bracket2709 BracketBatch0169.bracket2710 (743102667391925058235042171494905408446797/10000000000000000000000000000000000000000) (2810213063387173936085619846681851290659/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0169.bracket2709 BracketBatch0169.bracket2710
  (743102667391925058235042171494905408446797/10000000000000000000000000000000000000000) (2810213063387173936085619846681851290659/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2709
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2710
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (74530397263665290364451354794626155568609/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (74530397263665290364451354794626155568609/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (29990372378437695628716334273316063035551/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (29990372378437695628716334273316063035551/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (299012656419519058872484380955832626314973/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (299012656419519058872484380955832626314973/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0169.bracket2710 BracketBatch0169.bracket2711 (299012656419519058872484380955832626314973/4000000000000000000000000000000000000000) (562896002394300811478606952386453843761/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0169.bracket2710 BracketBatch0169.bracket2711
  (299012656419519058872484380955832626314973/4000000000000000000000000000000000000000) (562896002394300811478606952386453843761/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2710
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2711
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (187439827365235597679477089208225393972193/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (187439827365235597679477089208225393972193/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (754268325505563683618503199646213552842099/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (754268325505563683618503199646213552842099/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (1504027634966506074336411556479115128730871/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1504027634966506074336411556479115128730871/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0338.rows ScalarLogs0338.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0169.bracket2711 BracketBatch0169.bracket2712 (1504027634966506074336411556479115128730871/20000000000000000000000000000000000000000) (2818769046937484827263714350513347863639/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0169.bracket2711 BracketBatch0169.bracket2712
  (1504027634966506074336411556479115128730871/20000000000000000000000000000000000000000) (2818769046937484827263714350513347863639/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2711
