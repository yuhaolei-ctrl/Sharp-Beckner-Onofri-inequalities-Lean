module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0337
public import BecknerOnofri.EntropyScalarCertificate.Bessel0338
public import BecknerOnofri.EntropyScalarCertificate.Bessel0657
public import BecknerOnofri.EntropyScalarCertificate.Bessel0658
public import BecknerOnofri.EntropyScalarCertificate.Brackets0135
public import BecknerOnofri.EntropyScalarCertificate.Logs0270
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2160
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (79931384926190233027822486383313813793493/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (79931384926190233027822486383313813793493/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (16035832411828496366845791631798550698327/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (16035832411828496366845791631798550698327/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (20013818373166589357756430567788320910641/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (20013818373166589357756430567788320910641/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0135.bracket2160 BracketBatch0135.bracket2161 (20013818373166589357756430567788320910641/2500000000000000000000000000000000000000) (123488156179254197335959476232802507569/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0135.bracket2160 BracketBatch0135.bracket2161
  (20013818373166589357756430567788320910641/2500000000000000000000000000000000000000) (123488156179254197335959476232802507569/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2160
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2161
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (5011197628696405114639309884937047093227/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5011197628696405114639309884937047093227/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (80428508961603803188516072124126882999761/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (80428508961603803188516072124126882999761/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (160607671020746285022745030283119636491393/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (160607671020746285022745030283119636491393/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0135.bracket2161 BracketBatch0135.bracket2162 (160607671020746285022745030283119636491393/20000000000000000000000000000000000000000) (309224721418757175083892096407578408481/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0135.bracket2161 BracketBatch0135.bracket2162
  (160607671020746285022745030283119636491393/20000000000000000000000000000000000000000) (309224721418757175083892096407578408481/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2161
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2162
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (40214254480801901594258036062063441499879/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (40214254480801901594258036062063441499879/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (16135888116435591701971390735659334035333/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (16135888116435591701971390735659334035333/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (161107949543781761698373025802423553176423/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (161107949543781761698373025802423553176423/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0135.bracket2162 BracketBatch0135.bracket2163 (161107949543781761698373025802423553176423/20000000000000000000000000000000000000000) (2477846355115229785152215522294545397991/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0135.bracket2162 BracketBatch0135.bracket2163
  (161107949543781761698373025802423553176423/20000000000000000000000000000000000000000) (2477846355115229785152215522294545397991/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2162
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2163
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0337.rows BesselBatch0337.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (40339720291088979254928476839148335088331/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (40339720291088979254928476839148335088331/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (10116496507487553076380938473464761682879/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10116496507487553076380938473464761682879/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (80805706321039191560452230733007381819847/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (80805706321039191560452230733007381819847/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0135.bracket2163 BracketBatch0135.bracket2164 (80805706321039191560452230733007381819847/10000000000000000000000000000000000000000) (496381793049633204613599782728094230081/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0135.bracket2163 BracketBatch0135.bracket2164
  (80805706321039191560452230733007381819847/10000000000000000000000000000000000000000) (496381793049633204613599782728094230081/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2163
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2164
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (80931972059900424611047507787718093463029/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (80931972059900424611047507787718093463029/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (40593059363640208753180487392507233422789/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (40593059363640208753180487392507233422789/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (162118090787180842117408482572732560308607/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (162118090787180842117408482572732560308607/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0135.bracket2164 BracketBatch0135.bracket2165 (162118090787180842117408482572732560308607/20000000000000000000000000000000000000000) (2485985692983872036876057267294552408197/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0135.bracket2164 BracketBatch0135.bracket2165
  (162118090787180842117408482572732560308607/20000000000000000000000000000000000000000) (2485985692983872036876057267294552408197/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2164
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2165
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (3247444749091216700254438991400578673823/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3247444749091216700254438991400578673823/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (2545059253543794275331468685128361168339/312500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2545059253543794275331468685128361168339/312500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (162628014840681834316967972709122024232423/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (162628014840681834316967972709122024232423/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0135.bracket2165 BracketBatch0135.bracket2166 (162628014840681834316967972709122024232423/20000000000000000000000000000000000000000) (2490076630435644887930843565795546393169/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0135.bracket2165 BracketBatch0135.bracket2166
  (162628014840681834316967972709122024232423/20000000000000000000000000000000000000000) (2490076630435644887930843565795546393169/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2165
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2166
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (16288379222680283362121399584821511477369/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (16288379222680283362121399584821511477369/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (81699319947081507461243095194298040593919/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (81699319947081507461243095194298040593919/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (40785304015120731067962523279601399495191/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (40785304015120731067962523279601399495191/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0135.bracket2166 BracketBatch0135.bracket2167 (40785304015120731067962523279601399495191/5000000000000000000000000000000000000000) (623545467651522368122906629774296873543/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0135.bracket2166 BracketBatch0135.bracket2167
  (40785304015120731067962523279601399495191/5000000000000000000000000000000000000000) (623545467651522368122906629774296873543/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2166
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2167
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (20424829986770376865310773798574510148479/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (20424829986770376865310773798574510148479/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (3278336246403795579023445216990831044451/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3278336246403795579023445216990831044451/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (163657726107176396936829225619068816705191/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (163657726107176396936829225619068816705191/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0270.rows ScalarLogs0270.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0135.bracket2167 BracketBatch0135.bracket2168 (163657726107176396936829225619068816705191/20000000000000000000000000000000000000000) (624575376849576196498128773574016390091/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0135.bracket2167 BracketBatch0135.bracket2168
  (163657726107176396936829225619068816705191/20000000000000000000000000000000000000000) (624575376849576196498128773574016390091/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2167
