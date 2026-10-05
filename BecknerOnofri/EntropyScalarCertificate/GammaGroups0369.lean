module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0461
public import BecknerOnofri.EntropyScalarCertificate.Bessel0462
public import BecknerOnofri.EntropyScalarCertificate.Bessel0719
public import BecknerOnofri.EntropyScalarCertificate.Bessel0720
public import BecknerOnofri.EntropyScalarCertificate.Brackets0184
public import BecknerOnofri.EntropyScalarCertificate.Brackets0185
public import BecknerOnofri.EntropyScalarCertificate.Logs0369
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2952
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (1331040775726377795310523506442158775004357/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1331040775726377795310523506442158775004357/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (667293432776610791789462800172136776065223/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (667293432776610791789462800172136776065223/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (2665627641279599378889449106786432327134803/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2665627641279599378889449106786432327134803/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0184.bracket2952 BracketBatch0184.bracket2953 (2665627641279599378889449106786432327134803/20000000000000000000000000000000000000000) (6553726253078826646030537504948479843483/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0184.bracket2952 BracketBatch0184.bracket2953
  (2665627641279599378889449106786432327134803/20000000000000000000000000000000000000000) (6553726253078826646030537504948479843483/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2952
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2953
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (1334586865553221583578925600344273552130443/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1334586865553221583578925600344273552130443/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (267630383695623275054075879712866203152581/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (267630383695623275054075879712866203152581/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (668184696007834489712326249727151141973337/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (668184696007834489712326249727151141973337/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0184.bracket2953 BracketBatch0184.bracket2954 (668184696007834489712326249727151141973337/5000000000000000000000000000000000000000) (6557816377424596160312918581336054776641/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0184.bracket2953 BracketBatch0184.bracket2954
  (668184696007834489712326249727151141973337/5000000000000000000000000000000000000000) (6557816377424596160312918581336054776641/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2953
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2954
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (669075959239058187635189699282165507881451/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (669075959239058187635189699282165507881451/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (268347217403855023856663032371794023126057/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (268347217403855023856663032371794023126057/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (2679888005497391494553694560423301131393187/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2679888005497391494553694560423301131393187/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0184.bracket2954 BracketBatch0184.bracket2955 (2679888005497391494553694560423301131393187/20000000000000000000000000000000000000000) (3280958587899245383538777024924281264413/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0184.bracket2954 BracketBatch0184.bracket2955
  (2679888005497391494553694560423301131393187/20000000000000000000000000000000000000000) (3280958587899245383538777024924281264413/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2954
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2955
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (670868043509637559641657580929485057815141/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (670868043509637559641657580929485057815141/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (1345339525334891549059467822234947115895947/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1345339525334891549059467822234947115895947/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (2687075612354166668342782984093917231526229/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2687075612354166668342782984093917231526229/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0184.bracket2955 BracketBatch0184.bracket2956 (2687075612354166668342782984093917231526229/20000000000000000000000000000000000000000) (6566028699791729020639197619623322355667/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0184.bracket2955 BracketBatch0184.bracket2956
  (2687075612354166668342782984093917231526229/20000000000000000000000000000000000000000) (6566028699791729020639197619623322355667/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2955
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2956
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (168167440666861443632433477779368389486993/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (168167440666861443632433477779368389486993/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (337240597311310587372862539063686306713533/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (337240597311310587372862539063686306713533/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (673575478645033474637729494622423085687519/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (673575478645033474637729494622423085687519/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0184.bracket2956 BracketBatch0184.bracket2957 (673575478645033474637729494622423085687519/5000000000000000000000000000000000000000) (131403020026716143075755534118594341277/200000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0184.bracket2956 BracketBatch0184.bracket2957
  (673575478645033474637729494622423085687519/5000000000000000000000000000000000000000) (131403020026716143075755534118594341277/200000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2956
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2957
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (1348962389245242349491450156254745226854129/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1348962389245242349491450156254745226854129/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (676302418127573868673873033672998514986937/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (676302418127573868673873033672998514986937/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (2701567225500390086839196223600742256828003/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2701567225500390086839196223600742256828003/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0184.bracket2957 BracketBatch0184.bracket2958 (2701567225500390086839196223600742256828003/20000000000000000000000000000000000000000) (3287142066352480830630452489317960251429/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0184.bracket2957 BracketBatch0184.bracket2958
  (2701567225500390086839196223600742256828003/20000000000000000000000000000000000000000) (3287142066352480830630452489317960251429/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2957
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2958
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (1352604836255147737347746067345997029973871/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1352604836255147737347746067345997029973871/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (135626702557679725438754116075345052479213/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (135626702557679725438754116075345052479213/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (2708871861831944991735287228099447554766001/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2708871861831944991735287228099447554766001/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0184.bracket2958 BracketBatch0184.bracket2959 (2708871861831944991735287228099447554766001/20000000000000000000000000000000000000000) (26313712586074570660293799831488537681/40000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0184.bracket2958 BracketBatch0184.bracket2959
  (2708871861831944991735287228099447554766001/20000000000000000000000000000000000000000) (26313712586074570660293799831488537681/40000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2958
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2959
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (1356267025576797254387541160753450524792127/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1356267025576797254387541160753450524792127/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0462.rows BesselBatch0462.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (679974559076473860072951910251743346691287/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (679974559076473860072951910251743346691287/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0720.rows BesselBatch0720.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (2716216143729744974533444981256937218174701/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2716216143729744974533444981256937218174701/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0369.rows ScalarLogs0369.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0184.bracket2959 BracketBatch0185.bracket2960 (2716216143729744974533444981256937218174701/20000000000000000000000000000000000000000) (3291291547871998877388131872988273050143/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0184.bracket2959 BracketBatch0185.bracket2960
  (2716216143729744974533444981256937218174701/20000000000000000000000000000000000000000) (3291291547871998877388131872988273050143/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2959
