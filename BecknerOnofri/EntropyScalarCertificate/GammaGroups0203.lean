module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0253
public import BecknerOnofri.EntropyScalarCertificate.Bessel0254
public import BecknerOnofri.EntropyScalarCertificate.Bessel0255
public import BecknerOnofri.EntropyScalarCertificate.Bessel0615
public import BecknerOnofri.EntropyScalarCertificate.Bessel0616
public import BecknerOnofri.EntropyScalarCertificate.Brackets0101
public import BecknerOnofri.EntropyScalarCertificate.Brackets0102
public import BecknerOnofri.EntropyScalarCertificate.Logs0203
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1624
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (4727973816899566841118703450308384226677/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4727973816899566841118703450308384226677/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (3784668114860783534343193628047053815163/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3784668114860783534343193628047053815163/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (37835235841902185036190781941468805982523/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (37835235841902185036190781941468805982523/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0101.bracket1624 BracketBatch0101.bracket1625 (37835235841902185036190781941468805982523/20000000000000000000000000000000000000000) (37249793993410736070499794574652248489/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0101.bracket1624 BracketBatch0101.bracket1625
  (37835235841902185036190781941468805982523/20000000000000000000000000000000000000000) (37249793993410736070499794574652248489/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1624
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1625
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (4730835143575979417928992035058817268953/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4730835143575979417928992035058817268953/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (18934801800295513586242622973331488194893/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (18934801800295513586242622973331488194893/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (7571628474919886251591718222713351454141/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7571628474919886251591718222713351454141/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0101.bracket1625 BracketBatch0101.bracket1626 (7571628474919886251591718222713351454141/4000000000000000000000000000000000000000) (372798999042880262151488660243688305629/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0101.bracket1625 BracketBatch0101.bracket1626
  (7571628474919886251591718222713351454141/4000000000000000000000000000000000000000) (372798999042880262151488660243688305629/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1625
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1626
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (1893480180029551358624262297333148819489/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1893480180029551358624262297333148819489/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (18946278980295780834382095100498879680091/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (18946278980295780834382095100498879680091/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (37881080780591294420624718073830367874981/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (37881080780591294420624718073830367874981/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0101.bracket1626 BracketBatch0101.bracket1627 (37881080780591294420624718073830367874981/20000000000000000000000000000000000000000) (373100389180621526686819297246025481071/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0101.bracket1626 BracketBatch0101.bracket1627
  (37881080780591294420624718073830367874981/20000000000000000000000000000000000000000) (373100389180621526686819297246025481071/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1626
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1627
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (2368284872536972604297761887562359960011/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2368284872536972604297761887562359960011/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (9478886074561885397342164315617335633351/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9478886074561885397342164315617335633351/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (3790405112941955162906642373173355094679/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3790405112941955162906642373173355094679/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0101.bracket1627 BracketBatch0101.bracket1628 (3790405112941955162906642373173355094679/2000000000000000000000000000000000000000) (746804221740273449187107764391433250769/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0101.bracket1627 BracketBatch0101.bracket1628
  (3790405112941955162906642373173355094679/2000000000000000000000000000000000000000) (746804221740273449187107764391433250769/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1627
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1628
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (18957772149123770794684328631234671266699/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18957772149123770794684328631234671266699/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (3793856268339036263596770134682161316021/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3793856268339036263596770134682161316021/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (9481763372704738028167044826161369461701/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9481763372704738028167044826161369461701/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0101.bracket1628 BracketBatch0101.bracket1629 (9481763372704738028167044826161369461701/5000000000000000000000000000000000000000) (46713020579403229967875912825071913023/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0101.bracket1628 BracketBatch0101.bracket1629
  (9481763372704738028167044826161369461701/5000000000000000000000000000000000000000) (46713020579403229967875912825071913023/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1628
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1629
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (9484640670847590658991925336705403290051/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9484640670847590658991925336705403290051/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (18980806593022678819251252553555115833003/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (18980806593022678819251252553555115833003/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (7590017586943572027447020645393184482621/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7590017586943572027447020645393184482621/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0101.bracket1629 BracketBatch0101.bracket1630 (7590017586943572027447020645393184482621/4000000000000000000000000000000000000000) (748013102001370604007458412926840141293/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0101.bracket1629 BracketBatch0101.bracket1630
  (7590017586943572027447020645393184482621/4000000000000000000000000000000000000000) (748013102001370604007458412926840141293/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1629
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1630
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (18980806593022678819251252553555115833/10000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18980806593022678819251252553555115833/10000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (2374043492277027705913870655899101826093/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2374043492277027705913870655899101826093/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (2373322158202431279160138612546745652609/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2373322158202431279160138612546745652609/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0101.bracket1630 BracketBatch0101.bracket1631 (2373322158202431279160138612546745652609/1250000000000000000000000000000000000000) (748618540984620049886505696211229545343/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0101.bracket1630 BracketBatch0101.bracket1631
  (2373322158202431279160138612546745652609/1250000000000000000000000000000000000000) (748618540984620049886505696211229545343/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1630
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1631
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0254.rows BesselBatch0254.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (18992347938216221647310965247192814608741/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18992347938216221647310965247192814608741/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (4750976353120846184634255075698154837113/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4750976353120846184634255075698154837113/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (37996253350699606385847985549985433957193/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (37996253350699606385847985549985433957193/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0203.rows ScalarLogs0203.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0101.bracket1631 BracketBatch0102.bracket1632 (37996253350699606385847985549985433957193/20000000000000000000000000000000000000000) (749224647273790897701369701274981785791/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0101.bracket1631 BracketBatch0102.bracket1632
  (37996253350699606385847985549985433957193/20000000000000000000000000000000000000000) (749224647273790897701369701274981785791/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1631
