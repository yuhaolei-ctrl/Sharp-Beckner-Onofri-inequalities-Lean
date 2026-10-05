module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0245
public import BecknerOnofri.EntropyScalarCertificate.Bessel0246
public import BecknerOnofri.EntropyScalarCertificate.Bessel0611
public import BecknerOnofri.EntropyScalarCertificate.Bessel0612
public import BecknerOnofri.EntropyScalarCertificate.Brackets0098
public import BecknerOnofri.EntropyScalarCertificate.Logs0196
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1568
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (18295336023929408203648426153232136237589/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18295336023929408203648426153232136237589/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (2288242804407098865960861896184839288041/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2288242804407098865960861896184839288041/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (36601278459186199131335321322710850541917/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (36601278459186199131335321322710850541917/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0098.bracket1568 BracketBatch0098.bracket1569 (36601278459186199131335321322710850541917/20000000000000000000000000000000000000000) (142460504860910966460118416070307618941/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0098.bracket1568 BracketBatch0098.bracket1569
  (36601278459186199131335321322710850541917/20000000000000000000000000000000000000000) (142460504860910966460118416070307618941/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1568
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1569
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (732237697410271637107475806779148572173/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (732237697410271637107475806779148572173/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (2289570370722682875693814128528438164449/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2289570370722682875693814128528438164449/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (36622505401038253933237408197706219619917/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (36622505401038253933237408197706219619917/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0098.bracket1569 BracketBatch0098.bracket1570 (36622505401038253933237408197706219619917/20000000000000000000000000000000000000000) (89108647062601789631420672665168957821/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0098.bracket1569 BracketBatch0098.bracket1570
  (36622505401038253933237408197706219619917/20000000000000000000000000000000000000000) (89108647062601789631420672665168957821/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1569
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1570
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (18316562965781463005550513028227505315589/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18316562965781463005550513028227505315589/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (18327197645307287187536591982005891519217/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (18327197645307287187536591982005891519217/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (18321880305544375096543552505116698417403/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (18321880305544375096543552505116698417403/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0098.bracket1570 BracketBatch0098.bracket1571 (18321880305544375096543552505116698417403/10000000000000000000000000000000000000000) (89179554406758869785458557939929480269/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0098.bracket1570 BracketBatch0098.bracket1571
  (18321880305544375096543552505116698417403/10000000000000000000000000000000000000000) (89179554406758869785458557939929480269/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1570
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1571
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (9163598822653643593768295991002945759607/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9163598822653643593768295991002945759607/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (9168923251859171469270581035926870347681/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9168923251859171469270581035926870347681/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (2291565259314101882879859628366227013411/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2291565259314101882879859628366227013411/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0098.bracket1571 BracketBatch0098.bracket1572 (2291565259314101882879859628366227013411/1250000000000000000000000000000000000000) (142800860300949042641087065503007487159/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0098.bracket1571 BracketBatch0098.bracket1572
  (2291565259314101882879859628366227013411/1250000000000000000000000000000000000000) (142800860300949042641087065503007487159/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1571
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1572
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (18337846503718342938541162071853740695359/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18337846503718342938541162071853740695359/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (18348509570979184755930472466245065528939/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (18348509570979184755930472466245065528939/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (18343178037348763847235817269049403112149/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (18343178037348763847235817269049403112149/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0098.bracket1572 BracketBatch0098.bracket1573 (18343178037348763847235817269049403112149/10000000000000000000000000000000000000000) (714572776195034115907719357342662764189/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0098.bracket1572 BracketBatch0098.bracket1573
  (18343178037348763847235817269049403112149/10000000000000000000000000000000000000000) (714572776195034115907719357342662764189/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1572
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1573
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (2293563696372398094491309058280633191117/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2293563696372398094491309058280633191117/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (458979671928377536704531557748929859699/250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (458979671928377536704531557748929859699/250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (1147115514003571444503491711756320622403/625000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1147115514003571444503491711756320622403/625000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0098.bracket1573 BracketBatch0098.bracket1574 (1147115514003571444503491711756320622403/625000000000000000000000000000000000000) (143028372053782965013166293752919609851/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0098.bracket1573 BracketBatch0098.bracket1574
  (1147115514003571444503491711756320622403/625000000000000000000000000000000000000) (143028372053782965013166293752919609851/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1573
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1574
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0245.rows BesselBatch0245.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (18359186877135101468181262309957194387957/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18359186877135101468181262309957194387957/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (9184939226156188259367310410711660388781/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9184939226156188259367310410711660388781/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (36729065329447477986915883131380515165519/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (36729065329447477986915883131380515165519/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0098.bracket1574 BracketBatch0098.bracket1575 (36729065329447477986915883131380515165519/20000000000000000000000000000000000000000) (715711554672148179752587326384467424493/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0098.bracket1574 BracketBatch0098.bracket1575
  (36729065329447477986915883131380515165519/20000000000000000000000000000000000000000) (715711554672148179752587326384467424493/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1574
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1575
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (18369878452312376518734620821423320777559/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18369878452312376518734620821423320777559/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (3676116865343709847906503443609410011817/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3676116865343709847906503443609410011817/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0611.rows BesselBatch0611.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (9187615694757731439566784509867592709161/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9187615694757731439566784509867592709161/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0196.rows ScalarLogs0196.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0098.bracket1575 BracketBatch0098.bracket1576 (9187615694757731439566784509867592709161/5000000000000000000000000000000000000000) (716281860352282263398742020898833959599/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0098.bracket1575 BracketBatch0098.bracket1576
  (9187615694757731439566784509867592709161/5000000000000000000000000000000000000000) (716281860352282263398742020898833959599/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1575
