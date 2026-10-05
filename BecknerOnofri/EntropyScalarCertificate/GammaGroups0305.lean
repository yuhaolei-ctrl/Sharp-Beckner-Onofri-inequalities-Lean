module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0381
public import BecknerOnofri.EntropyScalarCertificate.Bessel0382
public import BecknerOnofri.EntropyScalarCertificate.Bessel0679
public import BecknerOnofri.EntropyScalarCertificate.Bessel0680
public import BecknerOnofri.EntropyScalarCertificate.Brackets0152
public import BecknerOnofri.EntropyScalarCertificate.Brackets0153
public import BecknerOnofri.EntropyScalarCertificate.Logs0305
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2440
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (35831865594090761133969534525843291907327/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (35831865594090761133969534525843291907327/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (143653973802490553765200934115646650292533/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (143653973802490553765200934115646650292533/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (286981436178853598301079072219019817921841/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (286981436178853598301079072219019817921841/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0152.bracket2440 BracketBatch0152.bracket2441 (286981436178853598301079072219019817921841/10000000000000000000000000000000000000000) (846421352766402731395771305719618491421/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0152.bracket2440 BracketBatch0152.bracket2441
  (286981436178853598301079072219019817921841/10000000000000000000000000000000000000000) (846421352766402731395771305719618491421/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2440
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2441
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (287307947604981107530401868231293300585063/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (287307947604981107530401868231293300585063/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (57592793231797488608687214902205968279463/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (57592793231797488608687214902205968279463/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (287635956881984275286918971371161570991189/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (287635956881984275286918971371161570991189/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0152.bracket2441 BracketBatch0152.bracket2442 (287635956881984275286918971371161570991189/10000000000000000000000000000000000000000) (4235389441905424898805874007738843148411/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0152.bracket2441 BracketBatch0152.bracket2442
  (287635956881984275286918971371161570991189/10000000000000000000000000000000000000000) (4235389441905424898805874007738843148411/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2441
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2442
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (4499436971234178797553688664234841271833/156250000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4499436971234178797553688664234841271833/156250000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (288623001074727567320102355889884301743843/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (288623001074727567320102355889884301743843/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (115317393446743002072707686080182828628231/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (115317393446743002072707686080182828628231/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0152.bracket2442 BracketBatch0152.bracket2443 (115317393446743002072707686080182828628231/4000000000000000000000000000000000000000) (2119340578784648557397992485408868960713/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0152.bracket2442 BracketBatch0152.bracket2443
  (115317393446743002072707686080182828628231/4000000000000000000000000000000000000000) (2119340578784648557397992485408868960713/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2442
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2443
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (1803893756717047295750639724311776885899/62500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1803893756717047295750639724311776885899/62500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (144642536601299273346792767287220244598953/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (144642536601299273346792767287220244598953/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (288954037138663057006843945232162395470873/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (288954037138663057006843945232162395470873/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0152.bracket2443 BracketBatch0152.bracket2444 (288954037138663057006843945232162395470873/10000000000000000000000000000000000000000) (424198088597596219074238343432901535907/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0152.bracket2443 BracketBatch0152.bracket2444
  (288954037138663057006843945232162395470873/10000000000000000000000000000000000000000) (424198088597596219074238343432901535907/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2443
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2444
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0381.rows BesselBatch0381.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (289285073202598546693585534574440489197903/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (289285073202598546693585534574440489197903/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (289950203585610824963533518936236541121813/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (289950203585610824963533518936236541121813/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (144808819197052342914279763377669257579929/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (144808819197052342914279763377669257579929/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0152.bracket2444 BracketBatch0152.bracket2445 (144808819197052342914279763377669257579929/5000000000000000000000000000000000000000) (530661082997094817218255056951670811247/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0152.bracket2444 BracketBatch0152.bracket2445
  (144808819197052342914279763377669257579929/5000000000000000000000000000000000000000) (530661082997094817218255056951670811247/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2444
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2445
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (28995020358561082496353351893623654112181/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (28995020358561082496353351893623654112181/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (290618413461617544889174068680870979953969/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (290618413461617544889174068680870979953969/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0679.rows BesselBatch0679.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (580568617047228369852707587617107521075779/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (580568617047228369852707587617107521075779/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0152.bracket2445 BracketBatch0152.bracket2446 (580568617047228369852707587617107521075779/20000000000000000000000000000000000000000) (4248604528671050861062388523612614116237/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0152.bracket2445 BracketBatch0152.bracket2446
  (580568617047228369852707587617107521075779/20000000000000000000000000000000000000000) (4248604528671050861062388523612614116237/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2445
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2446
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (145309206730808772444587034340435489976983/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (145309206730808772444587034340435489976983/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (291289724265574904320391247774418289942791/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (291289724265574904320391247774418289942791/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (581908137727192449209565316455289269896757/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (581908137727192449209565316455289269896757/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0152.bracket2446 BracketBatch0152.bracket2447 (581908137727192449209565316455289269896757/20000000000000000000000000000000000000000) (425192851740841122616298546662676079957/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0152.bracket2446 BracketBatch0152.bracket2447
  (581908137727192449209565316455289269896757/20000000000000000000000000000000000000000) (425192851740841122616298546662676079957/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2446
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2447
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (72822431066393726080097811943604572485697/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (72822431066393726080097811943604572485697/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0382.rows BesselBatch0382.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (291964157631834052181798112942432855615953/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (291964157631834052181798112942432855615953/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0680.rows BesselBatch0680.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (583253881897408956502189360716851145558741/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (583253881897408956502189360716851145558741/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0305.rows ScalarLogs0305.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0152.bracket2447 BracketBatch0153.bracket2448 (583253881897408956502189360716851145558741/20000000000000000000000000000000000000000) (1063815166947705884046525078352268460399/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0152.bracket2447 BracketBatch0153.bracket2448
  (583253881897408956502189360716851145558741/20000000000000000000000000000000000000000) (1063815166947705884046525078352268460399/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2447
