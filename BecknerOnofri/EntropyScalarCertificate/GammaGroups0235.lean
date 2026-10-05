module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0293
public import BecknerOnofri.EntropyScalarCertificate.Bessel0294
public import BecknerOnofri.EntropyScalarCertificate.Bessel0295
public import BecknerOnofri.EntropyScalarCertificate.Bessel0635
public import BecknerOnofri.EntropyScalarCertificate.Bessel0636
public import BecknerOnofri.EntropyScalarCertificate.Brackets0117
public import BecknerOnofri.EntropyScalarCertificate.Brackets0118
public import BecknerOnofri.EntropyScalarCertificate.Logs0235
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1880
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (26771820538108777383598653296230658716081/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (26771820538108777383598653296230658716081/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (26897941817963190402404257495161513504927/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (26897941817963190402404257495161513504927/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (3354360147254497986625181924462010763813/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3354360147254497986625181924462010763813/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0117.bracket1880 BracketBatch0117.bracket1881 (3354360147254497986625181924462010763813/1250000000000000000000000000000000000000) (556763529351026421313934098737646448113/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0117.bracket1880 BracketBatch0117.bracket1881
  (3354360147254497986625181924462010763813/1250000000000000000000000000000000000000) (556763529351026421313934098737646448113/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1880
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1881
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (6724485454490797600601064373790378376231/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6724485454490797600601064373790378376231/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (2702537855984043327046336308303070390209/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2702537855984043327046336308303070390209/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (26961660188901811836433810289096108703507/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (26961660188901811836433810289096108703507/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0117.bracket1881 BracketBatch0117.bracket1882 (26961660188901811836433810289096108703507/10000000000000000000000000000000000000000) (279709319045750528077578077497482050887/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0117.bracket1881 BracketBatch0117.bracket1882
  (26961660188901811836433810289096108703507/10000000000000000000000000000000000000000) (279709319045750528077578077497482050887/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1881
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1882
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (27025378559840433270463363083030703902087/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (27025378559840433270463363083030703902087/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (27154151024657124815283544478911111839427/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (27154151024657124815283544478911111839427/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (27089764792248779042873453780970907870757/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (27089764792248779042873453780970907870757/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0117.bracket1882 BracketBatch0117.bracket1883 (27089764792248779042873453780970907870757/10000000000000000000000000000000000000000) (14052300993200790299328532177600445559/125000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0117.bracket1882 BracketBatch0117.bracket1883
  (27089764792248779042873453780970907870757/10000000000000000000000000000000000000000) (14052300993200790299328532177600445559/125000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1882
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1883
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (424283609760267575238805382482986122491/156250000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (424283609760267575238805382482986122491/156250000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (6821069971118328373610567924235545491993/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6821069971118328373610567924235545491993/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (13609607727282609577431454043963323451849/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (13609607727282609577431454043963323451849/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0117.bracket1883 BracketBatch0117.bracket1884 (13609607727282609577431454043963323451849/5000000000000000000000000000000000000000) (282391954463444380914214341999831426533/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0117.bracket1883 BracketBatch0117.bracket1884
  (13609607727282609577431454043963323451849/5000000000000000000000000000000000000000) (282391954463444380914214341999831426533/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1883
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1884
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (27284279884473313494442271696942181967969/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (27284279884473313494442271696942181967969/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (685394655829000358541696963726862811253/250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (685394655829000358541696963726862811253/250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (54700066117633327836110150246016694418089/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (54700066117633327836110150246016694418089/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0117.bracket1884 BracketBatch0117.bracket1885 (54700066117633327836110150246016694418089/20000000000000000000000000000000000000000) (567494422671434897674765696715418841409/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0117.bracket1884 BracketBatch0117.bracket1885
  (54700066117633327836110150246016694418089/20000000000000000000000000000000000000000) (567494422671434897674765696715418841409/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1884
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1885
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (27415786233160014341667878549074512450117/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (27415786233160014341667878549074512450117/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (27548691597405318051190282746500803796973/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (27548691597405318051190282746500803796973/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (5496447783056533239285816129557531624709/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5496447783056533239285816129557531624709/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0117.bracket1885 BracketBatch0117.bracket1886 (5496447783056533239285816129557531624709/2000000000000000000000000000000000000000) (71277970038916280889806884820755465901/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0117.bracket1885 BracketBatch0117.bracket1886
  (5496447783056533239285816129557531624709/2000000000000000000000000000000000000000) (71277970038916280889806884820755465901/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1885
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1886
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (2754869159740531805119028274650080379697/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2754869159740531805119028274650080379697/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (27683017948071539802685043363318654956671/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (27683017948071539802685043363318654956671/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (55231709545476857853875326109819458753641/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (55231709545476857853875326109819458753641/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0117.bracket1886 BracketBatch0117.bracket1887 (55231709545476857853875326109819458753641/20000000000000000000000000000000000000000) (572972103613161974116522824608014684127/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0117.bracket1886 BracketBatch0117.bracket1887
  (55231709545476857853875326109819458753641/20000000000000000000000000000000000000000) (572972103613161974116522824608014684127/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1886
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1887
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0294.rows BesselBatch0294.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (6920754487017884950671260840829663739167/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6920754487017884950671260840829663739167/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0295.rows BesselBatch0295.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (278187877119163933377685499736545430653/100000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (278187877119163933377685499736545430653/100000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0636.rows BesselBatch0636.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (3468862853749245821278349583560824876373/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3468862853749245821278349583560824876373/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0235.rows ScalarLogs0235.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0117.bracket1887 BracketBatch0118.bracket1888 (3468862853749245821278349583560824876373/1250000000000000000000000000000000000000) (575739636812537824421430476516110442651/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0117.bracket1887 BracketBatch0118.bracket1888
  (3468862853749245821278349583560824876373/1250000000000000000000000000000000000000) (575739636812537824421430476516110442651/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1887
