module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0158
public import BecknerOnofri.EntropyScalarCertificate.Bessel0159
public import BecknerOnofri.EntropyScalarCertificate.Bessel0160
public import BecknerOnofri.EntropyScalarCertificate.Bessel0568
public import BecknerOnofri.EntropyScalarCertificate.Brackets0063
public import BecknerOnofri.EntropyScalarCertificate.Brackets0064
public import BecknerOnofri.EntropyScalarCertificate.Logs0127
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1016
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (5765291561520002152709248872953396685049/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5765291561520002152709248872953396685049/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (1445232142722213804701117095977772627121/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1445232142722213804701117095977772627121/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (11546220132408857371513717256864487193533/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (11546220132408857371513717256864487193533/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0063.bracket1016 BracketBatch0063.bracket1017 (11546220132408857371513717256864487193533/20000000000000000000000000000000000000000) (26802205624675964197232816286272360151/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0063.bracket1016 BracketBatch0063.bracket1017
  (11546220132408857371513717256864487193533/20000000000000000000000000000000000000000) (26802205624675964197232816286272360151/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1016
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1017
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (5780928570888855218804468383911090508481/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5780928570888855218804468383911090508481/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (2898299801875345905013303682639098051199/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2898299801875345905013303682639098051199/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (11577528174639547028831075749189286610879/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (11577528174639547028831075749189286610879/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0063.bracket1017 BracketBatch0063.bracket1018 (11577528174639547028831075749189286610879/20000000000000000000000000000000000000000) (54064932093144945063522345580456271041/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0063.bracket1017 BracketBatch0063.bracket1018
  (11577528174639547028831075749189286610879/20000000000000000000000000000000000000000) (54064932093144945063522345580456271041/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1017
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1018
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (1159319920750138362005321473055639220479/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1159319920750138362005321473055639220479/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (5812304862941169762109485312515889559633/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5812304862941169762109485312515889559633/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (2902226116672965393034023169448521415507/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2902226116672965393034023169448521415507/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0063.bracket1018 BracketBatch0063.bracket1019 (2902226116672965393034023169448521415507/5000000000000000000000000000000000000000) (27264315798434897135311485142415000903/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0063.bracket1018 BracketBatch0063.bracket1019
  (2902226116672965393034023169448521415507/5000000000000000000000000000000000000000) (27264315798434897135311485142415000903/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1018
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1019
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (581230486294116976210948531251588955963/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (581230486294116976210948531251588955963/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (1165608910572489681902288236336788498811/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1165608910572489681902288236336788498811/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (2328069883160723634324185298839966410737/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2328069883160723634324185298839966410737/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0063.bracket1019 BracketBatch0063.bracket1020 (2328069883160723634324185298839966410737/4000000000000000000000000000000000000000) (10999105535711299645354673239646647491/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0063.bracket1019 BracketBatch0063.bracket1020
  (2328069883160723634324185298839966410737/4000000000000000000000000000000000000000) (10999105535711299645354673239646647491/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1019
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1020
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (1457011138215612102377860295420985623513/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1457011138215612102377860295420985623513/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (730477359937422007460238742258581592083/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (730477359937422007460238742258581592083/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (2917965858090456117298337779938148807679/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2917965858090456117298337779938148807679/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0063.bracket1020 BracketBatch0063.bracket1021 (2917965858090456117298337779938148807679/5000000000000000000000000000000000000000) (55465638355266726729786434749528623891/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0063.bracket1020 BracketBatch0063.bracket1021
  (2917965858090456117298337779938148807679/5000000000000000000000000000000000000000) (55465638355266726729786434749528623891/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1020
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1021
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (5843818879499376059681909938068652736661/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5843818879499376059681909938068652736661/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (5859628050435880349812012487786430657211/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5859628050435880349812012487786430657211/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (731465433120953525593370151615942712117/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (731465433120953525593370151615942712117/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0063.bracket1021 BracketBatch0063.bracket1022 (731465433120953525593370151615942712117/1250000000000000000000000000000000000000) (55938981743882195893353551209451088671/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0063.bracket1021 BracketBatch0063.bracket1022
  (731465433120953525593370151615942712117/1250000000000000000000000000000000000000) (55938981743882195893353551209451088671/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1021
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1022
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (732453506304485043726501560973303832151/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (732453506304485043726501560973303832151/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (5875472274871564490930821841151994376809/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5875472274871564490930821841151994376809/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (11735100325307444840742834328938425034017/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (11735100325307444840742834328938425034017/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0063.bracket1022 BracketBatch0063.bracket1023 (11735100325307444840742834328938425034017/20000000000000000000000000000000000000000) (56415576061902383826959062915986361399/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0063.bracket1022 BracketBatch0063.bracket1023
  (11735100325307444840742834328938425034017/20000000000000000000000000000000000000000) (56415576061902383826959062915986361399/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1022
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1023
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (2937736137435782245465410920575997188403/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2937736137435782245465410920575997188403/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (2945675881819256227640486185228991329871/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2945675881819256227640486185228991329871/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (2941706009627519236552948552902494259137/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2941706009627519236552948552902494259137/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0127.rows ScalarLogs0127.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0063.bracket1023 BracketBatch0064.bracket1024 (2941706009627519236552948552902494259137/5000000000000000000000000000000000000000) (2844771981412584938101420540730410449/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0063.bracket1023 BracketBatch0064.bracket1024
  (2941706009627519236552948552902494259137/5000000000000000000000000000000000000000) (2844771981412584938101420540730410449/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1023
