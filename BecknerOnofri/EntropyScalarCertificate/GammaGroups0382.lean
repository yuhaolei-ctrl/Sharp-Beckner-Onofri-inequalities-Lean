module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0477
public import BecknerOnofri.EntropyScalarCertificate.Bessel0478
public import BecknerOnofri.EntropyScalarCertificate.Bessel0727
public import BecknerOnofri.EntropyScalarCertificate.Bessel0728
public import BecknerOnofri.EntropyScalarCertificate.Brackets0191
public import BecknerOnofri.EntropyScalarCertificate.Logs0382
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3056
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (183948785283156960832420526145733834610489/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (183948785283156960832420526145733834610489/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (184627099945930783897214851332697319749401/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (184627099945930783897214851332697319749401/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (36857588522908774472963537747843115435989/200000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (36857588522908774472963537747843115435989/200000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0191.bracket3056 BracketBatch0191.bracket3057 (36857588522908774472963537747843115435989/200000000000000000000000000000000000000) (3523728862556068813024639782103678814759/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0191.bracket3056 BracketBatch0191.bracket3057
  (36857588522908774472963537747843115435989/200000000000000000000000000000000000000) (3523728862556068813024639782103678814759/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3056
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3057
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (1846270999459307838972148513326973197494007/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1846270999459307838972148513326973197494007/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (1853104391687779238154491750697265066341443/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1853104391687779238154491750697265066341443/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (73987507822941741542532805280484765276709/400000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (73987507822941741542532805280484765276709/400000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0191.bracket3057 BracketBatch0191.bracket3058 (73987507822941741542532805280484765276709/400000000000000000000000000000000000000) (7053007419176717070196644558347648822707/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0191.bracket3057 BracketBatch0191.bracket3058
  (73987507822941741542532805280484765276709/400000000000000000000000000000000000000) (7053007419176717070196644558347648822707/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3057
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3058
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (5790951224024310119232786720928953332317/31250000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5790951224024310119232786720928953332317/31250000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (464997147469210154132751270929838904120621/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (464997147469210154132751270929838904120621/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (928273245391154963671374208604155170705981/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (928273245391154963671374208604155170705981/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0191.bracket3058 BracketBatch0191.bracket3059 (928273245391154963671374208604155170705981/5000000000000000000000000000000000000000) (1411715078437796563186533661556625064977/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0191.bracket3058 BracketBatch0191.bracket3059
  (928273245391154963671374208604155170705981/5000000000000000000000000000000000000000) (1411715078437796563186533661556625064977/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3058
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3059
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (1859988589876840616531005083719355616482481/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1859988589876840616531005083719355616482481/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (1866924162749928737360139384021495699586279/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1866924162749928737360139384021495699586279/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (93172818815669233847278611693521282901719/500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (93172818815669233847278611693521282901719/500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0191.bracket3059 BracketBatch0191.bracket3060 (93172818815669233847278611693521282901719/500000000000000000000000000000000000000) (7064161741171200837666673881265836149531/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0191.bracket3059 BracketBatch0191.bracket3060
  (93172818815669233847278611693521282901719/500000000000000000000000000000000000000) (7064161741171200837666673881265836149531/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3059
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3060
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (466731040687482184340034846005373924896569/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (466731040687482184340034846005373924896569/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (117119480471917603995371413463265190937997/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (117119480471917603995371413463265190937997/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (935208962575152600321520499858434688648557/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (935208962575152600321520499858434688648557/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0191.bracket3060 BracketBatch0191.bracket3061 (935208962575152600321520499858434688648557/5000000000000000000000000000000000000000) (3534883281758463433733543749962093439587/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0191.bracket3060 BracketBatch0191.bracket3061
  (935208962575152600321520499858434688648557/5000000000000000000000000000000000000000) (3534883281758463433733543749962093439587/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3060
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3061
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (1873911687550681663925942615412243055007949/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1873911687550681663925942615412243055007949/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (940475875101546459656475862821072763735643/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (940475875101546459656475862821072763735643/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (750972687550754916647778868210877716495847/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (750972687550754916647778868210877716495847/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0191.bracket3061 BracketBatch0191.bracket3062 (750972687550754916647778868210877716495847/4000000000000000000000000000000000000000) (7075389956980731200082107690515319355177/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0191.bracket3061 BracketBatch0191.bracket3062
  (750972687550754916647778868210877716495847/4000000000000000000000000000000000000000) (7075389956980731200082107690515319355177/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3061
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3062
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (1880951750203092919312951725642145527471283/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1880951750203092919312951725642145527471283/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (1888044945475291778100516057439328644613063/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1888044945475291778100516057439328644613063/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (1884498347839192348706733891540737086042173/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1884498347839192348706733891540737086042173/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0191.bracket3062 BracketBatch0191.bracket3063 (1884498347839192348706733891540737086042173/10000000000000000000000000000000000000000) (7081032019667317820029974081605825488887/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0191.bracket3062 BracketBatch0191.bracket3063
  (1884498347839192348706733891540737086042173/10000000000000000000000000000000000000000) (7081032019667317820029974081605825488887/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3062
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3063
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (94402247273764588905025802871966432230653/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (94402247273764588905025802871966432230653/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (1895191877147045837413809932737904350438421/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1895191877147045837413809932737904350438421/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (3783236822622337615514325990177232995051481/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3783236822622337615514325990177232995051481/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0382.rows ScalarLogs0382.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0191.bracket3063 BracketBatch0191.bracket3064 (3783236822622337615514325990177232995051481/20000000000000000000000000000000000000000) (7086692850020011770949485313471601343477/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0191.bracket3063 BracketBatch0191.bracket3064
  (3783236822622337615514325990177232995051481/20000000000000000000000000000000000000000) (7086692850020011770949485313471601343477/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3063
