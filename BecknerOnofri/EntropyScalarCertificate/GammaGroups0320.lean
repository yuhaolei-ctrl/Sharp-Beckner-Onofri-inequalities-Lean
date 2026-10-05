module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0400
public import BecknerOnofri.EntropyScalarCertificate.Bessel0401
public import BecknerOnofri.EntropyScalarCertificate.Bessel0688
public import BecknerOnofri.EntropyScalarCertificate.Bessel0689
public import BecknerOnofri.EntropyScalarCertificate.Brackets0160
public import BecknerOnofri.EntropyScalarCertificate.Logs0320
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2560
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (197171940110647422214116793656157007704547/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (197171940110647422214116793656157007704547/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (395583847042091960862572385275415163717927/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (395583847042091960862572385275415163717927/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (789927727263386805290805972587729179127021/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (789927727263386805290805972587729179127021/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0160.bracket2560 BracketBatch0160.bracket2561 (789927727263386805290805972587729179127021/20000000000000000000000000000000000000000) (1174027023225091945479441179251214334559/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0160.bracket2560 BracketBatch0160.bracket2561
  (789927727263386805290805972587729179127021/20000000000000000000000000000000000000000) (1174027023225091945479441179251214334559/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2560
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2561
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (98895961760522990215643096318853790929481/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (98895961760522990215643096318853790929481/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (396831662003346101578884615007471949437213/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (396831662003346101578884615007471949437213/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (792415509045438062441457000282887113155137/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (792415509045438062441457000282887113155137/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0160.bracket2561 BracketBatch0160.bracket2562 (792415509045438062441457000282887113155137/20000000000000000000000000000000000000000) (4700709939583023209851706189461864292721/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0160.bracket2561 BracketBatch0160.bracket2562
  (792415509045438062441457000282887113155137/20000000000000000000000000000000000000000) (4700709939583023209851706189461864292721/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2561
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2562
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (39683166200334610157888461500747194943721/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (39683166200334610157888461500747194943721/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (398087399849212752149393429979282794304489/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (398087399849212752149393429979282794304489/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (794919061852558853728278044986754743741699/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (794919061852558853728278044986754743741699/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0160.bracket2562 BracketBatch0160.bracket2563 (794919061852558853728278044986754743741699/20000000000000000000000000000000000000000) (2352663457632164405575140565484121801053/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0160.bracket2562 BracketBatch0160.bracket2563
  (794919061852558853728278044986754743741699/20000000000000000000000000000000000000000) (2352663457632164405575140565484121801053/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2562
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2563
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (199043699924606376074696714989641397152243/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (199043699924606376074696714989641397152243/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (399351136276002257568168055324272028227061/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (399351136276002257568168055324272028227061/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (797438536125215009717561485303554822531547/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (797438536125215009717561485303554822531547/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0160.bracket2563 BracketBatch0160.bracket2564 (797438536125215009717561485303554822531547/20000000000000000000000000000000000000000) (1177489777886190228563907341527474676703/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0160.bracket2563 BracketBatch0160.bracket2564
  (797438536125215009717561485303554822531547/20000000000000000000000000000000000000000) (1177489777886190228563907341527474676703/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2563
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2564
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (199675568138001128784084027662136014113529/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (199675568138001128784084027662136014113529/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (200311473973694981884375792302499938715221/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (200311473973694981884375792302499938715221/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (319989633689356888534767855971708762263/8000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (319989633689356888534767855971708762263/8000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0160.bracket2564 BracketBatch0160.bracket2565 (319989633689356888534767855971708762263/8000000000000000000000000000000000000) (1178651655205606526343883669163743479951/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0160.bracket2564 BracketBatch0160.bracket2565
  (319989633689356888534767855971708762263/8000000000000000000000000000000000000) (1178651655205606526343883669163743479951/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2564
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2565
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (400622947947389963768751584604999877430439/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (400622947947389963768751584604999877430439/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (401902912509918861863287002030827396960891/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (401902912509918861863287002030827396960891/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (80252586045730882563203858663582727439133/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (80252586045730882563203858663582727439133/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0160.bracket2565 BracketBatch0160.bracket2566 (80252586045730882563203858663582727439133/2000000000000000000000000000000000000000) (4719269536301790613627386551065391216431/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0160.bracket2565 BracketBatch0160.bracket2566
  (80252586045730882563203858663582727439133/2000000000000000000000000000000000000000) (4719269536301790613627386551065391216431/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2565
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2566
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (50237864063739857732910875253853424620111/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (50237864063739857732910875253853424620111/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (40319110860880131876568318478360510542323/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (40319110860880131876568318478360510542323/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (402547010559360090314485093407216251192059/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (402547010559360090314485093407216251192059/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0160.bracket2566 BracketBatch0160.bracket2567 (402547010559360090314485093407216251192059/10000000000000000000000000000000000000000) (4723947952002517425378062401332041191549/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0160.bracket2566 BracketBatch0160.bracket2567
  (402547010559360090314485093407216251192059/10000000000000000000000000000000000000000) (4723947952002517425378062401332041191549/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2566
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2567
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (403191108608801318765683184783605105423227/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (403191108608801318765683184783605105423227/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0401.rows BesselBatch0401.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (40448761590402664776233145959227035095053/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (40448761590402664776233145959227035095053/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0689.rows BesselBatch0689.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (807678724512827966528014644375875456373757/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (807678724512827966528014644375875456373757/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0320.rows ScalarLogs0320.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0160.bracket2567 BracketBatch0160.bracket2568 (807678724512827966528014644375875456373757/20000000000000000000000000000000000000000) (4728641962768412394828127352325687895183/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0160.bracket2567 BracketBatch0160.bracket2568
  (807678724512827966528014644375875456373757/20000000000000000000000000000000000000000) (4728641962768412394828127352325687895183/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2567
