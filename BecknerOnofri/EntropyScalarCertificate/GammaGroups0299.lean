import BecknerOnofri.EntropyScalarCertificate.Bessel0373
import BecknerOnofri.EntropyScalarCertificate.Bessel0374
import BecknerOnofri.EntropyScalarCertificate.Bessel0375
import BecknerOnofri.EntropyScalarCertificate.Bessel0675
import BecknerOnofri.EntropyScalarCertificate.Bessel0676
import BecknerOnofri.EntropyScalarCertificate.Brackets0149
import BecknerOnofri.EntropyScalarCertificate.Brackets0150
import BecknerOnofri.EntropyScalarCertificate.Logs0299
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2392
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (129235165348824457404138408648932542619969/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (129235165348824457404138408648932542619969/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (259000603944488825101981533540350954021333/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (259000603944488825101981533540350954021333/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (517470934642137739910258350838216039261271/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (517470934642137739910258350838216039261271/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0149.bracket2392 BracketBatch0149.bracket2393 (517470934642137739910258350838216039261271/20000000000000000000000000000000000000000) (816658150935418634394225793017032823937/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0149.bracket2392 BracketBatch0149.bracket2393
  (517470934642137739910258350838216039261271/20000000000000000000000000000000000000000) (816658150935418634394225793017032823937/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2392
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2393
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0373.rows BesselBatch0373.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (25900060394448882510198153354035095402133/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (25900060394448882510198153354035095402133/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (324416335712755665453353954628441879303/12500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (324416335712755665453353954628441879303/12500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (51853367251469335746466469724310445746373/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (51853367251469335746466469724310445746373/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0149.bracket2393 BracketBatch0149.bracket2394 (51853367251469335746466469724310445746373/2000000000000000000000000000000000000000) (2043114561563213974365492277063528588599/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0149.bracket2393 BracketBatch0149.bracket2394
  (51853367251469335746466469724310445746373/2000000000000000000000000000000000000000) (2043114561563213974365492277063528588599/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2393
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2394
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (259533068570204532362683163702753503442397/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (259533068570204532362683163702753503442397/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (65016934546454467347993918584904308175149/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (65016934546454467347993918584904308175149/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (519600806756022401754658838042370736142993/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (519600806756022401754658838042370736142993/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0149.bracket2394 BracketBatch0149.bracket2395 (519600806756022401754658838042370736142993/20000000000000000000000000000000000000000) (4089173944339033796366368518461865423013/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0149.bracket2394 BracketBatch0149.bracket2395
  (519600806756022401754658838042370736142993/20000000000000000000000000000000000000000) (4089173944339033796366368518461865423013/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2394
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2395
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (260067738185817869391975674339617232700593/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (260067738185817869391975674339617232700593/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (130302313257652607964861113599613286283967/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (130302313257652607964861113599613286283967/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (520672364701123085321697901538843805268527/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (520672364701123085321697901538843805268527/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0149.bracket2395 BracketBatch0149.bracket2396 (520672364701123085321697901538843805268527/20000000000000000000000000000000000000000) (102303131125548531353977173689473988657/250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0149.bracket2395 BracketBatch0149.bracket2396
  (520672364701123085321697901538843805268527/20000000000000000000000000000000000000000) (102303131125548531353977173689473988657/250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2395
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2396
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (260604626515305215929722227199226572567931/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (260604626515305215929722227199226572567931/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (130571873698385831169323140706240927049807/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (130571873698385831169323140706240927049807/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (104349674782415375653673701722341685333509/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (104349674782415375653673701722341685333509/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0149.bracket2396 BracketBatch0149.bracket2397 (104349674782415375653673701722341685333509/4000000000000000000000000000000000000000) (4095083052043347164014130764890430093089/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0149.bracket2396 BracketBatch0149.bracket2397
  (104349674782415375653673701722341685333509/4000000000000000000000000000000000000000) (4095083052043347164014130764890430093089/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2396
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2397
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (261143747396771662338646281412481854099611/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (261143747396771662338646281412481854099611/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (10467404591345594013399373356162532129837/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10467404591345594013399373356162532129837/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (2042300242892232471381369591080254520881/78125000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2042300242892232471381369591080254520881/78125000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0149.bracket2397 BracketBatch0149.bracket2398 (2042300242892232471381369591080254520881/78125000000000000000000000000000000000) (2049023696216939390506395014387430994747/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0149.bracket2397 BracketBatch0149.bracket2398
  (2042300242892232471381369591080254520881/78125000000000000000000000000000000000) (2049023696216939390506395014387430994747/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2397
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2398
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (130842557391819925167492166952031651622961/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (130842557391819925167492166952031651622961/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (131114371372926852626151745079869626934507/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (131114371372926852626151745079869626934507/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (65489232191186694448410978007975319639367/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (65489232191186694448410978007975319639367/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0149.bracket2398 BracketBatch0149.bracket2399 (65489232191186694448410978007975319639367/2500000000000000000000000000000000000000) (1025254573346967472086070355077808440807/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0149.bracket2398 BracketBatch0149.bracket2399
  (65489232191186694448410978007975319639367/2500000000000000000000000000000000000000) (1025254573346967472086070355077808440807/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2398
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2399
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0374.rows BesselBatch0374.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (262228742745853705252303490159739253869011/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (262228742745853705252303490159739253869011/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (16423415341943579869708085645680113805827/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (16423415341943579869708085645680113805827/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (525003388216950983167632860490621074762243/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (525003388216950983167632860490621074762243/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0299.rows ScalarLogs0299.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0149.bracket2399 BracketBatch0150.bracket2400 (525003388216950983167632860490621074762243/20000000000000000000000000000000000000000) (102599894556616226179781255110913164581/250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0149.bracket2399 BracketBatch0150.bracket2400
  (525003388216950983167632860490621074762243/20000000000000000000000000000000000000000) (102599894556616226179781255110913164581/250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2399
