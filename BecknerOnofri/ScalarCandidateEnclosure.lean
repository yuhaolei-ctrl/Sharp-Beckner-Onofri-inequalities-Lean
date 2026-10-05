import BecknerOnofri.ScalarTightEnclosure
import BecknerOnofri.CircleScalarDefinitions

namespace BecknerOnofri.HighDim.ScalarCertificate
open CircleScalar

noncomputable def costFunctionEnclosure {a b : ℝ} {A B C D L r x : ℝ → ℝ}
    (eA : FunctionEnclosure a b A) (eB : FunctionEnclosure a b B)
    (eC : FunctionEnclosure a b C) (eD : FunctionEnclosure a b D)
    (eL : FunctionEnclosure a b L) (er : FunctionEnclosure a b r)
    (ex : FunctionEnclosure a b x) :
    FunctionEnclosure a b (fun h => cost (A h) (B h) (C h) (D h) (L h) (r h) (x h)) := by
  let ez : FunctionEnclosure a b (fun _ => (0 : ℝ)) :=
    (FunctionEnclosure.const a b 0).congr (fun _ => Rat.cast_zero)
  exact ((eA.rmul ex.rsquare).radd (eB.rmul (ex.rsub er).rsquare)).radd
    (eC.rmul (ez.tightMax (eL.rsub (eD.rmul ex))).rsquare)

noncomputable def candidateFunctionEnclosure {a b : ℝ} {A B C D L r m : ℝ → ℝ}
    (eA : FunctionEnclosure a b A) (eB : FunctionEnclosure a b B)
    (eC : FunctionEnclosure a b C) (eD : FunctionEnclosure a b D)
    (eL : FunctionEnclosure a b L) (er : FunctionEnclosure a b r)
    (em : FunctionEnclosure a b m)
    (hAB : 0<(eA.radd eB).value.lower)
    (hABC : 0<((eA.radd eB).radd (eC.rmul eD.rsquare)).value.lower)
    (hD : 0<eD.value.lower) :
    FunctionEnclosure a b (fun h => candidateMinimum (A h) (B h) (C h) (D h) (L h) (r h) (m h)) := by
  let x1 := em.tightMax ((eB.rmul er).rdiv (eA.radd eB) hAB)
  let x2 := em.tightMax (((eB.rmul er).radd ((eC.rmul eD).rmul eL)).rdiv
    ((eA.radd eB).radd (eC.rmul eD.rsquare)) hABC)
  let x3 := em.tightMax (eL.rdiv eD hD)
  let c0 := costFunctionEnclosure eA eB eC eD eL er em
  let c1 := costFunctionEnclosure eA eB eC eD eL er x1
  let c2 := costFunctionEnclosure eA eB eC eD eL er x2
  let c3 := costFunctionEnclosure eA eB eC eD eL er x3
  exact (c0.tightMin c1).tightMin (c2.tightMin c3)

#print axioms candidateFunctionEnclosure
end BecknerOnofri.HighDim.ScalarCertificate
