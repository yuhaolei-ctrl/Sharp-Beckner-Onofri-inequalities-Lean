# New analytic clauses and their mathematical objects

Scope: the two formerly open clauses among the manuscript's 51 formal results.
This is an implementer crosswalk, not an independent reviewer verdict. Machine
outcomes, source identities and checker runs are recorded separately.

## Lemma 2.9: physical Friedrichs intertwining

Write `c = 2π`. The physical measure is a product of restricted, unweighted
Lebesgue measures: `(0,1/2)` on an active coordinate, `(0,1]` on an inactive
coordinate. The latter is a fundamental interval for the periodic space.
Boundary identifications are imposed through the smooth core's periodicity.

| Manuscript object or clause | Formal implementation |
|---|---|
| Coordinate-labelled mixed space | `Physical.coordinateMeasure`, `Physical.spatialMeasure`, `Physical.H` |
| Change of variables θ=cx | `Physical.map_spatial`: pushforward of angular measure is `c^d` times physical measure |
| Actual L² coordinate maps | `Physical.coordinateLpEquiv`: `Wf(x)=f(cx)`; `coordinateLpEquiv_inner`: `<f,g>=c^d< Wf,Wg >`; `coordinateUnitary`: `sqrt(c^d) W` |
| Zero Dirichlet and inactive periodic conditions | `Physical.smoothCoreProfile`; `smoothCore_up` and `smoothCore_down` transport both conditions |
| Gradient and potential energy | `partial_up`, `partial_down`, `potentialFactor_sq`; the potential is `c² m(m−1)/sin²(cx)` |
| Friedrichs form closure | `Physical.core`, `Physical.formClosure`, `energyEquiv_closure_image`; the energy map scales gradient and potential coordinates by c |
| Actual associated operator and its domain | `Physical.operatorGraph` is defined by testing the closed form; `operatorGraph_transport` proves `B_x Wf=c² WB_θ f` in graph form |
| Physical spectral powers | `Physical.SpectralPowerGraph` uses the transported complete mixed basis and eigenvalues `c²λ`; `spectralPowerGraph_one` identifies its first power with the form-defined operator |
| Power domains | `spectralPowerGraph_transport` and `spectralPowerGraph_domain`; the paper uses s>0 |
| Arbitrary smooth U and all nonzero multi-indices | `Physical.FractionalIntertwining` and `Physical.fractional_intertwining` |
| Full torus multiplier | `Physical.torusPower` and the Fourier clause of the same theorem give `(c|k|)^(2s)` |

The spatial weight is `∏ᵢ sin(cxᵢ)^(αᵢ)`. Inactive exponents are zero, so the
product over all coordinates equals the paper's product over active ones.
The input and output vectors are identified almost everywhere with the literal
weighted mixed derivatives of U and the smooth cosine representation of its
physical torus power. The domain assertion is the existence of an actual
physical L² output vector satisfying the spectral graph, not an assumed
regularity predicate.

The transported basis is multiplied by a common nonzero factor relative to
the unitary image of the angular orthonormal basis. This factor cancels on
both sides of the spectral coefficient equation. No periodic odd sector is
removed. The original angular theorem remains separately registered and is
not relabelled as a physical-coordinate theorem.

## Lemma 4.2: the original differentiated periodization series

`Periodization.coordinatePartial i f x` is
`deriv (fun t => f (x + t • eᵢ)) 0`, on the full Euclidean space. `mixed` iterates
this operation over every finite list of coordinate indices, including the
empty list. Thus the target covers the original series and every order of
coordinate differentiation.

The proof constructs finite expressions from constants,
`(1+25∑xᵢ²)⁻¹`, and `xⱼ/(1+25∑xᵢ²)`. Each expression is bounded globally.
Differentiating one of these expressions stays in the same algebra, and each
derivative of the Euclidean profile equals the original profile times such
an expression. Therefore, for each derivative, a constant multiple of the
already proved translated-profile majorant controls every term uniformly
on each compact set.

`mixed_translate` proves that differentiation commutes with the lattice
translation. `derivative_majorant` supplies the summable compact-set bound;
`derivatives_locally_uniform` applies the Weierstrass M-test to finite lattice
subsets directed by inclusion. The registered target is
`Paper2.periodization_derivatives_locally_uniform`.

The proof does not need the sharper displayed decay rate `−22−|α|`: a
summable `−22` bound for each fixed derivative suffices. Existing targets
supply the same density's smoothness, positivity, mass and conditional entropy
identity. This is an alternative proof of the convergence clause, with the
original summands retained.
