# Proof-route audit: does the Lean proof follow the paper?

Comparator certifies that `Solution.lean` proves the 28 statements of `Challenge.lean`.
It does not certify that the Lean proof follows the proofs written in the manuscript.
This file compares the two at the level of proof structure: for each numbered result X,
which earlier results the paper's proof of X uses, and which ones the Lean proof uses.

This audit was carried out by AI agents (Claude Code) on 7 October 2026, against the
manuscript of 6 October 2026. It is not an independent human review. It is meant to show a
reviewer where to look.

## Method

1. **Paper side.** Each proof environment of the LaTeX source was scanned for `\ref`,
   `\cref` and `\eqref`. An equation label was attributed to the result whose statement or
   proof contains it. This gives 86 citations "the proof of X uses Y".
2. **Lean side.** The development was exported with `leanexport`, and a graph was built in
   which a declaration points to every project constant in its type or proof term (11,158
   declarations). The Lean proof of X uses Y if a Lean counterpart of Y (listed in
   `CORRESPONDENCE.md`) is reachable from a counterpart of X.
3. **Comparison.** 73 citations have Lean counterparts at both ends.
   - **33** match directly: the Lean proof of X goes through the Lean version of Y.
   - **40** were reviewed by hand. For each one, the reviewer found the step of the
     paper's proof that uses Y and how the Lean proof handles that step. Every claim was
     checked against the dependency graph and the source, with file and line references.

## Results of the review of the 40 citations

| Class | Meaning | Count |
|---|---|---|
| Same step, other name | Lean uses the content of Y through a sibling declaration, which may be stronger, weaker or specialised | 29 |
| Hypothesis | Y enters the Lean statement of X as an explicit hypothesis, discharged where X is applied (e.g. Lemma 5.17 as `hminor`) | 4 |
| Citation artifact | the paper cites a label of Y only for a formula or a definition, or the proof belongs to another result | 3 |
| Different route | the Lean proof does this step without Y | 4 |

No step of a paper proof is missing from the Lean proof without a replacement argument.

## Where the Lean proof takes a different route

1. **Proposition 3.7 (dimensions 2–10): uses neither Lemma 2.1 nor Lemma 2.12.**
   - **Inequality.** It is proved first for continuous positive densities, which have
     finite energy because they are in L². It then extends to all finite-entropy densities
     by heat regularization: entropy decreases, Fourier coefficients converge, and the
     energy is lower semicontinuous. No a priori finite-energy bound is used.
   - **Selection.** A counterexample produces a subcritical potential maximizer that is
     fixed by every polarization (two-point rearrangement), hence Steiner symmetric. Its
     Gibbs density is a cosine mixture, which contradicts the strict mixture gap
     (Lemma 3.6 with Proposition 3.1).
   - **Equality.** An equality density is shown to be Gibbs and in L². A
     polarization-fixed equality density with the same entropy is obtained by compactness,
     and it is uniform by the mixture gap.
   - **Status of the paper's lemmas.** Lemma 2.1 and Lemma 2.12 are formalized as
     stated, but these arguments do not use them.
2. **Lemma 2.12 in dimensions d ≥ 12 (Propositions 5.1 and 5.7).** The symmetric optimizer
   is selected on the potential side, as above: a Steiner-symmetric maximizer obtained by
   polarization. It reaches all finite-entropy densities by weak duality and heat
   regularization. The paper instead rearranges a density minimizer coordinate by
   coordinate.
3. **Proposition 5.23 (global minimizers and pressure onset): partially supported branches
   are never classified.**
   - **Upper bound.** The pressure is bounded above by coercivity of the reduced quartic on
     the Lyapunov–Schmidt graph.
   - **Lower bound.** The explicit full diagonal branch is used as a competitor.
   - **Classification.** Near-optimal energy forces the rescaled amplitudes to the
     all-active point. A rescaled implicit-function argument then places every optimizer
     on the orbit of the diagonal branch.
   - **Compactness.** This is proved in the Wiener algebra, not by Sobolev-algebra
     bootstrap.
   - **Status of Proposition 5.22.** It is formalized as stated (namespace
     `BecknerOnofri.HighDim.LocalEleven`), but only its full-branch pieces are used: the
     analytic branch, the Hessian kernel and the normal coercivity.
4. **Lemma 3.3 for d = 11.** The weight r⁻¹ is bounded by 1 instead of using Lemma 3.2.
   The result, J₁₁ < 5/2, is still obtained. For d = 10 and d = 12 the bound of Lemma 3.2
   is used.
5. **Minor changes of setting.** These are the same arguments carried out in a different
   space or form:
   - Proposition 4.8 applies Lemma 4.7 in C(𝕋¹¹) instead of H¹¹.
   - Proposition 5.7 is proved by induction one dimension at a time, using the deletion
     forms of Lemma 5.2 and Proposition 5.5. The paper notes these are iterates of the
     r = 12 forms.
   - Lemma 2.5 and Corollary 5.8 use the inequality halves of the gap identities.

## Results proved in the paper's generality but used in a specialised form

The main theorems apply the following results only to the selected (Steiner-symmetric)
maximizers, which is the only case in which the paper applies them. The general statements
are also formalized, but the main proof does not use them:

- **Proposition 2.11:** used for maximizers. The general version is
  `GeneralEulerBridge.cosine_representation`.
- **Lemma 2.9:** used for s = d/2 only, with the operator defined by its Jacobi eigenbasis.
  The general version is `Friedrichs.MixedSpatial.fractional_intertwining`.
- **Lemma 5.9:** coordinate permutations only.
- **Propositions 5.10, 5.11 and 5.12(i):** used in the `Selected u` form. The
  general-density versions are in `GlobalShapeEntropyPaper.lean`,
  `SingularFourierTailPaper.lean` and `GeneralShapeEntropyEta.lean`.

## What this means for the manuscript

Every theorem of the paper is proved in Lean. Each step of a paper proof is either carried
out in Lean or replaced by a complete alternative argument, as listed above. Where the
Lean proof takes a different route, the paper's own lemma is also formalized, except in two
places:

- the argument of Proposition 5.23 that partially supported branches are not global
  minimizers, and its Sobolev-algebra compactness step;
- the strict inequality ψ < γ for t > 0 in Lemma 5.17 (only ψ ≤ γ is formalized and
  needed).

In these places the Lean development does not certify the manuscript's written argument.
It certifies the stated results by another argument.
