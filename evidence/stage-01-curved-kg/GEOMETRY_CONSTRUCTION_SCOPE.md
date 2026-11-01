> Historical stage note, retained with its original scope and date. Stage-local “private,” “pending,” or “remaining” wording is not the current repository status. See [the evidence guide](../../EVIDENCE.md) for final acceptance and later source-bootstrap results.

# First construction: quantitative pointwise EH cone control

This begins phase1 after the independently reviewed source contract, SHA256 `de91973a7def19d2a38185d10c7c928a2c12a1d2816a1617ef23b0aa9d259235`, was reported. It does not complete phase1 or Stage1.

Source-first basis: queries001/002 and the full source/defense reading recorded in `SOURCE_AND_COMPLETION_CONTRACT.md` precede this target. Bär's symmetric-hyperbolic receiving conditions and the corpus's explicit Cauchy reductions require the actual metric's causal geometry. Existing `WickLorentzSignatureDomain`, `WickOriginalLorentzMetricDomain` and `OriginalEHMetricActGeometry` were read in full at their recorded source pins. They already prove spatial positivity, signature and the exact operand's smooth Lorentz field. This helper derives a useful quantitative consequence of the original `<1/16` coefficient bound.

`EHKGUniformCone.lean` concerns the same field `originalEHActMetric H`, for arbitrary admitted original `H`. For a coordinate vector `v`, write `S = sum_i (v[i+1])^2` and `Q = gH(v,v)`. The proposed bounds are:

```text
(3/4) S - (5/4) v[0]^2 <= Q <= (5/4) S - (3/4) v[0]^2.
```

Consequently a causal vector has `3S <= 5 v[0]^2`; a nonzero causal vector has nonzero time component. The proof uses ordinary finite-sum inequalities and the actual inherited coefficient estimate, not a cone or temporal-function certificate as an input.

These are pointwise algebraic/metric results. Global hyperbolicity, integration of causal curves, Cauchy leaves, an occupied curvature-bearing operand and the KG evolution theorem remain unproved in this stage. No finite-propagation statement follows just from this helper.

The new module is not presented as a new derivation of the Kernel or as a proof of full constraint architecture from a metric. The final construction must later compose these downstream geometric proofs through the actual inherited source/licensing maps in the constraint-first direction.
