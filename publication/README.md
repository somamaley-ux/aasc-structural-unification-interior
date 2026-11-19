# What the original preparations determine

The publication entry point `PreparationPublication.lean` imports the original operational stage-four capstone, the task-coverage audit, the previously distributed preparation and access supplements, and the new metric and travel-time comparisons. Each theorem retains its own physical hypotheses.

## Occupied metric readings and minimum differential order

`OccupiedMetricGerms.lean` constructs bounded compact metric operands with the same germ as a locally smooth Lorentzian metric in a normalized chart. The cutoff equals one on a neighborhood. This supplies equality of response derivatives wherever a local response agrees on that neighborhood. `OccupiedFullProfileGerms.lean` shows that matching every original compact variation identifies the specified Einstein–Hilbert response even for a natural germ-local rival without an assigned differential order or action.

`OccupiedLieReadings.lean` constructs compact metric Lie probes on occupied operands, checks their admission along short variation rays, and relates their readings to the represented source divergence. `OriginalWardLocalization.lean` transfers those comparisons to smooth normal charts and the curved cubic metric witness. A nonzero normalized divergence supplies a compact Lie test whose reading differs on an occupied operand.

`CompactRelativeGauge.lean` proves that the original relative Einstein–Hilbert action has the same value on two occupied operands related by a certified compact pullback on its invariant patch. A parameter family retaining these certificates near zero has zero action derivative there.

`MetricDivergenceTransport.lean` calculates how the divergence of a smooth symmetric tensor transforms between the input chart and its centered normal chart. The occupied Ward corollary uses the tensor's covariance on the chart germ to conclude zero divergence in the original coordinates at every smooth, framed Lorentz point. This transport is proved at the tensor level without assuming that divergence is covariant.

`MinimumMetricResponseOrder.lean` defines differential order by factorization through the actual metric jet. A natural response of order zero or one is a constant metric multiple on smooth Lorentzian operands. The original active, closed Einstein response attains order two. `SmoothMinimumEinstein.lean` classifies the active second-order responses with the differentiated natural-tensor component identities, and constructs an example for each allowed coefficient pair. `OccupiedMinimumEinstein.lean` connects the occupied Lie readings to the cubic conservation test and gives the minimum order and unique Einstein coefficient pair together. The smooth classification records the published Lovelock implication from smooth geometric naturality and off-shell conservation to the differential component identities as an external mathematical input. The coefficient obstruction and the subsequent use of those identities are checked in Lean.

`ObservedOrderMinimum.lean` minimizes directly over natural active responses reproducing the original compact Lie readings. The actual Einstein–Hilbert response witnesses attainability in this comparison class. The source-derived bound and the unique Einstein coefficient pair for a smooth minimizer are combined in `einstein_form_at_observed_minimum`.

`OccupiedRestOperationQueries.lean` compares two kinds of query on the same original finite-ray preparation. Retaining just the identity frame comparison leaves the answers to every ray-arrival query unchanged. The original occupied source admits the proper half-turn that sends the first unit spatial direction to its negative at one tick; the restricted collection loses that interchange. This reduction of the available operations changes the complete protocol.

## Metric response

`FourDimensionalDiv2.lean` proves the dimension-four coefficient obstruction for the differentiated symmetry identities. `SmoothMetricResponse.lean` relates the derivative of the actual response on normalized metric Hessian probes to curvature affinity on original metric germs. `FourDimensionalMetricResponse.lean` combines them. Its theorem `AASCSemanticExhaustion.c2_profile_unique_einstein_of_four_dimensional_symmetries` gives the unique Einstein-form coefficients for the twice continuously differentiable probe response, assuming the stated second-derivative symmetries, naturality, two-jet locality, output symmetry, closure and activity. `OccupiedSmoothMetricResponse.lean` verifies a smooth probe profile and the coefficient identities for the original Einstein–Hilbert response.

The manuscript’s classical smooth-branch corollary cites Navarro and Navarro for the passage from geometric naturality and off-shell conservation to the differentiated natural-tensor identities. The Lean theorem takes the named predicate `NormalResponseSecondSymmetries` at this boundary. The coefficient obstruction and the application to the original metric germs are checked in this project. [Navarro and Navarro, Corollary 2.3 and Theorem 2.6](https://arxiv.org/abs/1005.2386)

## Inertial and scalar comparisons

`TravelTimePolarization.lean` identifies the least finite-ray arrival on the original normed displacement space. The parallelogram identity for all pairs is equivalent to existence of a unique symmetric bilinear form with the original squared times as its diagonal. A failing pair distinguishes a proposed quadratic account. The cube example realizes the six-event selective access pattern while its four specified arrival times exclude a spatial inner product. A linear transformation preserving the complete finite-ray reach relation preserves the reconstructed spatial form on this branch. The existence of a physical rest group with full frontier transitivity belongs to the inertial preparation.

`TransitiveRestRotations.lean` proves that an orientation-preserving three-dimensional rest-comparison subgroup acting transitively on the unit frontier contains every proper rotation. Exact frontier transitivity is its hypothesis. In `NativeTransitiveRestFrame.lean`, `AASCKleinGordon.CanonicalLicensing.SRIntegration.sr_transitive_rest_and_same_tick_preserve_native_interval` derives the proper rest family for the admitted matrix frames and applies the same positive native rest tick to interval preservation. The original joined Stage 4 theorem is `AASCKleinGordon.OperationalSR.kernel_faithful_operational_sr`, with its admitted operands and resources. `OccupiedScalarFlow.lean` retains the earlier identification of the separately continuous free flow by the original limiting complex packet amplitudes. `PreparationPublicationAudit.lean` queries these declarations together with the native capstone and the retained metric, inertial and causal results.

## Reproduction

Use the repository’s pinned Lean 4.28.0 toolchain and mathlib commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`. From the repository root run the normal Lake target.

```sh
lake build PreparationPublication
lake env lean publication/PreparationPublicationAudit.lean
python verify.py
```

For a local checkout containing the same precompiled native sources and mathlib dependencies, the following route re-elaborates the publication sources into a new directory, rechecks the new modules with `leanchecker` and verifies the complete axiom inventory. The script requires Python 3.10 or later.

```sh
python publication/replay_publication.py --native-project /path/to/compiled-native-project --lean-bin /path/to/lean-4.28.0/bin --out /path/to/new-output --jobs 2
```

An older partial cache may be missing `Mathlib.Analysis.InnerProductSpace.OfNorm` and its import `Mathlib.Algebra.Module.LinearMap.Rat`. Build those modules using the pinned mathlib sources. The optional `--mathlib-overlay` argument accepts a compiled library root containing these modules and the rest of their mathlib import tree. The original full-export bootstrap and dependency-object evidence remain documented in the repository’s reproduction guide.
