/- Isolated pre-Hilbert generalization of the retained scalar-ray API.
Original bytes and transformations are bound in prehilbert_api_binding.json. -/
import KGPreHilbertCarrier
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Schrödinger transition probabilities on physical rays

This file constructs the normalized pure-state transition probability

`‖⟪ψ, φ⟫_ℂ‖² / (‖ψ‖² * ‖φ‖²)`

for nonzero Hilbert-space representatives.  It proves invariance under
independent nonzero complex rescalings, descends the quantity to pairs of
physical rays, and derives separation of physical rays from the equality
case of Cauchy--Schwarz.

The final section proves simultaneous transport invariance under a supplied
complex-linear isometric equivalence, directly from preservation of the
inner product and norm.  No Wigner converse, Standing semantics, Hamiltonian,
dynamics, completeness interpretation, certificate, or project axiom is
introduced.
-/

noncomputable section

namespace AASCKleinGordon
namespace KGQuantum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

omit [InnerProductSpace ℂ H] in
/--
The denominator in the normalized transition probability is nonzero for two
nonzero pure-state representatives.
-/
theorem transitionProbability_denominator_ne_zero (ψ φ : PureVector H) :
    ‖(ψ : H)‖ ^ 2 * ‖(φ : H)‖ ^ 2 ≠ 0 := by
  exact mul_ne_zero
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr ψ.2))
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr φ.2))

/--
The normalized transition probability between two nonzero representatives.
-/
def transitionProbability (ψ φ : PureVector H) : ℝ :=
  norm (inner ℂ (ψ : H) (φ : H)) ^ 2 /
    (‖(ψ : H)‖ ^ 2 * ‖(φ : H)‖ ^ 2)

/--
The nonnegative normalized transition amplitude.  Its square is the
transition probability.
-/
def normalizedTransitionAmplitude (ψ φ : PureVector H) : ℝ :=
  norm (inner ℂ (ψ : H) (φ : H)) / (‖(ψ : H)‖ * ‖(φ : H)‖)

theorem transitionProbability_eq_normalizedTransitionAmplitude_sq
    (ψ φ : PureVector H) :
    transitionProbability ψ φ =
      normalizedTransitionAmplitude ψ φ ^ 2 := by
  simp only [transitionProbability, normalizedTransitionAmplitude, div_pow, mul_pow]

theorem normalizedTransitionAmplitude_nonneg (ψ φ : PureVector H) :
    0 ≤ normalizedTransitionAmplitude ψ φ := by
  exact div_nonneg (norm_nonneg (inner ℂ (ψ : H) (φ : H)))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/--
Independent nonzero rescaling of the first representative leaves the
normalized transition amplitude unchanged.
-/
theorem normalizedTransitionAmplitude_smul_left
    (c : ℂ) (hc : c ≠ 0) (ψ φ : PureVector H) :
    normalizedTransitionAmplitude (PureVector.smul c hc ψ) φ =
      normalizedTransitionAmplitude ψ φ := by
  have hcnorm : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  have hψnorm : ‖(ψ : H)‖ ≠ 0 := norm_ne_zero_iff.mpr ψ.2
  have hφnorm : ‖(φ : H)‖ ≠ 0 := norm_ne_zero_iff.mpr φ.2
  have hstar : ‖(starRingEnd ℂ) c‖ = ‖c‖ := by
    exact RCLike.norm_conj c
  simp only [normalizedTransitionAmplitude, PureVector.coe_smul,
    inner_smul_left, norm_mul, norm_smul]
  field_simp
  rw [hstar]
  exact mul_comm _ _

/--
Independent nonzero rescaling of the second representative leaves the
normalized transition amplitude unchanged.
-/
theorem normalizedTransitionAmplitude_smul_right
    (d : ℂ) (hd : d ≠ 0) (ψ φ : PureVector H) :
    normalizedTransitionAmplitude ψ (PureVector.smul d hd φ) =
      normalizedTransitionAmplitude ψ φ := by
  have hdnorm : ‖d‖ ≠ 0 := norm_ne_zero_iff.mpr hd
  have hψnorm : ‖(ψ : H)‖ ≠ 0 := norm_ne_zero_iff.mpr ψ.2
  have hφnorm : ‖(φ : H)‖ ≠ 0 := norm_ne_zero_iff.mpr φ.2
  simp only [normalizedTransitionAmplitude, PureVector.coe_smul,
    inner_smul_right, norm_mul, norm_smul]
  field_simp

/--
The transition probability is invariant under arbitrary independent nonzero
complex rescalings of both representatives.
-/
theorem transitionProbability_smul
    (c d : ℂ) (hc : c ≠ 0) (hd : d ≠ 0) (ψ φ : PureVector H) :
    transitionProbability (PureVector.smul c hc ψ)
        (PureVector.smul d hd φ) =
      transitionProbability ψ φ := by
  rw [transitionProbability_eq_normalizedTransitionAmplitude_sq,
    normalizedTransitionAmplitude_smul_left,
    normalizedTransitionAmplitude_smul_right,
    ← transitionProbability_eq_normalizedTransitionAmplitude_sq]

theorem transitionProbability_smul_left
    (c : ℂ) (hc : c ≠ 0) (ψ φ : PureVector H) :
    transitionProbability (PureVector.smul c hc ψ) φ =
      transitionProbability ψ φ := by
  rw [transitionProbability_eq_normalizedTransitionAmplitude_sq,
    normalizedTransitionAmplitude_smul_left,
    ← transitionProbability_eq_normalizedTransitionAmplitude_sq]

theorem transitionProbability_smul_right
    (d : ℂ) (hd : d ≠ 0) (ψ φ : PureVector H) :
    transitionProbability ψ (PureVector.smul d hd φ) =
      transitionProbability ψ φ := by
  rw [transitionProbability_eq_normalizedTransitionAmplitude_sq,
    normalizedTransitionAmplitude_smul_right,
    ← transitionProbability_eq_normalizedTransitionAmplitude_sq]

/--
The transition probability descends simultaneously through both physical-ray
quotients.
-/
def rayTransitionProbability : PhysicalRay H → PhysicalRay H → ℝ :=
  Quotient.lift₂ transitionProbability (by
    intro ψ φ ψ' φ' hψ hφ
    rcases hψ with ⟨c, hc, hscaleψ⟩
    rcases hφ with ⟨d, hd, hscaleφ⟩
    have hψ' : PureVector.smul c hc ψ = ψ' := Subtype.ext hscaleψ
    have hφ' : PureVector.smul d hd φ = φ' := Subtype.ext hscaleφ
    rw [← hψ', ← hφ']
    exact (transitionProbability_smul c d hc hd ψ φ).symm)

@[simp]
theorem rayTransitionProbability_on_representatives (ψ φ : PureVector H) :
    rayTransitionProbability (rayMap H ψ) (rayMap H φ) =
      transitionProbability ψ φ :=
  rfl

/--
The uncurried transition probability on a pair of physical rays.
-/
def physicalRayPairTransitionProbability
    (rays : PhysicalRay H × PhysicalRay H) : ℝ :=
  rayTransitionProbability rays.1 rays.2

@[simp]
theorem physicalRayPairTransitionProbability_on_representatives
    (ψ φ : PureVector H) :
    physicalRayPairTransitionProbability (rayMap H ψ, rayMap H φ) =
      transitionProbability ψ φ :=
  rfl

theorem normalizedTransitionAmplitude_self (ψ : PureVector H) :
    normalizedTransitionAmplitude ψ ψ = 1 := by
  simpa only [normalizedTransitionAmplitude, one_smul] using
    (norm_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul
      (𝕜 := ℂ) ψ.2 one_ne_zero)

theorem transitionProbability_self_rep (ψ : PureVector H) :
    transitionProbability ψ ψ = 1 := by
  rw [transitionProbability_eq_normalizedTransitionAmplitude_sq,
    normalizedTransitionAmplitude_self]
  norm_num

theorem rayTransitionProbability_self (r : PhysicalRay H) :
    rayTransitionProbability r r = 1 := by
  refine Quotient.inductionOn r ?_
  intro ψ
  exact transitionProbability_self_rep ψ

/--
If two physical rays have the same transition probability against every
physical ray, then they are equal.

No positive-dimension or finite-dimensional hypothesis is needed.  If rays
exist, the proof tests against one of the rays and invokes the equality case
of Cauchy--Schwarz; if the Hilbert space is zero-dimensional, the universally
quantified statement is vacuous because `PhysicalRay H` is empty.
-/
theorem ray_eq_of_transitionProfile_eq {r s : PhysicalRay H}
    (hprofile : ∀ t : PhysicalRay H,
      rayTransitionProbability r t = rayTransitionProbability s t) :
    r = s := by
  refine Quotient.inductionOn₂ r s ?_ hprofile
  intro ψ φ h
  have htest :
      transitionProbability φ ψ = 1 := by
    have hψ := h (rayMap H ψ)
    change transitionProbability ψ ψ = transitionProbability φ ψ at hψ
    rw [transitionProbability_self_rep] at hψ
    exact hψ.symm
  have hamp_sq :
      normalizedTransitionAmplitude φ ψ ^ 2 = 1 := by
    rw [← transitionProbability_eq_normalizedTransitionAmplitude_sq]
    exact htest
  have hamp_one : normalizedTransitionAmplitude φ ψ = 1 := by
    have hnonneg := normalizedTransitionAmplitude_nonneg φ ψ
    nlinarith
  have hnorm :
      norm (inner ℂ (φ : H) (ψ : H)) =
        ‖(φ : H)‖ * ‖(ψ : H)‖ := by
    exact eq_of_div_eq_one hamp_one
  rcases (norm_inner_eq_norm_iff φ.2 ψ.2).1 hnorm with
    ⟨c, hc, hscale⟩
  exact ((rayMap_eq_iff H φ ψ).2 ⟨c, hc, hscale.symm⟩).symm

/--
Exact transition-profile extensionality for physical rays.
-/
theorem transitionProfile_eq_iff_ray_eq (r s : PhysicalRay H) :
    (∀ t : PhysicalRay H,
      rayTransitionProbability r t = rayTransitionProbability s t) ↔
      r = s := by
  constructor
  · exact ray_eq_of_transitionProfile_eq
  · rintro rfl
    exact fun _ => rfl

section UnitaryTransport

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

namespace PureVector

/--
A complex-linear isometric equivalence transports a nonzero representative
to a nonzero representative.
-/
def mapUnitary (U : H ≃ₗᵢ[ℂ] K) (ψ : PureVector H) : PureVector K :=
  ⟨U (ψ : H), by
    intro hzero
    apply ψ.2
    apply U.injective
    simpa using hzero⟩

@[simp]
theorem coe_mapUnitary (U : H ≃ₗᵢ[ℂ] K) (ψ : PureVector H) :
    (mapUnitary U ψ : K) = U (ψ : H) :=
  rfl

end PureVector

/--
Representative-level simultaneous unitary transport invariance, derived
directly from preservation of the inner product and norm.
-/
theorem transitionProbability_mapUnitary
    (U : H ≃ₗᵢ[ℂ] K) (ψ φ : PureVector H) :
    transitionProbability (PureVector.mapUnitary U ψ)
        (PureVector.mapUnitary U φ) =
      transitionProbability ψ φ := by
  simp only [transitionProbability, PureVector.coe_mapUnitary,
    U.inner_map_map, U.norm_map]

/--
The map induced by a supplied unitary operator on physical rays.
-/
def unitaryRayMap (U : H ≃ₗᵢ[ℂ] K) : PhysicalRay H → PhysicalRay K :=
  Quotient.map (PureVector.mapUnitary U) (by
    intro ψ φ hrel
    rcases hrel with ⟨c, hc, hscale⟩
    refine ⟨c, hc, ?_⟩
    change c • U (ψ : H) = U (φ : H)
    rw [← U.map_smul, hscale])

@[simp]
theorem unitaryRayMap_on_representative
    (U : H ≃ₗᵢ[ℂ] K) (ψ : PureVector H) :
    unitaryRayMap U (rayMap H ψ) =
      rayMap K (PureVector.mapUnitary U ψ) :=
  rfl

/--
Physical-ray transition probabilities are invariant when both rays are
transported by the same supplied unitary operator.
-/
theorem rayTransitionProbability_unitary_invariant
    (U : H ≃ₗᵢ[ℂ] K) (r s : PhysicalRay H) :
    rayTransitionProbability (unitaryRayMap U r) (unitaryRayMap U s) =
      rayTransitionProbability r s := by
  refine Quotient.inductionOn₂ r s ?_
  intro ψ φ
  exact transitionProbability_mapUnitary U ψ φ

end UnitaryTransport


end KGQuantum
end AASCKleinGordon
