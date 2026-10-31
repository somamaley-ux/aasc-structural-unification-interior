/- Isolated pre-Hilbert generalization of the retained scalar-ray API.
Original bytes and transformations are bound in prehilbert_api_binding.json. -/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Data.Quot

/-!
# Schrödinger pure-state carrier

This file constructs only the kinematic carrier of pure states for a complex
Hilbert space `H`.

* `PureVector H` consists of the nonzero vectors of `H`.
* `PhysicalRay H` is the quotient of those vectors by multiplication by an
  arbitrary nonzero complex scalar.
* `NormalizedVector H` consists of the unit vectors of `H`.
* `NormalizedRay H` is the quotient of unit vectors by multiplication by a
  unit-modulus complex phase.

The quotient relations are constructed directly and their exact equality and
fibre theorems are proved below.  No Hamiltonian, dynamics, observable, AASC
attachment, or physical-completeness assertion is made.
-/

open Set

noncomputable section

namespace AASCKleinGordon
namespace KGQuantum

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A possible pure-state representative: an actual nonzero Hilbert vector. -/
abbrev PureVector := {ψ : H // ψ ≠ 0}

/-- A unit-normalized Hilbert vector. -/
abbrev NormalizedVector := {ψ : H // ‖ψ‖ = 1}

namespace PureVector

variable {H}

/-- Multiplication by a nonzero scalar stays inside the nonzero-vector carrier. -/
def smul (c : ℂ) (hc : c ≠ 0) (ψ : PureVector H) : PureVector H :=
  ⟨c • ψ.1, smul_ne_zero hc ψ.2⟩

@[simp]
theorem coe_smul (c : ℂ) (hc : c ≠ 0) (ψ : PureVector H) :
    (smul c hc ψ : H) = c • (ψ : H) :=
  rfl

/-- Exact norm covariance under arbitrary complex rescaling. -/
theorem norm_smul (c : ℂ) (hc : c ≠ 0) (ψ : PureVector H) :
    ‖(smul c hc ψ : H)‖ = ‖c‖ * ‖(ψ : H)‖ := by
  exact _root_.norm_smul c (ψ : H)

/--
Two nonzero vectors represent the same pure state when one is an arbitrary
nonzero complex multiple of the other.
-/
def ScalarRel (ψ φ : PureVector H) : Prop :=
  ∃ c : ℂ, c ≠ 0 ∧ c • (ψ : H) = (φ : H)

theorem scalarRel_refl (ψ : PureVector H) : ScalarRel ψ ψ := by
  exact ⟨1, one_ne_zero, one_smul ℂ (ψ : H)⟩

theorem scalarRel_symm {ψ φ : PureVector H} (h : ScalarRel ψ φ) :
    ScalarRel φ ψ := by
  rcases h with ⟨c, hc, hscale⟩
  refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
  rw [← hscale, smul_smul]
  simp [hc]

theorem scalarRel_trans {ψ φ χ : PureVector H}
    (hψφ : ScalarRel ψ φ) (hφχ : ScalarRel φ χ) :
    ScalarRel ψ χ := by
  rcases hψφ with ⟨c, hc, hscale₁⟩
  rcases hφχ with ⟨d, hd, hscale₂⟩
  refine ⟨d * c, mul_ne_zero hd hc, ?_⟩
  rw [mul_smul, hscale₁, hscale₂]

end PureVector

/-- The explicitly proved setoid of nonzero vectors modulo nonzero scaling. -/
def pureVectorSetoid : Setoid (PureVector H) where
  r := PureVector.ScalarRel
  iseqv := ⟨PureVector.scalarRel_refl, PureVector.scalarRel_symm,
    PureVector.scalarRel_trans⟩

/-- The physical pure-state ray carrier. -/
def PhysicalRay := Quotient (pureVectorSetoid H)

/-- The quotient map from nonzero vectors to physical rays. -/
def rayMap (ψ : PureVector H) : PhysicalRay H :=
  Quotient.mk (pureVectorSetoid H) ψ

/--
Exact quotient equality: two representatives have the same physical ray if
and only if one is a nonzero complex scalar multiple of the other.
-/
theorem rayMap_eq_iff (ψ φ : PureVector H) :
    rayMap H ψ = rayMap H φ ↔
      ∃ c : ℂ, c ≠ 0 ∧ c • (ψ : H) = (φ : H) := by
  change Quotient.mk (pureVectorSetoid H) ψ =
      Quotient.mk (pureVectorSetoid H) φ ↔ PureVector.ScalarRel ψ φ
  exact Quotient.eq

/-- Exact description of every fibre of the physical-ray quotient map. -/
theorem mem_rayMap_fiber_iff (ψ φ : PureVector H) :
    φ ∈ rayMap H ⁻¹' ({rayMap H ψ} : Set (PhysicalRay H)) ↔
      ∃ c : ℂ, c ≠ 0 ∧ c • (φ : H) = (ψ : H) := by
  simpa only [Set.mem_preimage, Set.mem_singleton_iff] using
    (rayMap_eq_iff H φ ψ)

/-- The quotient map is invariant under every admissible nonzero rescaling. -/
theorem rayMap_smul (c : ℂ) (hc : c ≠ 0) (ψ : PureVector H) :
    rayMap H (PureVector.smul c hc ψ) = rayMap H ψ := by
  apply (rayMap_eq_iff H _ _).2
  exact ⟨c⁻¹, inv_ne_zero hc, by simp [PureVector.smul, smul_smul, hc]⟩


end KGQuantum
end AASCKleinGordon
