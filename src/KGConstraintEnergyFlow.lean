import KGConstraintEnergyCore
import KGOriginalQuantumContinuation
import KGSpacetimeTranslationUnitary

/-! Restriction of the SAME original physical-time unitary to its proved
invariant common core.  Its strong derivative is stated in the ambient Fock
norm on core inputs and equals the constructed core energy vector. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace AASCKleinGordon
local instance (a : Parameters) (n : ℕ) : NormedSpace ℝ (bosonicHilbertSector a n) :=
  NormedSpace.restrictScalars ℝ ℂ (bosonicHilbertSector a n)
local instance (a : Parameters) : NormedSpace ℝ (FockHilbert a) :=
  NormedSpace.restrictScalars ℝ ℂ (FockHilbert a)

theorem kg_constraint_energy_poincare_time (a : Parameters) (t : ℝ) (u : FockHilbert a) :
    originalFockPoincareRepresentation a
      ⟨Multiplicative.ofAdd (timeTranslationEvent a t), 1⟩ u = fockTimeTranslation a t u := by
  change fockEventTranslation a (timeTranslationEvent a t) (fockLorentzUnitary a 1 u) = _
  rw [fockLorentzUnitary_one, fockEventTranslation_time]

theorem kg_constraint_energy_time_preserves_core (a : Parameters) (t : ℝ)
    (u : fockCoreDomain a) : fockTimeTranslation a t u.val ∈ fockCoreDomain a := by
  rw [← kg_constraint_energy_poincare_time]
  exact originalFockPoincareRepresentation_preserves_domain a _ u

def kgConstraintEnergyTime (a : Parameters) (t : ℝ) :
    fockCoreDomain a ≃ₗᵢ[ℂ] fockCoreDomain a where
  toFun u := ⟨fockTimeTranslation a t u.val, kg_constraint_energy_time_preserves_core a t u⟩
  invFun u := ⟨fockTimeTranslation a (-t) u.val, kg_constraint_energy_time_preserves_core a (-t) u⟩
  left_inv u := Subtype.ext ((fockTimeTranslation a t).symm_apply_apply u.val)
  right_inv u := Subtype.ext ((fockTimeTranslation a t).apply_symm_apply u.val)
  map_add' u v := Subtype.ext ((fockTimeTranslation a t).map_add u.val v.val)
  map_smul' c u := Subtype.ext ((fockTimeTranslation a t).map_smul c u.val)
  norm_map' u := (fockTimeTranslation a t).norm_map u.val

theorem kg_constraint_energy_time_original (a : Parameters) (t : ℝ)
    (u : fockCoreDomain a) :
    kgConstraintEnergyTime a t u = kgCorePoincareIsometry a
      ⟨Multiplicative.ofAdd (timeTranslationEvent a t), 1⟩ u := by
  apply Subtype.ext
  exact (kg_constraint_energy_poincare_time a t u.val).symm

theorem kg_constraint_energy_time_zero (a : Parameters) (u : fockCoreDomain a) :
    kgConstraintEnergyTime a 0 u = u := by
  apply Subtype.ext
  exact fockPhaseMultiplier_zero a _ _ _ _ u.val

theorem kg_constraint_energy_time_add (a : Parameters) (t s : ℝ) (u : fockCoreDomain a) :
    kgConstraintEnergyTime a (t + s) u =
      kgConstraintEnergyTime a t (kgConstraintEnergyTime a s u) := by
  apply Subtype.ext
  exact fockPhaseMultiplier_add a _ _ _ _ t s u.val

def kgConstraintEnergyVector (a : Parameters) (u : fockCoreDomain a) : fockCoreDomain a :=
  Translation.coefficient a.hbar • kgConstraintEnergyOperator a u

theorem kg_constraint_energy_time_derivative (a : Parameters) (u : fockCoreDomain a) :
    HasDerivAt (fun t : ℝ => (kgConstraintEnergyTime a t u).val)
      (kgConstraintEnergyVector a u).val 0 := by
  let h := fockCoreEnergy_le_maximal a
  have hd := (fockTimeTranslation_exactGenerator a).2 (Submodule.inclusion h.1 u)
  have he := LinearPMap.apply_comp_inclusion h u
  rw [← he] at hd
  exact hd

theorem kg_constraint_energy_time_continuous (a : Parameters) (u : fockCoreDomain a) :
    Continuous (fun t : ℝ => (kgConstraintEnergyTime a t u).val) :=
  fockTimeTranslation_strongly_continuous a u.val

end AASCKleinGordon
