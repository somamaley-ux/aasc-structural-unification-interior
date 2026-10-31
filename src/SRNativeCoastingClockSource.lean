import KernelReference.ContextualQuotient
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! Actual zero-force sector of SR 15.3--15.4. Rest energy includes internal
clock energy. All marked-time state/phase/identity records are retained, not a
selected future-free signature. This is not the driven pulse or its symplectic
reduction, nor the full action-to-distributional-response attachment. -/
namespace AASCMetricConstruction
noncomputable section
set_option autoImplicit false
open AASC.KernelReference
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure SRNativeClockState (E:Type*) where
  position:E
  momentum:E
  reading:ℝ
  internalEnergy:ℝ

def srNativeClockMass (μ0:ℝ) (z:SRNativeClockState E) : ℝ:=μ0+z.internalEnergy
def srNativeClockHamiltonian (μ0:ℝ) (z:SRNativeClockState E) : ℝ:=
  Real.sqrt (‖z.momentum‖^2+(srNativeClockMass μ0 z)^2)
def srNativeClockVelocity (μ0:ℝ) (z:SRNativeClockState E) : E:=
  (srNativeClockHamiltonian μ0 z)⁻¹ • z.momentum
def srNativeClockRate (μ0:ℝ) (z:SRNativeClockState E) : ℝ:=
  srNativeClockMass μ0 z/srNativeClockHamiltonian μ0 z

def srNativeClockCoastFlow (μ0 s:ℝ) (z:SRNativeClockState E) : SRNativeClockState E where
  position:=z.position+s • srNativeClockVelocity μ0 z
  momentum:=z.momentum
  reading:=z.reading+s*srNativeClockRate μ0 z
  internalEnergy:=z.internalEnergy

theorem sr_native_clock_internal_energy_is_in_same_body_mass (μ0:ℝ) (z:SRNativeClockState E) :
    srNativeClockMass μ0 z=μ0+z.internalEnergy := rfl

theorem sr_native_clock_hamiltonian_positive (μ0:ℝ) (z:SRNativeClockState E)
    (positive:0<srNativeClockMass μ0 z) : 0<srNativeClockHamiltonian μ0 z := by
  apply Real.sqrt_pos.mpr
  nlinarith [sq_nonneg ‖z.momentum‖]

theorem sr_native_clock_hamiltonian_square (μ0:ℝ) (z:SRNativeClockState E) :
    (srNativeClockHamiltonian μ0 z)^2=‖z.momentum‖^2+(srNativeClockMass μ0 z)^2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem sr_native_clock_actual_velocity_subluminal (μ0:ℝ) (z:SRNativeClockState E)
    (positive:0<srNativeClockMass μ0 z) : ‖srNativeClockVelocity μ0 z‖<1 := by
  have hp:=sr_native_clock_hamiltonian_positive μ0 z positive
  have hs:=sr_native_clock_hamiltonian_square μ0 z
  have hn:‖z.momentum‖<srNativeClockHamiltonian μ0 z:=by nlinarith [norm_nonneg z.momentum]
  rw [srNativeClockVelocity,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hp]
  rw [← div_eq_inv_mul]
  exact (div_lt_one hp).mpr hn

theorem sr_native_clock_reading_rate_positive_bounded (μ0:ℝ) (z:SRNativeClockState E)
    (positive:0<srNativeClockMass μ0 z) :
    0<srNativeClockRate μ0 z ∧ srNativeClockRate μ0 z≤1 := by
  have hp:=sr_native_clock_hamiltonian_positive μ0 z positive
  have hs:=sr_native_clock_hamiltonian_square μ0 z
  have hm:srNativeClockMass μ0 z≤srNativeClockHamiltonian μ0 z:=by
    nlinarith [sq_nonneg ‖z.momentum‖]
  exact ⟨div_pos positive hp,(div_le_one hp).mpr hm⟩

theorem sr_native_rest_clock_has_rate_one (μ0:ℝ) (z:SRNativeClockState E)
    (positive:0<srNativeClockMass μ0 z) (rest:z.momentum=0) : srNativeClockRate μ0 z=1 := by
  have hh:srNativeClockHamiltonian μ0 z=srNativeClockMass μ0 z:=by
    simp only [srNativeClockHamiltonian,rest,norm_zero,zero_pow (by norm_num:2≠0),zero_add]
    exact Real.sqrt_sq (le_of_lt positive)
  rw [srNativeClockRate,hh,div_self (ne_of_gt positive)]

theorem sr_native_coasting_flow_zero (μ0:ℝ) (z:SRNativeClockState E) :
    srNativeClockCoastFlow μ0 0 z=z := by cases z; simp [srNativeClockCoastFlow]

theorem sr_native_coasting_flow_composition (μ0 s t:ℝ) (z:SRNativeClockState E) :
    srNativeClockCoastFlow μ0 s (srNativeClockCoastFlow μ0 t z)=
      srNativeClockCoastFlow μ0 (s+t) z := by
  cases z
  simp only [srNativeClockCoastFlow,srNativeClockVelocity,srNativeClockHamiltonian,
    srNativeClockMass,srNativeClockRate,add_smul,add_mul]
  congr 1 <;> abel

def srNativeCoastingMarkedRecord {ID:Type*} (μ0:ℝ)
    (r:ID × (ℝ × SRNativeClockState E)) (σ:ℝ) : ID × SRNativeClockState E:=
  (r.1,srNativeClockCoastFlow μ0 (σ-r.2.1) r.2.2)

def srNativeCoastingSourceQuotient {ID:Type*} (μ0:ℝ)
    (r:ID × (ℝ × SRNativeClockState E)) : ID × SRNativeClockState E:=
  srNativeCoastingMarkedRecord μ0 r 0

theorem sr_all_original_marked_coasting_records_recovered {ID:Type*} (μ0:ℝ)
    (r:ID × (ℝ × SRNativeClockState E)) (σ:ℝ) :
    srNativeCoastingMarkedRecord μ0 r σ=
      ((srNativeCoastingSourceQuotient μ0 r).1,
       srNativeClockCoastFlow μ0 σ (srNativeCoastingSourceQuotient μ0 r).2) := by
  apply Prod.ext
  · rfl
  · change srNativeClockCoastFlow μ0 (σ-r.2.1) r.2.2=
      srNativeClockCoastFlow μ0 σ (srNativeClockCoastFlow μ0 (0-r.2.1) r.2.2)
    rw [sr_native_coasting_flow_composition]
    congr 1
    ring

theorem sr_native_coasting_source_quotient_surjective {ID:Type*} (μ0:ℝ) :
    Function.Surjective (srNativeCoastingSourceQuotient (E:=E) (ID:=ID) μ0) := by
  rintro ⟨id,z⟩
  exact ⟨(id,0,z),by simp [srNativeCoastingSourceQuotient,srNativeCoastingMarkedRecord,
    sr_native_coasting_flow_zero]⟩

theorem sr_native_coasting_exact_full_original_state_phase_identity_fibres {ID:Type*} (μ0:ℝ)
    (r s:ID × (ℝ × SRNativeClockState E)) :
    srNativeCoastingSourceQuotient μ0 r=srNativeCoastingSourceQuotient μ0 s ↔
      ContextualQuotient.Equivalent (srNativeCoastingMarkedRecord μ0) r s := by
  constructor
  · intro he σ
    rw [sr_all_original_marked_coasting_records_recovered,
      sr_all_original_marked_coasting_records_recovered,he]
  · exact fun he=>he 0

theorem sr_native_coasting_unique_exact_public_kernel_source {ID:Type*} (μ0:ℝ) :
    ∃! e:ContextualQuotient.CanonicalQuotient (srNativeCoastingMarkedRecord (E:=E) (ID:=ID) μ0) ≃
      (ID × SRNativeClockState E),
      ∀ r,e (ContextualQuotient.classify (srNativeCoastingMarkedRecord μ0) r)=
        srNativeCoastingSourceQuotient μ0 r :=
  ContextualQuotient.unique_exact_classifier _ _
    (sr_native_coasting_source_quotient_surjective μ0)
    (sr_native_coasting_exact_full_original_state_phase_identity_fibres μ0)

#print axioms sr_native_clock_internal_energy_is_in_same_body_mass
#print axioms sr_native_clock_hamiltonian_positive
#print axioms sr_native_clock_hamiltonian_square
#print axioms sr_native_clock_actual_velocity_subluminal
#print axioms sr_native_clock_reading_rate_positive_bounded
#print axioms sr_native_rest_clock_has_rate_one
#print axioms sr_native_coasting_flow_zero
#print axioms sr_native_coasting_flow_composition
#print axioms sr_all_original_marked_coasting_records_recovered
#print axioms sr_native_coasting_source_quotient_surjective
#print axioms sr_native_coasting_exact_full_original_state_phase_identity_fibres
#print axioms sr_native_coasting_unique_exact_public_kernel_source
end
end AASCMetricConstruction
