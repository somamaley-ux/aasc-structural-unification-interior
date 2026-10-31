import SRNativeOrientedClockMetricAttachment

/-! Derive a unit future proper-parameter tangent from the actual native
Hamiltonian clock; no moving-duration law is a hypothesis. Passive comparison
transport can subsequently act on this tangent and the same marked events. -/
namespace AASCMetricConstruction.SRIntegration
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def srNativeProperTangent (μ0 : ℝ) (z : SRNativeClockState E) : ℝ × E :=
  (srNativeClockHamiltonian μ0 z / srNativeClockMass μ0 z,
    (srNativeClockMass μ0 z)⁻¹ • z.momentum)

theorem sr_native_proper_tangent_future (μ0 : ℝ) (z : SRNativeClockState E)
    (positive : 0 < srNativeClockMass μ0 z) : 0 < (srNativeProperTangent μ0 z).1 :=
  div_pos (sr_native_clock_hamiltonian_positive μ0 z positive) positive

theorem sr_native_proper_tangent_unit (μ0 : ℝ) (z : SRNativeClockState E)
    (positive : 0 < srNativeClockMass μ0 z) :
    (srNativeProperTangent μ0 z).1^2 - ‖(srNativeProperTangent μ0 z).2‖^2 = 1 := by
  have h := sr_native_clock_hamiltonian_square μ0 z
  simp only [srNativeProperTangent,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos positive]
  field_simp
  nlinarith

theorem sr_native_proper_tangent_uses_source_constructed_form
    [FiniteDimensional ℝ E] [Nontrivial E]
    (dimension : 2 ≤ Module.finrank ℝ E) (μ0 : ℝ) (z : SRNativeClockState E)
    (positive : 0 < srNativeClockMass μ0 z) :
    srSourceLorentzForm (srRayClock (E:=E)) (srRayRestVector (E:=E))
      (sr_ray_rest_clock_one (E:=E))
      (srCompletedOrderToConeSource (srRayClock (E:=E)) (srRayRestVector (E:=E))
        (srNativeOrientedCompletedOrderSource (E:=E) dimension))
      (srNativeProperTangent μ0 z) = 1 := by
  rw [sr_native_oriented_order_constructor_matches_full_original_ray_form,
    sr_full_ray_source_constructor_computes_lorentz_form_everywhere]
  exact sr_native_proper_tangent_unit μ0 z positive

theorem sr_native_actual_coasting_event_in_proper_parameter (μ0 θ τ : ℝ)
    (z : SRNativeClockState E) (positive : 0 < srNativeClockMass μ0 z) :
    (θ + τ * (srNativeProperTangent μ0 z).1,
      (srNativeClockCoastFlow μ0 (τ * (srNativeProperTangent μ0 z).1) z).position) =
      (θ,z.position) + τ • srNativeProperTangent μ0 z := by
  have hp := sr_native_clock_hamiltonian_positive μ0 z positive
  apply Prod.ext
  · rfl
  · change z.position + (τ * (srNativeClockHamiltonian μ0 z / srNativeClockMass μ0 z)) •
        ((srNativeClockHamiltonian μ0 z)⁻¹ • z.momentum) =
      z.position + τ • ((srNativeClockMass μ0 z)⁻¹ • z.momentum)
    rw [smul_smul,smul_smul]
    have scalar : τ * (srNativeClockHamiltonian μ0 z / srNativeClockMass μ0 z) *
        (srNativeClockHamiltonian μ0 z)⁻¹ = τ * (srNativeClockMass μ0 z)⁻¹ := by
      field_simp
    rw [scalar]

theorem sr_native_actual_coasting_reading_in_proper_parameter (μ0 τ : ℝ)
    (z : SRNativeClockState E) (positive : 0 < srNativeClockMass μ0 z) :
    (srNativeClockCoastFlow μ0 (τ * (srNativeProperTangent μ0 z).1) z).reading =
      z.reading + τ := by
  have hp := sr_native_clock_hamiltonian_positive μ0 z positive
  simp only [srNativeClockCoastFlow,srNativeProperTangent,srNativeClockRate]
  congr 1
  field_simp

theorem sr_native_interval_readout_is_actual_rate (μ0 : ℝ) (c : SRNativeClockUse E) :
    srNativeClockActualInterval μ0 c = (c.finish-c.start) * srNativeClockRate μ0 c.record.2.2 := by
  simp only [srNativeClockActualInterval,srNativeCoastingMarkedRecord,srNativeClockCoastFlow]
  ring

theorem sr_native_actual_clock_rate_is_positive_metric_root
    [FiniteDimensional ℝ E] [Nontrivial E]
    (dimension : 2 ≤ Module.finrank ℝ E) (μ0 : ℝ) (z : SRNativeClockState E)
    (positive : 0 < srNativeClockMass μ0 z) :
    Real.sqrt (srSourceLorentzForm (srRayClock (E:=E)) (srRayRestVector (E:=E))
      (sr_ray_rest_clock_one (E:=E))
      (srCompletedOrderToConeSource (srRayClock (E:=E)) (srRayRestVector (E:=E))
        (srNativeOrientedCompletedOrderSource (E:=E) dimension))
      (1,srNativeClockVelocity μ0 z)) = srNativeClockRate μ0 z := by
  rw [sr_native_same_oriented_order_source_form_matches_actual_clock_rate dimension μ0 z positive]
  exact Real.sqrt_sq (sr_native_clock_reading_rate_positive_bounded μ0 z positive).1.le

def srNativeExtendClockUse (μ0 δ : ℝ) (c : SRNativeClockUse E) : SRNativeClockUse E :=
  let d : SRNativeClockUse E := {c with finish := c.finish+δ}
  {d with claimed := srNativeClockActualInterval μ0 d}

theorem sr_native_clock_extension_valid (μ0 δ : ℝ) (c : SRNativeClockUse E)
    (valid : srNativeClockUseValid μ0 c) (forward : 0 ≤ δ) :
    srNativeClockUseValid μ0 (srNativeExtendClockUse μ0 δ c) := by
  refine ⟨valid.1,?_,rfl⟩
  change c.start ≤ c.finish+δ
  exact valid.2.1.trans (le_add_of_nonneg_right forward)

theorem sr_native_clock_extension_retains_every_marked_record (μ0 δ σ : ℝ)
    (c : SRNativeClockUse E) :
    srNativeCoastingMarkedRecord μ0 (srNativeExtendClockUse μ0 δ c).record σ =
      srNativeCoastingMarkedRecord μ0 c.record σ := rfl

theorem sr_native_clock_extension_readout_additive (μ0 δ : ℝ) (c : SRNativeClockUse E) :
    srNativeClockActualInterval μ0 (srNativeExtendClockUse μ0 δ c) =
      srNativeClockActualInterval μ0 c + δ * srNativeClockRate μ0 c.record.2.2 := by
  rw [sr_native_interval_readout_is_actual_rate,sr_native_interval_readout_is_actual_rate]
  change (c.finish+δ-c.start)*srNativeClockRate μ0 c.record.2.2 = _
  ring

theorem sr_native_clock_rebase_extension_commutes [FiniteDimensional ℝ E] [Nontrivial E]
    (μ0 h δ : ℝ) (c : SRNativeClockUse E) :
    srNativeExtendClockUse μ0 δ (srNativeClockUseRedescription μ0 h c) =
      srNativeClockUseRedescription μ0 h (srNativeExtendClockUse μ0 δ c) := by
  simp [srNativeExtendClockUse,srNativeClockUseRedescription,srNativeClockActualInterval,
    sr_native_clock_redescription_preserves_every_original_marked_record]

#print axioms sr_native_proper_tangent_uses_source_constructed_form
#print axioms sr_native_actual_coasting_reading_in_proper_parameter
#print axioms sr_native_actual_clock_rate_is_positive_metric_root
#print axioms sr_native_clock_extension_valid
end
end AASCMetricConstruction.SRIntegration
