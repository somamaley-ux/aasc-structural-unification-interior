import KGLicensedEHReceiver

noncomputable section
set_option autoImplicit false
namespace AASCKleinGordon.CanonicalLicensing
open AASCSemanticExhaustion TopologicalSpace

variable (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)

theorem licensed_original_failure_square (κ Λ : ℝ) (coupling : κ ≠ 0)
    (r : LicensedMetricReceiver a s Ω κ Λ) (q : PreparedQuestion a Ω) :
    (licensedReadout a s Ω r []).failure q =
      preparedEventFailure a s Ω
        ⟨restrictedEHPrepared a s Ω (licensedEHResponse a s Ω r), q⟩ := by
  rw [licensed_readout_square a s Ω κ Λ coupling, raw_metric_use_profile_empty]
  obtain ⟨h, rfl⟩ := present_licensed_history_surjective a s Ω κ Λ coupling r
  change restrictedRawFailure a s Ω (restrictedRawHistoryRun a Ω h).current q =
    preparedEventFailure a s Ω ⟨restrictedEHPrepared a s Ω (Quotient.mk _ h), q⟩
  rw [restricted_eh_raw_current]
  exact restricted_raw_failure_square a s Ω _ q

theorem licensed_rejected_metric_request_stays_failed (κ Λ : ℝ) (coupling : κ ≠ 0)
    (r : LicensedMetricReceiver a s Ω κ Λ) (H : MetricSourceProbe Ω)
    (rejected : H ∉ wickOriginalMetricNeighborhood Ω) :
    (licensedReadout a s Ω r []).failure (preparedFiniteRequest a Ω H) =
      some KGExecutionFailure.originalMetricRejection := by
  rw [licensed_original_failure_square a s Ω κ Λ coupling, prepared_finite_request_failure,
    if_neg rejected]

end AASCKleinGordon.CanonicalLicensing
