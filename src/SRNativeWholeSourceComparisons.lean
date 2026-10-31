import SRNativeClockLicensing
import SROrientedCompletedOrderSource

/-! Whole-source comparisons of the explicit coasting clock/ray branch:
spatial rest maps preserve body energy, phase, all marked times and interval
domains; translations transport those same original records and events. These
are model-law calculations, not assumed metric-commutation certificates. -/
namespace AASCMetricConstruction
noncomputable section
set_option autoImplicit false
variable {E:Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

def srNativeBodyRest (A:E ≃ₗᵢ[ℝ] E) (z:SRNativeClockState E) : SRNativeClockState E:=
  ⟨A z.position,A z.momentum,z.reading,z.internalEnergy⟩

theorem sr_native_rest_preserves_actual_body_hamiltonian (A:E ≃ₗᵢ[ℝ] E)
    (μ0:ℝ) (z:SRNativeClockState E) :
    srNativeClockHamiltonian μ0 (srNativeBodyRest A z)=srNativeClockHamiltonian μ0 z := by
  simp only [srNativeClockHamiltonian,srNativeBodyRest,LinearIsometryEquiv.norm_map,
    srNativeClockMass]

theorem sr_native_rest_commutes_with_complete_coasting_flow (A:E ≃ₗᵢ[ℝ] E)
    (μ0 t:ℝ) (z:SRNativeClockState E) :
    srNativeBodyRest A (srNativeClockCoastFlow μ0 t z)=
      srNativeClockCoastFlow μ0 t (srNativeBodyRest A z) := by
  cases z
  simp [srNativeBodyRest,srNativeClockCoastFlow,srNativeClockVelocity,srNativeClockRate,
    srNativeClockHamiltonian,srNativeClockMass,map_add,map_smul]

def srNativeRecordRest {ID:Type*} (A:E ≃ₗᵢ[ℝ] E)
    (r:ID × (ℝ × SRNativeClockState E)) : ID × (ℝ × SRNativeClockState E):=
  (r.1,r.2.1,srNativeBodyRest A r.2.2)

theorem sr_native_rest_transports_all_original_marked_records {ID:Type*}
    (A:E ≃ₗᵢ[ℝ] E) (μ0 σ:ℝ) (r:ID × (ℝ × SRNativeClockState E)) :
    srNativeCoastingMarkedRecord μ0 (srNativeRecordRest A r) σ=
      ((srNativeCoastingMarkedRecord μ0 r σ).1,
        srNativeBodyRest A (srNativeCoastingMarkedRecord μ0 r σ).2) := by
  apply Prod.ext
  · rfl
  · exact (sr_native_rest_commutes_with_complete_coasting_flow A μ0 _ _).symm

def srNativeUseRest (A:E ≃ₗᵢ[ℝ] E) (c:SRNativeClockUse E) : SRNativeClockUse E:=
  {c with record:=srNativeRecordRest A c.record}

theorem sr_native_rest_preserves_original_clock_use_domains_and_answers
    (A:E ≃ₗᵢ[ℝ] E) (μ0:ℝ) (c:SRNativeClockUse E) :
    srNativeClockUseValid μ0 (srNativeUseRest A c) ↔ srNativeClockUseValid μ0 c := by
  simp [srNativeClockUseValid,srNativeClockActualInterval,srNativeUseRest,
    srNativeRecordRest,srNativeBodyRest,srNativeCoastingMarkedRecord,srNativeClockCoastFlow,
    srNativeClockRate,srNativeClockHamiltonian,srNativeClockMass]

theorem sr_native_rest_transports_original_ray_and_reflection_records
    (A:E ≃ₗᵢ[ℝ] E) (ε ℓ:ℝ) (n:E) (k:ℕ) :
    srRayRestComparison A (srNativePositiveRayMomentum ε n)=srNativePositiveRayMomentum ε (A n) ∧
      srRayRestComparison A (srNativeProtocolReflection ℓ n k)=srNativeProtocolReflection ℓ (A n) k := by
  constructor <;> apply Prod.ext <;> simp [sr_ray_rest_comparison_value,
    srNativePositiveRayMomentum,srNativeProtocolReflection,map_smul]

def srNativeBodyTranslate (b:E) (z:SRNativeClockState E) : SRNativeClockState E:=
  ⟨z.position+b,z.momentum,z.reading,z.internalEnergy⟩

def srNativeRecordTranslate {ID:Type*} (d:ℝ × E)
    (r:ID × (ℝ × SRNativeClockState E)) : ID × (ℝ × SRNativeClockState E):=
  (r.1,r.2.1+d.1,srNativeBodyTranslate d.2 r.2.2)

theorem sr_native_translation_transports_complete_original_records {ID:Type*}
    (d:ℝ × E) (μ0 σ:ℝ) (r:ID × (ℝ × SRNativeClockState E)) :
    srNativeCoastingMarkedRecord μ0 (srNativeRecordTranslate d r) (σ+d.1)=
      ((srNativeCoastingMarkedRecord μ0 r σ).1,
       srNativeBodyTranslate d.2 (srNativeCoastingMarkedRecord μ0 r σ).2) := by
  have ht:σ+d.1-(r.2.1+d.1)=σ-r.2.1:=by ring
  simp only [srNativeCoastingMarkedRecord,srNativeRecordTranslate,ht,srNativeBodyTranslate,
    srNativeClockCoastFlow,srNativeClockVelocity,srNativeClockRate,srNativeClockHamiltonian,
    srNativeClockMass]
  congr 2
  abel

theorem sr_native_whole_translation_comparison_has_no_double_identity (d:ℝ × E)
    (double:d+d=0) : d=0 := by
  have hh:(2:ℝ) • d=0:=by simpa only [two_smul] using double
  exact (smul_eq_zero.mp hh).resolve_left (by norm_num)

theorem sr_native_whole_translation_event_action_free_and_transitive :
    (∀ d e:ℝ × E,(∀ p:ℝ × E,p+d=p+e) → d=e) ∧
      (∀ p q:ℝ × E,∃ d:ℝ × E,p+d=q) := by
  constructor
  · intro d e he
    simpa only [zero_add] using he 0
  · intro p q
    exact ⟨q-p,by abel⟩

theorem sr_native_entire_clock_translation_action_has_exact_event_action_profile
    (d e:ℝ × E) :
    ((∀ p:ℝ × E,p+d=p+e) ∧
      (∀ r:Fin 2 × (ℝ × SRNativeClockState E),srNativeRecordTranslate d r=srNativeRecordTranslate e r)) ↔
        (∀ p:ℝ × E,p+d=p+e) := by
  constructor
  · exact fun h=>h.1
  · intro he
    have same:d=e:=sr_native_whole_translation_event_action_free_and_transitive.1 d e he
    exact ⟨he,fun r=>congrArg (fun x:ℝ × E=>srNativeRecordTranslate x r) same⟩

#print axioms sr_native_rest_preserves_actual_body_hamiltonian
#print axioms sr_native_rest_commutes_with_complete_coasting_flow
#print axioms sr_native_rest_transports_all_original_marked_records
#print axioms sr_native_rest_preserves_original_clock_use_domains_and_answers
#print axioms sr_native_rest_transports_original_ray_and_reflection_records
#print axioms sr_native_translation_transports_complete_original_records
#print axioms sr_native_whole_translation_comparison_has_no_double_identity
#print axioms sr_native_whole_translation_event_action_free_and_transitive
#print axioms sr_native_entire_clock_translation_action_has_exact_event_action_profile
end
end AASCMetricConstruction
