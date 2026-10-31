import KGWeightedMomentumIdentification
import KGNRPhysicalTime

/-! Exact scalar time/rest-flow comparisons through constructed normalizations.
The varying-speed limit uses the unitary at that speed. No claim about the
unchanged Lorentz pullback, full Fock reduction, spatial domain or curved
Einstein background follows from scalar multiplier commutation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory Filter
open scoped Topology
namespace AASCKleinGordon

def kgCovariantMomentumUnitary (a : Parameters) :
    WickCovariantHilbert a ≃ₗᵢ[ℂ] KGNRMomentumHilbert :=
  (wickCovariantNormalization a).symm.trans (kgWeightedMomentumUnitary a)

def kgIsolatedMomentumUnitary (a : Parameters) :
    wickIsolatedOneParticleSpace a ≃ₗᵢ[ℂ] KGNRMomentumHilbert :=
  (wickIsolatedCovariantHilbert a).trans (kgCovariantMomentumUnitary a)

theorem kg_isolated_momentum_original_normalization (a : Parameters)
    (f : OneParticleHilbert a) :
    kgIsolatedMomentumUnitary a (wickWignerToIsolated a f) = kgWeightedMomentumUnitary a f := by
  simp [kgIsolatedMomentumUnitary, kgCovariantMomentumUnitary,
    wickIsolatedCovariantHilbert]

theorem kg_covariant_momentum_unitary_ae (a : Parameters) (f : WickCovariantHilbert a) :
    kgCovariantMomentumUnitary a f =ᵐ[volume]
      (fun p => (kgWignerRoot a p : ℂ) * (wickCovariantRoot a : ℂ)⁻¹ * f p) := by
  filter_upwards [kg_weighted_momentum_forward_ae a (wickCovariantInverse a f),
    (kg_wigner_ae a).mp (wick_covariant_inverse_ae a f)] with p hp hq
  change kgWeightedMomentumForward a (wickCovariantInverse a f) p = _
  rw [hp, hq, mul_assoc]

theorem kg_covariant_flat_ae (a : Parameters) {P : Momentum → Prop} :
    (∀ᵐ p ∂wickCovariantMeasure a, P p) ↔ ∀ᵐ p ∂(volume : Measure Momentum), P p :=
  (wick_covariant_ae a).trans (kg_wigner_ae a)

theorem kg_covariant_momentum_phase_intertwining (a : Parameters)
    (v : Momentum → ℝ) (hv : Measurable v) (hbar t : ℝ) (f : WickCovariantHilbert a) :
    kgCovariantMomentumUnitary a
      (Multiplication.phaseMultiplier (μ := wickCovariantMeasure a) v hv hbar t f) =
    Multiplication.phaseMultiplier (μ := (volume : Measure Momentum)) v hv hbar t
      (kgCovariantMomentumUnitary a f) := by
  apply Lp.ext
  filter_upwards [kg_covariant_momentum_unitary_ae a
      (Multiplication.phaseMultiplier (μ := wickCovariantMeasure a) v hv hbar t f),
    kg_covariant_momentum_unitary_ae a f,
    Multiplication.phaseMultiplier_ae (μ := (volume : Measure Momentum)) v hv hbar t
      (kgCovariantMomentumUnitary a f),
    (kg_covariant_flat_ae a).mp
      (Multiplication.phaseMultiplier_ae (μ := wickCovariantMeasure a) v hv hbar t f)]
      with p hp hf ht hs
  rw [hp, ht, hf, hs]
  ring

theorem kg_covariant_original_time_flat_intertwining (a : Parameters) (t : ℝ)
    (f : WickCovariantHilbert a) :
    kgCovariantMomentumUnitary a (kgNRCovariantTimeTranslation a t f) =
      Multiplication.phaseUnitary (μ := (volume : Measure Momentum)) (energy a)
        (energy_continuous a).measurable a.hbar t (kgCovariantMomentumUnitary a f) := by
  rw [kg_nr_covariant_time_translation_multiplier]
  exact kg_covariant_momentum_phase_intertwining a (energy a)
    (energy_continuous a).measurable a.hbar t f

theorem kg_covariant_original_rest_flat_intertwining (a : Parameters)
    (c : ℝ) (hc : 0 < c) (t : ℝ) (f : WickCovariantHilbert (kgNRParameters a c hc)) :
    kgCovariantMomentumUnitary (kgNRParameters a c hc)
      (kgNRActualCovariantRestFlow a c hc t f) =
    kgNRMomentumFlow a c t (kgCovariantMomentumUnitary (kgNRParameters a c hc) f) := by
  rw [kg_nr_actual_covariant_rest_flow_is_multiplier]
  exact kg_covariant_momentum_phase_intertwining (kgNRParameters a c hc)
    (kgNRDispersion a c) (kg_nr_dispersion_measurable a c) a.hbar t f

theorem kg_isolated_original_time_flat_intertwining (a : Parameters) (t : ℝ)
    (f : wickIsolatedOneParticleSpace a) :
    kgIsolatedMomentumUnitary a
      (wickIsolatedPoincareRepresentation a
        ⟨Multiplicative.ofAdd (timeTranslationEvent a t), 1⟩ f) =
    Multiplication.phaseUnitary (μ := (volume : Measure Momentum)) (energy a)
      (energy_continuous a).measurable a.hbar t (kgIsolatedMomentumUnitary a f) := by
  change kgCovariantMomentumUnitary a
    (wickIsolatedCovariantHilbert a (wickIsolatedPoincareRepresentation a _ f)) = _
  rw [wick_isolated_covariant_poincare_intertwining]
  exact kg_covariant_original_time_flat_intertwining a t (wickIsolatedCovariantHilbert a f)

def kgNRActualIsolatedRestFlow (a : Parameters) (c : ℝ) (hc : 0 < c) (t : ℝ)
    (f : wickIsolatedOneParticleSpace (kgNRParameters a c hc)) :
    wickIsolatedOneParticleSpace (kgNRParameters a c hc) :=
  Translation.phase a.hbar t (-a.mass * c ^ 2) •
    wickIsolatedPoincareRepresentation (kgNRParameters a c hc)
      ⟨Multiplicative.ofAdd (timeTranslationEvent (kgNRParameters a c hc) t), 1⟩ f

theorem kg_isolated_original_rest_flat_intertwining (a : Parameters)
    (c : ℝ) (hc : 0 < c) (t : ℝ)
    (f : wickIsolatedOneParticleSpace (kgNRParameters a c hc)) :
    kgIsolatedMomentumUnitary (kgNRParameters a c hc)
      (kgNRActualIsolatedRestFlow a c hc t f) =
    kgNRMomentumFlow a c t (kgIsolatedMomentumUnitary (kgNRParameters a c hc) f) := by
  have he : wickIsolatedCovariantHilbert (kgNRParameters a c hc)
      (kgNRActualIsolatedRestFlow a c hc t f) =
      kgNRActualCovariantRestFlow a c hc t
        (wickIsolatedCovariantHilbert (kgNRParameters a c hc) f) := by
    simp only [kgNRActualIsolatedRestFlow, map_smul,
      wick_isolated_covariant_poincare_intertwining,
      kgNRActualCovariantRestFlow, kgNRCovariantTimeTranslation]
  change kgCovariantMomentumUnitary (kgNRParameters a c hc)
    (wickIsolatedCovariantHilbert (kgNRParameters a c hc)
      (kgNRActualIsolatedRestFlow a c hc t f)) = _
  rw [he]
  exact kg_covariant_original_rest_flat_intertwining a c hc t
    (wickIsolatedCovariantHilbert (kgNRParameters a c hc) f)

/-- The transported actual isolated-sector carrier at each positive speed.
The nonpositive-speed branch only totalizes the function for the atTop limit. -/
def kgTransportedOriginalRestFlow (a : Parameters) (c t : ℝ)
    (f : KGNRMomentumHilbert) : KGNRMomentumHilbert :=
  if hc : 0 < c then
    kgCovariantMomentumUnitary (kgNRParameters a c hc)
      (kgNRActualCovariantRestFlow a c hc t
        ((kgCovariantMomentumUnitary (kgNRParameters a c hc)).symm f))
  else f

theorem kg_transported_original_rest_flow_eq (a : Parameters) (c : ℝ) (hc : 0 < c)
    (t : ℝ) (f : KGNRMomentumHilbert) :
    kgTransportedOriginalRestFlow a c t f = kgNRMomentumFlow a c t f := by
  simp only [kgTransportedOriginalRestFlow, dif_pos hc,
    kg_covariant_original_rest_flat_intertwining, LinearIsometryEquiv.apply_symm_apply]

theorem kg_transported_original_rest_flow_strong_limit (a : Parameters) (t : ℝ)
    (f : KGNRMomentumHilbert) :
    Tendsto (fun c : ℝ => kgTransportedOriginalRestFlow a c t f) atTop
      (nhds (kgNRFreeMomentumFlow a t f)) := by
  apply (kg_nr_full_momentum_flow_strong_limit a t f).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
  exact (kg_transported_original_rest_flow_eq a c hc t f).symm

def kgTransportedIsolatedRestFlow (a : Parameters) (c t : ℝ)
    (f : KGNRMomentumHilbert) : KGNRMomentumHilbert :=
  if hc : 0 < c then
    kgIsolatedMomentumUnitary (kgNRParameters a c hc)
      (kgNRActualIsolatedRestFlow a c hc t
        ((kgIsolatedMomentumUnitary (kgNRParameters a c hc)).symm f))
  else f

theorem kg_transported_isolated_rest_flow_eq (a : Parameters) (c : ℝ) (hc : 0 < c)
    (t : ℝ) (f : KGNRMomentumHilbert) :
    kgTransportedIsolatedRestFlow a c t f = kgNRMomentumFlow a c t f := by
  simp only [kgTransportedIsolatedRestFlow, dif_pos hc,
    kg_isolated_original_rest_flat_intertwining, LinearIsometryEquiv.apply_symm_apply]

theorem kg_transported_isolated_rest_flow_strong_limit (a : Parameters) (t : ℝ)
    (f : KGNRMomentumHilbert) :
    Tendsto (fun c : ℝ => kgTransportedIsolatedRestFlow a c t f) atTop
      (nhds (kgNRFreeMomentumFlow a t f)) := by
  apply (kg_nr_full_momentum_flow_strong_limit a t f).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
  exact (kg_transported_isolated_rest_flow_eq a c hc t f).symm

end AASCKleinGordon
