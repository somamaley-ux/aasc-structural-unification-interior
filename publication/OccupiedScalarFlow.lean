import OriginalWavepacketDetermination

/-! The original finite-speed packet comparisons have a unique separately
continuous realization on the specified spatial Hilbert space. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000

open AASCKleinGordon Filter

namespace AASCOriginalWavepacket

/-- There exists exactly one separately continuous candidate whose rational-time
packet amplitudes have the required finite-speed limits. -/
theorem existsUnique_flow_of_original_amplitudes (a : Parameters) :
    ∃! U : ℝ → KGNRSpatialHilbert → KGNRSpatialHilbert,
      OriginalAmplitudeLimits a U ∧ (∀ t, Continuous (U t)) ∧
        (∀ f, Continuous (fun t => U t f)) := by
  refine ⟨fun t f => kgNRSpatialFreeFlow a t f, ?_, ?_⟩
  · exact ⟨free_flow_has_original_wavepacket_limits a,
      fun t => (kgNRSpatialFreeFlow a t).continuous, kg_nr_full_spatial_time_continuous a⟩
  · rintro U ⟨hU, hstate, htime⟩
    funext t f
    exact flow_of_original_wavepacket_limits a U hstate htime hU t f

private theorem separate_readings {Time Packet : Type*}
    (seq : Time → Packet → Packet → ℝ → ℂ) (v w : Time → Packet → Packet → ℂ)
    (right : ∀ q f g, Tendsto (seq q f g) atTop (nhds (v q f g)))
    (wrong : ¬ ∀ q f g, Tendsto (seq q f g) atTop (nhds (w q f g))) :
    ∃ q f g, Tendsto (seq q f g) atTop (nhds (v q f g)) ∧ v q f g ≠ w q f g := by
  classical
  obtain ⟨q, hq⟩ := Classical.not_forall.mp wrong
  obtain ⟨f, hf⟩ := Classical.not_forall.mp hq
  obtain ⟨g, hg⟩ := Classical.not_forall.mp hf
  refine ⟨q, f, g, right q f g, fun h => hg ?_⟩
  rw [← h]
  exact right q f g
/-- If a separately continuous candidate differs from the free evolution,
some original preparation and probe at a rational time give it the wrong
complex amplitude. The source sequence actually converges at that test. -/
theorem distinct_flow_has_separating_packet (a : Parameters)
    (U : ℝ → KGNRSpatialHilbert → KGNRSpatialHilbert)
    (hstate : ∀ t, Continuous (U t)) (htime : ∀ f, Continuous (fun t => U t f))
    (hdiff : U ≠ fun t f => kgNRSpatialFreeFlow a t f) :
    ∃ (q : ℚ) (f g : kgOriginalOneCore a),
      let embed := kgOriginalOneCoreSpatialEmbedding a
      let original := inner ℂ (embed g) (kgNRSpatialFreeFlow a (q : ℝ) (embed f))
      Tendsto (fun c : ℝ => inner ℂ (embed g) (kgOriginalRestSpatialFlow a c (q : ℝ) (embed f)))
        atTop (nhds original) ∧
      original ≠ inner ℂ (embed g) (U (q : ℝ) (embed f)) := by
  let embed := kgOriginalOneCoreSpatialEmbedding a
  let seq := fun (q : ℚ) (f g : kgOriginalOneCore a) (c : ℝ) =>
    inner ℂ (embed g) (kgOriginalRestSpatialFlow a c (q : ℝ) (embed f))
  let obs := fun (V : ℝ → KGNRSpatialHilbert → KGNRSpatialHilbert) (q : ℚ)
      (f g : kgOriginalOneCore a) => inner ℂ (embed g) (V (q : ℝ) (embed f))
  let free := fun t f => kgNRSpatialFreeFlow a t f
  exact separate_readings seq (obs free) (obs U) (free_flow_has_original_wavepacket_limits a)
    (fun h => hdiff (funext fun t => funext fun f =>
      flow_of_original_wavepacket_limits a U hstate htime h t f))

end AASCOriginalWavepacket
