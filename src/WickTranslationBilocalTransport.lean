import WickTranslationKernelTransport
import WickLorentzBilocalTransport

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory
open scoped SchwartzMap
namespace AASCKleinGordon

def wickPlanePhase (b q : Spacetime) : ℂ := Real.fourierChar (-inner ℝ b q)

theorem wick_plane_phase_shell (a : Parameters) (b : Spacetime) (p : Momentum) :
    wickPlanePhase b (shellFrequency a p)=eventTranslationPhase a b p := by
  rw [eventTranslationPhase_eq_shell_fourier_phase]
  unfold wickPlanePhase
  simp only [Real.fourierChar_apply]
  congr 1
  push_cast
  ring

theorem wick_plane_phase_neg (b q : Spacetime) :
    wickPlanePhase b (-q)=star (wickPlanePhase b q) := by
  unfold wickPlanePhase
  simp only [inner_neg_right]
  rw [AddChar.map_neg_eq_inv]
  simpa only [Circle.coe_inv] using Circle.coe_inv_eq_conj (Real.fourierChar (-inner ℝ b q))

theorem wick_event_channel_kernel (a : Parameters) (b : Spacetime) (n : ℕ)
    (u v : FiniteParticleCore) (i : Fin 4) (z : ParticleConfiguration (n+2)) :
    wickCoreChannelStateKernel n (coreEventTranslation a b u) (coreEventTranslation a b v) i z =
      star (wickPlanePhase b (wickCoreChannelFrequency0 a n i z)) *
        star (wickPlanePhase b (wickCoreChannelFrequency1 a n i z)) *
          wickCoreChannelStateKernel n u v i z := by
  fin_cases i
  · change star (wickAAStateKernel n ((coreEventTranslation a b v) n).val
      ((coreEventTranslation a b u) (n+2)).val z)=
      star (wickPlanePhase b (shellFrequency a (z 0))) *
        star (wickPlanePhase b (shellFrequency a (z 1))) *
          star (wickAAStateKernel n (v n).val (u (n+2)).val z)
    rw [wick_event_AA_kernel]
    simp only [star_mul, wick_plane_phase_shell]
    ring
  · change wickMixedStateKernel n ((coreEventTranslation a b u) (n+1)).val
      ((coreEventTranslation a b v) (n+1)).val z=_
    rw [wick_event_mixed_kernel]
    change _=star (wickPlanePhase b (shellFrequency a (z 0))) *
      star (wickPlanePhase b (-shellFrequency a (z 1))) *
        wickMixedStateKernel n (u (n+1)).val (v (n+1)).val z
    simp only [wick_plane_phase_neg, wick_plane_phase_shell, star_star]
  · change wickMixedStateKernel n ((coreEventTranslation a b u) (n+1)).val
      ((coreEventTranslation a b v) (n+1)).val z=_
    rw [wick_event_mixed_kernel]
    change _=star (wickPlanePhase b (-shellFrequency a (z 1))) *
      star (wickPlanePhase b (shellFrequency a (z 0))) *
        wickMixedStateKernel n (u (n+1)).val (v (n+1)).val z
    simp only [wick_plane_phase_neg, wick_plane_phase_shell, star_star]
    ring
  · change wickAAStateKernel n ((coreEventTranslation a b u) n).val
      ((coreEventTranslation a b v) (n+2)).val z=_
    rw [wick_event_AA_kernel]
    change _=star (wickPlanePhase b (-shellFrequency a (z 1))) *
      star (wickPlanePhase b (-shellFrequency a (z 0))) *
        wickAAStateKernel n (u n).val (v (n+2)).val z
    simp only [wick_plane_phase_neg, wick_plane_phase_shell, star_star]
    ring

theorem wick_two_unit_phases_cancel (z w v : ℂ) (hz : ‖z‖=1) (hw : ‖w‖=1) :
    z*w*(star z*star w*v)=v := by
  calc
    _=(star z*z)*(star w*w)*v := by ring
    _=v := by rw [wick_unit_phase_star_mul z hz, wick_unit_phase_star_mul w hw]; ring

theorem wick_original_channel_matrix_translation (a : Parameters) (b : Spacetime)
    (n : ℕ) (u v : FiniteParticleCore) (i : Fin 4) (x y : Spacetime) :
    wickCoreChannelMatrix a n (coreEventTranslation a b u) (coreEventTranslation a b v) i
      (b+x) (b+y) = wickCoreChannelMatrix a n u v i x y := by
  unfold wickCoreChannelMatrix
  rw [wickBilocalMatrix_formula a (n+2) _ _ (wickCoreChannelFrequency1_temperate a n i),
    wickBilocalMatrix_formula a (n+2) _ _ (wickCoreChannelFrequency1_temperate a n i)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => by
    dsimp only
    rw [wick_event_channel_kernel]
    simp only [inner_add_left, neg_add, AddChar.map_add_eq_mul,
      Circle.smul_def, smul_eq_mul]
    have cancel := wick_two_unit_phases_cancel
      (wickPlanePhase b (wickCoreChannelFrequency0 a n i z))
      (wickPlanePhase b (wickCoreChannelFrequency1 a n i z))
      (wickCoreChannelStateKernel n u v i z) (by simp [wickPlanePhase]) (by simp [wickPlanePhase])
    change _=(_ : ℂ)
    unfold wickPlanePhase at cancel
    simp only [wickPlanePhase, Circle.coe_mul]
    linear_combination
      ((Real.fourierChar (-inner ℝ x (wickCoreChannelFrequency0 a n i z)) : ℂ) *
        (Real.fourierChar (-inner ℝ y (wickCoreChannelFrequency1 a n i z)) : ℂ)) * cancel)

theorem wick_event_tail_bound (a : Parameters) (b : Spacetime)
    (u : FiniteParticleCore) (N : ℕ) (bound : WickCoreTailBound u N) :
    WickCoreTailBound (coreEventTranslation a b u) N := by
  intro n hn
  change bosonicEventTranslationSchwartzCLM a n b (u n)=0
  rw [bound n hn, map_zero]

theorem wick_original_bilocal_translation (a : Parameters) (b : Spacetime)
    (s : ℝ) (u v : FiniteParticleCore) (x y : Spacetime) :
    originalWickBilocalCore a s (coreEventTranslation a b u) (coreEventTranslation a b v)
      (b+x) (b+y)=originalWickBilocalCore a s u v x y := by
  let N := wickJointCoreCutoff u v
  have hu : WickCoreTailBound u N := (wickCoreTailBound_cutoff u).mono (le_max_left _ _)
  have hv : WickCoreTailBound v N := (wickCoreTailBound_cutoff v).mono (le_max_right _ _)
  rw [originalWickBilocalCore_eq_any_cutoff a s _ _ N
    (wick_event_tail_bound a b u N hu) (wick_event_tail_bound a b v N hv),
    originalWickBilocalCore_eq_any_cutoff a s u v N hu hv]
  unfold originalWickBilocalCoreAt
  simp_rw [wick_original_channel_matrix_translation]

theorem wick_original_bilocal_poincare (a : Parameters) (b : Spacetime)
    (L : ProperLorentzTransform) (s : ℝ) (u v : FiniteParticleCore) (x y : Spacetime) :
    originalWickBilocalCore a s (corePoincare a b L u) (corePoincare a b L v)
      (b+spacetimeLorentzCLE L x) (b+spacetimeLorentzCLE L y) =
      originalWickBilocalCore a s u v x y := by
  change originalWickBilocalCore a s (coreEventTranslation a b (coreLorentz a L u))
    (coreEventTranslation a b (coreLorentz a L v)) _ _=_
  rw [wick_original_bilocal_translation, wick_original_bilocal_lorentz]

end AASCKleinGordon
