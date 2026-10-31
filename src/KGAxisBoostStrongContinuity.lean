import KGAxisBoostWeakContinuity
import L2HilbertSumConvergence

noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Filter
open scoped SchwartzMap Topology
namespace AASCKleinGordon

theorem continuous_isometric_orbits_of_dense {E D : Type*} [MetricSpace E]
    (U : ℝ → E → E) (hU : ∀ r,Isometry (U r)) (j : D → E) (hd : DenseRange j)
    (hj : ∀ d,Continuous (fun r => U r (j d))) (f : E) : Continuous (fun r => U r f) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨g,⟨d,rfl⟩,hg⟩ := Metric.mem_closure_iff.mp (hd f) (ε/3) (by positivity)
  obtain ⟨δ,hδ,hcont⟩ := Metric.continuousAt_iff.mp (hj d).continuousAt (ε/3) (by positivity)
  refine ⟨δ,hδ,fun r hr => ?_⟩
  have hm := hcont hr
  have ht := dist_triangle4 (U r f) (U r (j d)) (U s (j d)) (U s f)
  rw [(hU r).dist_eq,(hU s).dist_eq,dist_comm (j d) f] at ht
  linarith

theorem particleAxisBoost_schwartz_strongly_continuous (a : Parameters) (n : ℕ)
    (H : 𝓢(ParticleConfiguration n,ℂ)) :
    Continuous (fun r => particleAxisBoostUnitary a n r (particleSchwartzToHilbert a n H)) := by
  let f := particleSchwartzToHilbert a n H
  apply continuous_iff_continuousAt.mpr
  intro s
  have hi : Continuous (fun r => inner ℂ (particleAxisBoostUnitary a n r f)
      (particleAxisBoostUnitary a n s f)) := by
    simpa only [f,particleAxisBoost_intertwines_schwartz] using
      particleAxisBoost_schwartz_inner_continuous a n H (particleAxisBoostSchwartzCLM a n s H)
  have hs : Continuous (fun r => ‖particleAxisBoostUnitary a n r f-particleAxisBoostUnitary a n s f‖^2) := by
    simp_rw [norm_sub_sq (𝕜:=ℂ),LinearIsometryEquiv.norm_map]
    exact (continuous_const.sub (continuous_const.mul (Complex.continuous_re.comp hi))).add continuous_const
  have hn : Continuous (fun r => ‖particleAxisBoostUnitary a n r f-particleAxisBoostUnitary a n s f‖) := by
    have hr : Continuous (fun r => Real.sqrt
        (‖particleAxisBoostUnitary a n r f-particleAxisBoostUnitary a n s f‖^2)) :=
      Real.continuous_sqrt.comp hs
    simpa only [Real.sqrt_sq_eq_abs,abs_norm] using hr
  rw [ContinuousAt,← tendsto_sub_nhds_zero_iff]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [sub_self,norm_zero] using hn.tendsto s

theorem particleAxisBoost_strongly_continuous (a : Parameters) (n : ℕ) (f : ParticleHilbert a n) :
    Continuous (fun r => particleAxisBoostUnitary a n r f) :=
  continuous_isometric_orbits_of_dense (fun r => particleAxisBoostUnitary a n r)
    (fun r => (particleAxisBoostUnitary a n r).isometry) (particleSchwartzToHilbert a n)
    (particleSchwartzToHilbert_dense a n) (particleAxisBoost_schwartz_strongly_continuous a n) f

theorem bosonicAxisBoost_strongly_continuous (a : Parameters) (n : ℕ) (f : bosonicHilbertSector a n) :
    Continuous (fun r => bosonicAxisBoostUnitary a n r f) := by
  apply continuous_induced_rng.mpr
  exact particleAxisBoost_strongly_continuous a n f.val

theorem fockAxisBoost_strongly_continuous (a : Parameters) (f : FockHilbert a) :
    Continuous (fun r => fockAxisBoostUnitary a r f) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  rw [ContinuousAt,← tendsto_sub_nhds_zero_iff]
  apply HilbertSum.tendsto_zero_of_dominated _ (fun n => 2*‖f n‖) ?_ ?_ ?_
  · have h := ((lp.memℓp f).summable (by norm_num)).mul_left 4
    convert h using 1
    funext n
    simp only [ENNReal.toReal_ofNat,Real.rpow_two,mul_pow]
    ring
  · intro n
    have h := (bosonicAxisBoost_strongly_continuous a n (f n)).tendsto s
    simpa only [sub_self] using h.sub_const (bosonicAxisBoostUnitary a n s (f n))
  · exact Eventually.of_forall (fun r n => by
      change ‖bosonicAxisBoostUnitary a n r (f n)-bosonicAxisBoostUnitary a n s (f n)‖≤2*‖f n‖
      calc
        _ ≤ ‖bosonicAxisBoostUnitary a n r (f n)‖+‖bosonicAxisBoostUnitary a n s (f n)‖ := norm_sub_le _ _
        _ = 2*‖f n‖ := by rw [LinearIsometryEquiv.norm_map,LinearIsometryEquiv.norm_map,two_mul])

end AASCKleinGordon
