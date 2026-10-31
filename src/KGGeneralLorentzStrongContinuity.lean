import KGGeneralLorentzWeakContinuity
import L2HilbertSumConvergence

noncomputable section
set_option maxHeartbeats 2400000
open MeasureTheory Filter
open scoped SchwartzMap Topology
namespace AASCKleinGordon

theorem continuous_isometric_orbits_of_dense_topological {P E D : Type*}
    [TopologicalSpace P] [MetricSpace E]
    (U : P → E → E) (hU : ∀ r,Isometry (U r)) (j : D → E) (hd : DenseRange j)
    (hj : ∀ d,Continuous (fun r => U r (j d))) (f : E) : Continuous (fun r => U r f) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  apply Metric.continuousAt_iff'.mpr
  intro ε hε
  obtain ⟨g,⟨d,rfl⟩,hg⟩ := Metric.mem_closure_iff.mp (hd f) (ε/3) (by positivity)
  have hm := Metric.continuousAt_iff'.mp ((hj d).continuousAt (x:=s)) (ε/3) (by positivity)
  filter_upwards [hm] with r hr
  have ht := dist_triangle4 (U r f) (U r (j d)) (U s (j d)) (U s f)
  rw [(hU r).dist_eq,(hU s).dist_eq,dist_comm (j d) f] at ht
  linarith

theorem continuous_isometric_action_of_orbits {P E : Type*}
    [TopologicalSpace P] [MetricSpace E]
    (U : P → E → E) (hU : ∀ r,Isometry (U r))
    (hj : ∀ f,Continuous (fun r => U r f)) : Continuous (fun q : P × E => U q.1 q.2) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  apply Metric.continuousAt_iff'.mpr
  intro ε hε
  have hv := Metric.continuousAt_iff'.mp
    ((continuous_snd : Continuous (fun p : P × E => p.2)).continuousAt (x:=q)) (ε/2) (by positivity)
  have hr := Metric.continuousAt_iff'.mp
    (((hj q.2).comp continuous_fst).continuousAt (x:=q)) (ε/2) (by positivity)
  filter_upwards [hv,hr] with p hp hpr
  dsimp only [Function.comp_def] at hpr
  have ht := dist_triangle (U p.1 p.2) (U p.1 q.2) (U q.1 q.2)
  rw [(hU p.1).dist_eq] at ht
  linarith

theorem particleLorentz_schwartz_strongly_continuous (a : Parameters) (n : ℕ)
    (H : 𝓢(ParticleConfiguration n,ℂ)) :
    Continuous (fun L : ProperLorentzTransform => particleLorentzUnitary a n L (particleSchwartzToHilbert a n H)) := by
  let f := particleSchwartzToHilbert a n H
  apply continuous_iff_continuousAt.mpr
  intro M
  have hi : Continuous (fun L : ProperLorentzTransform => inner ℂ (particleLorentzUnitary a n L f)
      (particleLorentzUnitary a n M f)) := by
    simpa only [f,particleLorentz_intertwines_schwartz] using
      particleLorentz_schwartz_inner_continuous a n H (particleLorentzSchwartzCLM a n M H)
  have hs : Continuous (fun L : ProperLorentzTransform =>
      ‖particleLorentzUnitary a n L f-particleLorentzUnitary a n M f‖^2) := by
    simp_rw [norm_sub_sq (𝕜:=ℂ),LinearIsometryEquiv.norm_map]
    exact (continuous_const.sub (continuous_const.mul (Complex.continuous_re.comp hi))).add continuous_const
  have hn : Continuous (fun L : ProperLorentzTransform =>
      ‖particleLorentzUnitary a n L f-particleLorentzUnitary a n M f‖) := by
    have hr : Continuous (fun L : ProperLorentzTransform => Real.sqrt
        (‖particleLorentzUnitary a n L f-particleLorentzUnitary a n M f‖^2)) :=
      Real.continuous_sqrt.comp hs
    simpa only [Real.sqrt_sq_eq_abs,abs_norm] using hr
  rw [ContinuousAt,← tendsto_sub_nhds_zero_iff]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [sub_self,norm_zero] using hn.tendsto M

theorem particleLorentz_strongly_continuous (a : Parameters) (n : ℕ) (f : ParticleHilbert a n) :
    Continuous (fun L : ProperLorentzTransform => particleLorentzUnitary a n L f) :=
  continuous_isometric_orbits_of_dense_topological (fun L => particleLorentzUnitary a n L)
    (fun L => (particleLorentzUnitary a n L).isometry) (particleSchwartzToHilbert a n)
    (particleSchwartzToHilbert_dense a n) (particleLorentz_schwartz_strongly_continuous a n) f

theorem bosonicLorentz_strongly_continuous (a : Parameters) (n : ℕ) (f : bosonicHilbertSector a n) :
    Continuous (fun L : ProperLorentzTransform => bosonicLorentzUnitary a n L f) := by
  apply continuous_induced_rng.mpr
  exact particleLorentz_strongly_continuous a n f.val

theorem fockLorentz_strongly_continuous (a : Parameters) (f : FockHilbert a) :
    Continuous (fun L : ProperLorentzTransform => fockLorentzUnitary a L f) := by
  apply continuous_iff_continuousAt.mpr
  intro M
  rw [ContinuousAt,← tendsto_sub_nhds_zero_iff]
  apply HilbertSum.tendsto_zero_of_dominated _ (fun n => 2*‖f n‖) ?_ ?_ ?_
  · have h := ((lp.memℓp f).summable (by norm_num)).mul_left 4
    convert h using 1
    funext n
    simp only [ENNReal.toReal_ofNat,Real.rpow_two,mul_pow]
    ring
  · intro n
    have h := (bosonicLorentz_strongly_continuous a n (f n)).tendsto M
    simpa only [sub_self] using h.sub_const (bosonicLorentzUnitary a n M (f n))
  · exact Eventually.of_forall (fun L n => by
      change ‖bosonicLorentzUnitary a n L (f n)-bosonicLorentzUnitary a n M (f n)‖≤2*‖f n‖
      calc
        _ ≤ ‖bosonicLorentzUnitary a n L (f n)‖+‖bosonicLorentzUnitary a n M (f n)‖ := norm_sub_le _ _
        _ = 2*‖f n‖ := by rw [LinearIsometryEquiv.norm_map,LinearIsometryEquiv.norm_map,two_mul])

theorem fockLorentz_jointly_continuous (a : Parameters) :
    Continuous (fun q : ProperLorentzTransform × FockHilbert a => fockLorentzUnitary a q.1 q.2) :=
  continuous_isometric_action_of_orbits (fun L => fockLorentzUnitary a L)
    (fun L => (fockLorentzUnitary a L).isometry) (fockLorentz_strongly_continuous a)

end AASCKleinGordon
