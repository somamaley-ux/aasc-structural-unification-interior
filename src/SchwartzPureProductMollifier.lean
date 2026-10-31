import SchwartzPurePairBochner
import SchwartzJetMollifierApproximation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Filter Topology
open scoped SchwartzMap
namespace AASCKleinGordon

def wickPureMollifierFactor (ε : ℝ) (hε : 0<ε) : 𝓢(Momentum,ℂ) :=
  ((wickJetMollifierBump Momentum ε hε).hasCompactSupport.comp_left
    (g:=Complex.ofReal) (by simp)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp (wickJetMollifierBump Momentum ε hε).contDiff)

theorem wick_pure_mollifier_factor_apply (ε : ℝ) (hε : 0<ε) (p : Momentum) :
    wickPureMollifierFactor ε hε p=((wickJetMollifierBump Momentum ε hε p:ℝ):ℂ) := rfl

theorem wick_pure_mollifier_factor_compact (ε : ℝ) (hε : 0<ε) :
    HasCompactSupport (wickPureMollifierFactor ε hε) :=
  (wickJetMollifierBump Momentum ε hε).hasCompactSupport.comp_left
    (g:=Complex.ofReal) (by simp)

def wickPureMollifierRaw (ε : ℝ) (hε : 0<ε) (z : ParticleConfiguration 2) : ℝ :=
  wickJetMollifierBump Momentum ε hε (z 0)*wickJetMollifierBump Momentum ε hε (z 1)

theorem wick_pure_mollifier_pair_raw (ε : ℝ) (hε : 0<ε) (z : ParticleConfiguration 2) :
    wickCovariantPairTest (wickPureMollifierFactor ε hε) (wickPureMollifierFactor ε hε) z=
      (wickPureMollifierRaw ε hε z:ℂ) := by
  rw [wick_covariant_pair_test_apply,wick_pure_mollifier_factor_apply,wick_pure_mollifier_factor_apply]
  simp only [wickPureMollifierRaw,Complex.star_def,Complex.conj_ofReal,Complex.ofReal_mul]

theorem wick_pure_mollifier_raw_continuous (ε : ℝ) (hε : 0<ε) :
    Continuous (wickPureMollifierRaw ε hε) :=
  ((wickJetMollifierBump Momentum ε hε).continuous.comp (continuous_apply 0)).mul
    ((wickJetMollifierBump Momentum ε hε).continuous.comp (continuous_apply 1))

theorem wick_pure_mollifier_raw_nonneg (ε : ℝ) (hε : 0<ε) (z : ParticleConfiguration 2) :
    0≤wickPureMollifierRaw ε hε z :=
  mul_nonneg (wickJetMollifierBump Momentum ε hε).nonneg (wickJetMollifierBump Momentum ε hε).nonneg

theorem wick_pure_mollifier_raw_compact (ε : ℝ) (hε : 0<ε) :
    HasCompactSupport (wickPureMollifierRaw ε hε) := by
  have he : wickPureMollifierRaw ε hε=(fun z =>
      (wickCovariantPairTest (wickPureMollifierFactor ε hε) (wickPureMollifierFactor ε hε) z).re) := by
    funext z
    rw [wick_pure_mollifier_pair_raw]
    rfl
  rw [he]
  exact (wick_compact_actual_pair _ _ (wick_pure_mollifier_factor_compact ε hε)
    (wick_pure_mollifier_factor_compact ε hε)).comp_left (g:=Complex.re) (by simp)

theorem wick_pure_mollifier_raw_at_zero (ε : ℝ) (hε : 0<ε) :
    wickPureMollifierRaw ε hε 0=1 := by
  have hzero : wickJetMollifierBump Momentum ε hε (0:Momentum)=1 :=
    (wickJetMollifierBump Momentum ε hε).one_of_mem_closedBall (by
      simp only [Metric.mem_closedBall,dist_self]
      exact (wickJetMollifierBump Momentum ε hε).rIn_pos.le)
  simp only [wickPureMollifierRaw,Pi.zero_apply,hzero,mul_one]

def wickPureMollifierMass (ε : ℝ) (hε : 0<ε) : ℝ :=
  ∫ z : ParticleConfiguration 2,wickPureMollifierRaw ε hε z

theorem wick_pure_mollifier_mass_positive (ε : ℝ) (hε : 0<ε) :
    0<wickPureMollifierMass ε hε :=
  integral_pos_of_integrable_nonneg_nonzero (x:=(0:ParticleConfiguration 2)) (wick_pure_mollifier_raw_continuous ε hε)
    ((wick_pure_mollifier_raw_continuous ε hε).integrable_of_hasCompactSupport
      (wick_pure_mollifier_raw_compact ε hε))
    (wick_pure_mollifier_raw_nonneg ε hε)
    (by rw [wick_pure_mollifier_raw_at_zero];exact one_ne_zero)

/-- The normalization uses the actual auxiliary coordinate-volume integral.
It does not change the physical covariant source measure. -/
def wickPureMollifierWeight (ε : ℝ) (hε : 0<ε) (z : ParticleConfiguration 2) : ℝ :=
  wickPureMollifierRaw ε hε z/(wickPureMollifierMass ε hε)

def wickPureMollifierTest (ε : ℝ) (hε : 0<ε) : 𝓢(ParticleConfiguration 2,ℂ) :=
  ((wickPureMollifierMass ε hε)⁻¹:ℂ) •
    wickCovariantPairTest (wickPureMollifierFactor ε hε) (wickPureMollifierFactor ε hε)

theorem wick_pure_mollifier_test_apply (ε : ℝ) (hε : 0<ε) (z : ParticleConfiguration 2) :
    wickPureMollifierTest ε hε z=(wickPureMollifierWeight ε hε z:ℂ) := by
  rw [wickPureMollifierTest,SchwartzMap.smul_apply,wick_pure_mollifier_pair_raw]
  simp only [wickPureMollifierWeight,smul_eq_mul,Complex.ofReal_div]
  rw [div_eq_mul_inv]
  exact mul_comm _ _

theorem wick_pure_mollifier_test_span (ε : ℝ) (hε : 0<ε) :
    wickPureMollifierTest ε hε∈wickPurePairSpan :=
  wickPurePairSpan.smul_mem _ (wick_pure_pair_mem_span _ _)

theorem wick_pure_mollifier_test_compact (ε : ℝ) (hε : 0<ε) :
    HasCompactSupport (wickPureMollifierTest ε hε) :=
  (wick_compact_actual_pair _ _ (wick_pure_mollifier_factor_compact ε hε)
    (wick_pure_mollifier_factor_compact ε hε)).comp_left
      (g:=fun z : ℂ => ((wickPureMollifierMass ε hε)⁻¹:ℂ)*z) (by simp)

theorem wick_pure_mollifier_weight_continuous (ε : ℝ) (hε : 0<ε) :
    Continuous (wickPureMollifierWeight ε hε) :=
  (wick_pure_mollifier_raw_continuous ε hε).div_const _

theorem wick_pure_mollifier_weight_compact (ε : ℝ) (hε : 0<ε) :
    HasCompactSupport (wickPureMollifierWeight ε hε) :=
  (wick_pure_mollifier_raw_compact ε hε).comp_left
    (g:=fun r : ℝ => r/wickPureMollifierMass ε hε) (by simp)

theorem wick_pure_mollifier_weight_nonneg (ε : ℝ) (hε : 0<ε) (z : ParticleConfiguration 2) :
    0≤wickPureMollifierWeight ε hε z :=
  div_nonneg (wick_pure_mollifier_raw_nonneg ε hε z) (wick_pure_mollifier_mass_positive ε hε).le

theorem wick_pure_mollifier_weight_integral (ε : ℝ) (hε : 0<ε) :
    (∫ z : ParticleConfiguration 2,wickPureMollifierWeight ε hε z)=1 := by
  simp only [wickPureMollifierWeight,div_eq_mul_inv]
  rw [integral_mul_const]
  exact mul_inv_cancel₀ (wick_pure_mollifier_mass_positive ε hε).ne'

theorem wick_pure_mollifier_weight_support_bound (ε : ℝ) (hε : 0<ε)
    (z : ParticleConfiguration 2) (hz : wickPureMollifierWeight ε hε z≠0) : ‖z‖≤ε := by
  have hraw : wickPureMollifierRaw ε hε z≠0 := by
    intro h
    apply hz
    simp only [wickPureMollifierWeight,h,zero_div]
  have h0 := (mul_ne_zero_iff.mp hraw).1
  have h1 := (mul_ne_zero_iff.mp hraw).2
  have hb0 : ‖z 0‖<ε := by
    have hm : z 0∈Function.support (wickJetMollifierBump Momentum ε hε) := h0
    rw [(wickJetMollifierBump Momentum ε hε).support_eq] at hm
    simpa only [Metric.mem_ball,dist_zero_right,wickJetMollifierBump] using hm
  have hb1 : ‖z 1‖<ε := by
    have hm : z 1∈Function.support (wickJetMollifierBump Momentum ε hε) := h1
    rw [(wickJetMollifierBump Momentum ε hε).support_eq] at hm
    simpa only [Metric.mem_ball,dist_zero_right,wickJetMollifierBump] using hm
  apply (pi_norm_le_iff_of_nonneg hε.le).mpr
  intro i
  fin_cases i
  · exact hb0.le
  · exact hb1.le

end AASCKleinGordon
