import KGPauliJordanCCRIdentification
import Mathlib.Analysis.Fourier.Convolution

noncomputable section
set_option maxHeartbeats 600000
open MeasureTheory
open scoped SchwartzMap FourierTransform Pointwise
namespace AASCKleinGordon

theorem commutatorCorrelation_eq_convolution (h k : 𝓢(Spacetime,ℂ)) :
    commutatorCorrelationTest h k=SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
      (spacetimeNegationTestCLM h) k := by
  apply (FourierTransform.fourierCLE ℂ 𝓢(Spacetime,ℂ)).injective
  ext q
  change 𝓕 (commutatorCorrelationTest h k) q=
    𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (spacetimeNegationTestCLM h) k) q
  rw [fourier_commutatorCorrelationTest,SchwartzMap.fourier_convolution,
    SchwartzMap.pairing_apply_apply,fourier_spacetimeNegationTest]
  rfl

theorem commutatorCorrelation_apply_integral (h k : 𝓢(Spacetime,ℂ)) (z : Spacetime) :
    commutatorCorrelationTest h k z=∫ y : Spacetime,h (-y)*k (z-y) := by
  rw [commutatorCorrelation_eq_convolution,SchwartzMap.convolution_apply]
  rfl

theorem commutatorCorrelation_support_subset (h k : 𝓢(Spacetime,ℂ)) :
    Function.support (commutatorCorrelationTest h k)⊆tsupport k+(-tsupport h) := by
  intro z hz
  by_contra hn
  apply hz
  rw [commutatorCorrelation_apply_integral]
  apply integral_eq_zero_of_ae
  exact ae_of_all volume (fun y => by
    by_cases hh : h (-y)=0
    · simp only [hh,zero_mul,Pi.zero_apply]
    by_cases hk : k (z-y)=0
    · simp only [hk,mul_zero,Pi.zero_apply]
    have hht : -y∈tsupport h := subset_closure hh
    have hkt : z-y∈tsupport k := subset_closure hk
    have hyt : y∈-tsupport h := by simpa only [Set.mem_neg,neg_neg] using hht
    exact False.elim (hn ⟨z-y,hkt,y,hyt,sub_add_cancel z y⟩))

theorem commutatorCorrelation_tsupport_subset (h k : 𝓢(Spacetime,ℂ))
    (hh : HasCompactSupport (h : Spacetime → ℂ)) (hk : HasCompactSupport (k : Spacetime → ℂ)) :
    tsupport (commutatorCorrelationTest h k)⊆tsupport k+(-tsupport h) := by
  apply closure_minimal (commutatorCorrelation_support_subset h k)
  exact (hk.isCompact.add hh.isCompact.neg).isClosed

theorem commutatorCorrelation_compact_support (h k : 𝓢(Spacetime,ℂ))
    (hh : HasCompactSupport (h : Spacetime → ℂ)) (hk : HasCompactSupport (k : Spacetime → ℂ)) :
    HasCompactSupport (commutatorCorrelationTest h k : Spacetime → ℂ) := by
  exact (hk.isCompact.add hh.isCompact.neg).of_isClosed_subset isClosed_closure
    (commutatorCorrelation_tsupport_subset h k hh hk)

def spacetimeMinkowskiSquare (z : Spacetime) : ℝ :=
  minkowskiDot (fun i => z i) (fun i => z i)
def closedCausalCone : Set Spacetime := {z | spacetimeMinkowskiSquare z≤0}

def SpacelikeSeparatedTests (h k : 𝓢(Spacetime,ℂ)) : Prop :=
  ∀ x∈tsupport h,∀ y∈tsupport k,0<spacetimeMinkowskiSquare (y-x)

theorem commutatorCorrelation_causally_disjoint (h k : 𝓢(Spacetime,ℂ))
    (hh : HasCompactSupport (h : Spacetime → ℂ)) (hk : HasCompactSupport (k : Spacetime → ℂ))
    (hs : SpacelikeSeparatedTests h k) :
    Disjoint (tsupport (commutatorCorrelationTest h k)) closedCausalCone := by
  apply Set.disjoint_left.mpr
  intro z hz hc
  obtain ⟨y,hy,w,hw,he⟩ := commutatorCorrelation_tsupport_subset h k hh hk hz
  have hwt : -w∈tsupport h := by simpa only [Set.mem_neg] using hw
  have hp := hs (-w) hwt y hy
  have he' : y-(-w)=z := by simpa only [sub_neg_eq_add] using he
  rw [he'] at hp
  exact (not_lt_of_ge hc) hp

end AASCKleinGordon
