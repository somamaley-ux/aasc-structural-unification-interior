import KGFockHilbert
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

noncomputable section
open MeasureTheory Filter
open scoped SchwartzMap ENNReal
namespace AASCKleinGordon

theorem particleMeasure_le_volume (a : Parameters) (n : ℕ) : particleMeasure a n ≤ volume := by
  have ho : (particleMeasure a n).toOuterMeasure ≤
      OuterMeasure.pi (fun _ : Fin n => (volume : Measure Momentum).toOuterMeasure) := by
    apply OuterMeasure.le_pi.mpr
    intro s _
    change Measure.pi (fun _ : Fin n => wignerMeasure a) (Set.pi Set.univ s) ≤ _
    rw [Measure.pi_pi]
    exact Finset.prod_le_prod' (fun i _ => wignerMeasure_le_volume a (s i))
  intro s
  change particleMeasure a n s ≤ Measure.pi (fun _ : Fin n => (volume : Measure Momentum)) s
  rw [Measure.pi]
  exact (ho s).trans (le_toMeasure_apply _ _ _)

instance particleMeasure_temperate (a : Parameters) (n : ℕ) : (particleMeasure a n).HasTemperateGrowth where
  exists_integrable := by
    haveI : (volume : Measure (ParticleConfiguration n)).IsAddHaarMeasure := by
      change (Measure.pi (fun _ : Fin n => (volume : Measure Momentum))).IsAddHaarMeasure
      exact Measure.pi.isAddHaarMeasure _
    obtain ⟨k,hk⟩ := (inferInstance : (volume : Measure (ParticleConfiguration n)).HasTemperateGrowth).exists_integrable
    exact ⟨k,hk.mono_measure (particleMeasure_le_volume a n)⟩

instance particleMeasure_finite_on_compacts (a : Parameters) (n : ℕ) :
    IsFiniteMeasureOnCompacts (particleMeasure a n) := by
  unfold particleMeasure
  infer_instance

instance particleMeasure_open_positive (a : Parameters) (n : ℕ) :
    (particleMeasure a n).IsOpenPosMeasure := by
  unfold particleMeasure
  infer_instance

def particleSchwartzToHilbert (a : Parameters) (n : ℕ) :
    𝓢(ParticleConfiguration n,ℂ) →L[ℂ] ParticleHilbert a n :=
  SchwartzMap.toLpCLM ℂ ℂ 2 (particleMeasure a n)

theorem particleSchwartzToHilbert_dense (a : Parameters) (n : ℕ) :
    DenseRange (particleSchwartzToHilbert a n) :=
  SchwartzMap.denseRange_toLpCLM (F:=ℂ) (μ:=particleMeasure a n) (by norm_num : (2:ℝ≥0∞)≠⊤)

theorem particleSchwartzToHilbert_injective (a : Parameters) (n : ℕ) :
    Function.Injective (particleSchwartzToHilbert a n) := by
  intro f g h
  have hf := f.coeFn_toLp 2 (particleMeasure a n)
  have hg := g.coeFn_toLp 2 (particleMeasure a n)
  have hfg : (f : ParticleConfiguration n → ℂ)=ᵐ[particleMeasure a n] g := by
    filter_upwards [hf,hg] with p hp hq
    rw [← hp,← hq]
    exact congrArg (fun z : ParticleHilbert a n => z p) h
  apply SchwartzMap.ext
  exact congrFun (Measure.eq_of_ae_eq hfg f.continuous g.continuous)

end AASCKleinGordon
