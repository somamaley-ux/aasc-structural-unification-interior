import KGEnergyBounds
import KGFiniteParticleCore
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Current Module B's actual weighted continuum one-particle carrier,
H_c=L2(R3,w_c dp), w_c=mc2/E_c. Positivity, measure control and density are
proved, rather than included as certificate fields. Lorentz invariance,
boost generators and the full symmetric Fock completion remain separate. -/
noncomputable section
open MeasureTheory Filter
open scoped SchwartzMap ENNReal
namespace AASCKleinGordon

def wignerWeight (a : Parameters) (p : Momentum) : ℝ := a.mass*a.speed^2/energy a p

theorem wignerWeight_pos (a : Parameters) (p : Momentum) : 0 < wignerWeight a p := by
  apply div_pos _ (energy_pos a p)
  exact mul_pos a.mass_pos (sq_pos_of_pos a.speed_pos)

theorem wignerWeight_le_one (a : Parameters) (p : Momentum) : wignerWeight a p ≤ 1 :=
  (div_le_one (energy_pos a p)).2 (energy_ge_rest a p)

theorem energy_continuous (a : Parameters) : Continuous (energy a) := by
  unfold energy momentumSq
  fun_prop

theorem wignerWeight_continuous (a : Parameters) : Continuous (wignerWeight a) :=
  continuous_const.div (energy_continuous a) (fun p => ne_of_gt (energy_pos a p))

def wignerDensity (a : Parameters) (p : Momentum) : ℝ≥0∞ := ENNReal.ofReal (wignerWeight a p)

theorem wignerDensity_measurable (a : Parameters) : Measurable (wignerDensity a) :=
  (wignerWeight_continuous a).measurable.ennreal_ofReal

theorem wignerDensity_nonzero (a : Parameters) (p : Momentum) : wignerDensity a p≠0 :=
  (ENNReal.ofReal_pos.2 (wignerWeight_pos a p)).ne'

def wignerMeasure (a : Parameters) : Measure Momentum := volume.withDensity (wignerDensity a)

theorem wignerMeasure_le_volume (a : Parameters) : wignerMeasure a ≤ volume := by
  have h : (volume : Measure Momentum).withDensity (wignerDensity a) ≤ volume.withDensity 1 := by
    apply withDensity_mono
    exact Eventually.of_forall (fun p => by
      change ENNReal.ofReal (wignerWeight a p) ≤ 1
      exact ENNReal.ofReal_le_one.2 (wignerWeight_le_one a p))
  simpa [wignerMeasure] using h

theorem volume_absolutelyContinuous_wigner (a : Parameters) :
    (volume : Measure Momentum) ≪ wignerMeasure a :=
  withDensity_absolutelyContinuous' (wignerDensity_measurable a).aemeasurable
    (Eventually.of_forall (wignerDensity_nonzero a))

instance wignerMeasure_open_positive (a : Parameters) : (wignerMeasure a).IsOpenPosMeasure :=
  (volume_absolutelyContinuous_wigner a).isOpenPosMeasure

instance wignerMeasure_finite_on_compacts (a : Parameters) : IsFiniteMeasureOnCompacts (wignerMeasure a) where
  lt_top_of_isCompact := by
    intro K hK
    exact (wignerMeasure_le_volume a K).trans_lt hK.measure_lt_top

instance wignerMeasure_temperate (a : Parameters) : (wignerMeasure a).HasTemperateGrowth where
  exists_integrable := by
    obtain ⟨n,hn⟩ := (inferInstance : (volume : Measure Momentum).HasTemperateGrowth).exists_integrable
    exact ⟨n,hn.mono_measure (wignerMeasure_le_volume a)⟩

abbrev OneParticleHilbert (a : Parameters) := Lp ℂ 2 (wignerMeasure a)

def oneParticleSchwartzToHilbert (a : Parameters) : 𝓢(Momentum,ℂ) →L[ℂ] OneParticleHilbert a :=
  SchwartzMap.toLpCLM ℂ ℂ 2 (wignerMeasure a)

theorem oneParticleSchwartz_dense (a : Parameters) : DenseRange (oneParticleSchwartzToHilbert a) :=
  SchwartzMap.denseRange_toLpCLM (F:=ℂ) (μ:=wignerMeasure a) (by norm_num : (2 : ℝ≥0∞)≠⊤)

theorem oneParticleSchwartz_injective (a : Parameters) :
    Function.Injective (oneParticleSchwartzToHilbert a) := by
  intro f g h
  have hf := f.coeFn_toLp 2 (wignerMeasure a)
  have hg := g.coeFn_toLp 2 (wignerMeasure a)
  have hfg : (f : Momentum → ℂ)=ᵐ[wignerMeasure a] g := by
    filter_upwards [hf,hg] with p hp hq
    rw [← hp,← hq]
    exact congrArg (fun z : OneParticleHilbert a => z p) h
  apply SchwartzMap.ext
  exact congrFun (Measure.eq_of_ae_eq hfg f.continuous g.continuous)

theorem oneParticleHilbert_nontrivial (a : Parameters) : Nontrivial (OneParticleHilbert a) := by
  have hS : Nontrivial 𝓢(Momentum,ℂ) := by
    obtain ⟨f,_,hc,hs,_,h0⟩ := exists_contDiff_tsupport_subset
      (E:=Momentum) (x:=0) (n:=⊤) (s:=Set.univ) (by simp)
    let g : 𝓢(Momentum,ℂ) := (hc.comp_left (g:=Complex.ofReal) (by simp)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hs)
    refine ⟨⟨g,0,?_⟩⟩
    intro hz
    have hv := congrArg (fun z : 𝓢(Momentum,ℂ) => z 0) hz
    simpa [g,h0] using hv
  exact (oneParticleSchwartz_injective a).nontrivial

end AASCKleinGordon
