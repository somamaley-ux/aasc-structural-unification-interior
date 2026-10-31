import KGPhysicalFrequencyMeasure
import KGWeightedMomentumDynamics
import Mathlib.Analysis.Fourier.LpSpace

/-! Physical Fourier identification on the full continuum L2 carriers.
The coordinate change and Jacobian precede Fourier inversion. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory Filter
open scoped ENNReal SchwartzMap FourierTransform
namespace AASCKleinGordon

def kgPhysicalMomentumME (a : Parameters) : KGSpatialSpace ≃ᵐ Momentum :=
  (kgPhysicalMomentumScaleEquiv a).toHomeomorph.toMeasurableEquiv

theorem kg_physical_momentum_pushforward (a : Parameters) :
    Measure.map (kgPhysicalMomentumME a) (volume : Measure KGSpatialSpace) =
      kgPhysicalMomentumMeasure a := by
  change Measure.map (momentumEuclidean.symm ∘
    fun x : KGSpatialSpace => kgPhysicalMomentumLength a • x) volume = _
  have hm := Measure.map_map momentumEuclidean.symm.continuous.measurable
    (measurable_const.smul measurable_id :
      Measurable (fun x : KGSpatialSpace => kgPhysicalMomentumLength a • x))
      (μ := (volume : Measure KGSpatialSpace))
  rw [← hm]
  rw [Measure.map_addHaar_smul volume (kg_physical_momentum_length_positive a).ne',
    Measure.map_smul, momentumEuclidean_symm_preserves_volume.map_eq]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  rw [abs_of_pos (inv_pos.mpr (pow_pos (kg_physical_momentum_length_positive a) 3))]
  simp only [kgPhysicalMomentumMeasure, kgPhysicalMomentumScale,
    kgPhysicalMomentumLength, one_div]

theorem kg_physical_momentum_measure_preserving (a : Parameters) :
    MeasurePreserving (kgPhysicalMomentumME a) volume (kgPhysicalMomentumMeasure a) :=
  ⟨(kgPhysicalMomentumME a).measurable, kg_physical_momentum_pushforward a⟩

abbrev KGNRSpatialHilbert := Lp ℂ 2 (volume : Measure KGSpatialSpace)

def kgPhysicalFrequencyUnitary (a : Parameters) :
    KGNRMomentumHilbert ≃ₗᵢ[ℂ] KGNRSpatialHilbert :=
  (kgPhysicalMomentumNormalization a).trans
    (lpMeasureEquivalence (kgPhysicalMomentumME a)
      (kg_physical_momentum_measure_preserving a)
      (MeasurePreserving.symm (kgPhysicalMomentumME a)
        (kg_physical_momentum_measure_preserving a)))

theorem kg_physical_frequency_unitary_ae (a : Parameters) (f : KGNRMomentumHilbert) :
    kgPhysicalFrequencyUnitary a f =ᵐ[volume]
      (fun x => (kgPhysicalMomentumRoot a : ℂ) * f (kgPhysicalMomentumScaleEquiv a x)) := by
  have he := kg_physical_momentum_measure_preserving a
  filter_upwards [Lp.coeFn_compMeasurePreserving (kgPhysicalMomentumForward a f) he,
    he.quasiMeasurePreserving.ae (kg_physical_momentum_forward_ae a f)] with x hx hy
  change Lp.compMeasurePreserving (kgPhysicalMomentumME a) he
    (kgPhysicalMomentumForward a f) x = _
  exact hx.trans hy

def kgPhysicalFrequencySchwartz (a : Parameters) (f : 𝓢(Momentum, ℂ)) :
    𝓢(KGSpatialSpace, ℂ) :=
  (kgPhysicalMomentumRoot a : ℂ) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (kgPhysicalMomentumScaleEquiv a) f

theorem kg_physical_frequency_schwartz_apply (a : Parameters) (f : 𝓢(Momentum, ℂ))
    (x : KGSpatialSpace) :
    kgPhysicalFrequencySchwartz a f x =
      (kgPhysicalMomentumRoot a : ℂ) * f (spatialSpectralMomentumCLM a x) := by
  rw [kgPhysicalFrequencySchwartz]
  simp only [SchwartzMap.smul_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, smul_eq_mul,
    kg_physical_momentum_scale_equiv_apply]

theorem kg_physical_frequency_unitary_schwartz (a : Parameters) (f : 𝓢(Momentum, ℂ)) :
    kgPhysicalFrequencyUnitary a (f.toLp 2 volume) =
      (kgPhysicalFrequencySchwartz a f).toLp 2 volume := by
  apply Lp.ext
  have he := kg_physical_momentum_measure_preserving a
  filter_upwards [kg_physical_frequency_unitary_ae a (f.toLp 2 volume),
    he.quasiMeasurePreserving.ae ((kg_physical_momentum_ae a).mpr (f.coeFn_toLp 2 volume)),
    (kgPhysicalFrequencySchwartz a f).coeFn_toLp 2 volume] with x hx hy hz
  rw [hx, hz]
  change (kgPhysicalMomentumRoot a : ℂ) * (f.toLp 2 volume) (kgPhysicalMomentumME a x) = _
  rw [hy, kg_physical_frequency_schwartz_apply]
  rw [← kg_physical_momentum_scale_equiv_apply]
  rfl

def kgPhysicalSpatialUnitary (a : Parameters) :
    KGNRMomentumHilbert ≃ₗᵢ[ℂ] KGNRSpatialHilbert :=
  (kgPhysicalFrequencyUnitary a).trans (Lp.fourierTransformₗᵢ KGSpatialSpace ℂ).symm

def kgIsolatedSpatialUnitary (a : Parameters) :
    wickIsolatedOneParticleSpace a ≃ₗᵢ[ℂ] KGNRSpatialHilbert :=
  (kgIsolatedMomentumUnitary a).trans (kgPhysicalSpatialUnitary a)

theorem kg_physical_spatial_fourier (a : Parameters) (f : KGNRMomentumHilbert) :
    𝓕 (kgPhysicalSpatialUnitary a f) = kgPhysicalFrequencyUnitary a f :=
  (Lp.fourierTransformₗᵢ KGSpatialSpace ℂ).apply_symm_apply _

theorem kg_physical_spatial_unitary_schwartz (a : Parameters) (f : 𝓢(Momentum, ℂ)) :
    kgPhysicalSpatialUnitary a (f.toLp 2 volume) =
      (𝓕⁻ (kgPhysicalFrequencySchwartz a f)).toLp 2 volume := by
  change 𝓕⁻ (kgPhysicalFrequencyUnitary a (f.toLp 2 volume)) = _
  rw [kg_physical_frequency_unitary_schwartz, SchwartzMap.toLp_fourierInv_eq]

def kgNRFrequencyKineticEnergy (a : Parameters) (x : KGSpatialSpace) : ℝ :=
  kgNRKineticEnergy a (kgPhysicalMomentumScaleEquiv a x)

theorem kg_nr_frequency_kinetic_symbol (a : Parameters) (x : KGSpatialSpace) :
    kgNRFrequencyKineticEnergy a x =
      (a.hbar ^ 2 / (2 * a.mass)) * ((2 * Real.pi) ^ 2 * ‖x‖ ^ 2) := by
  unfold kgNRFrequencyKineticEnergy kgNRKineticEnergy
  rw [kg_physical_momentum_scale_equiv_apply, spatialSpectralMomentum_norm_sq]
  ring

theorem kg_nr_frequency_kinetic_measurable (a : Parameters) :
    Measurable (kgNRFrequencyKineticEnergy a) :=
  (kg_nr_kinetic_measurable a).comp (kgPhysicalMomentumScaleEquiv a).continuous.measurable

end AASCKleinGordon
