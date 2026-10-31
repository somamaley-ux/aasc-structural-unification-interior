import KGGeneralLorentzJacobian
import KGLorentzBoostMeasure

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace AASCKleinGordon

def lorentzJacobian (a : Parameters) (L : ProperLorentzTransform) (p : Momentum) : ℝ :=
  energy a (lorentzShellMap a L p)/energy a p

theorem lorentzJacobian_pos (a : Parameters) (L : ProperLorentzTransform) (p : Momentum) :
    0<lorentzJacobian a L p := div_pos (energy_pos a _) (energy_pos a _)

theorem lorentzJacobian_continuous (a : Parameters) (L : ProperLorentzTransform) :
    Continuous (lorentzJacobian a L) :=
  ((energy_continuous a).comp (lorentzShellMap_temperate a L).1.continuous).div
    (energy_continuous a) (fun p => (energy_pos a p).ne')

theorem lorentz_map_jacobian_volume (a : Parameters) (L : ProperLorentzTransform) :
    Measure.map (lorentzShellMap a L)
      (volume.withDensity (fun p => ENNReal.ofReal (lorentzJacobian a L p)))=
        (volume : Measure Momentum) := by
  have himage : lorentzShellMap a L '' Set.univ=Set.univ := by
    rw [Set.image_univ]
    exact Set.range_eq_univ.mpr (lorentzShellMap_surjective a L)
  have hdet (p : Momentum) : |(lorentzShellDerivativeCLM a L p).det|=lorentzJacobian a L p := by
    rw [abs_of_pos (lorentzShellDerivative_det_pos a L p),lorentzShellDerivative_det]
    rfl
  have h:=map_withDensity_abs_det_fderiv_eq_addHaar (volume : Measure Momentum)
    (s:=Set.univ) (f:=lorentzShellMap a L) (f':=lorentzShellDerivativeCLM a L)
    MeasurableSet.univ.nullMeasurableSet
    (fun p _ => (lorentzShellMap_hasFDerivAt a L p).hasFDerivWithinAt)
    (fun p _ q _ hpq => lorentzShellMap_injective a L hpq)
  simpa only [Measure.restrict_univ,himage,hdet] using h

theorem lorentz_wigner_weight_jacobian (a : Parameters) (L : ProperLorentzTransform) (p : Momentum) :
    wignerWeight a (lorentzShellMap a L p)*lorentzJacobian a L p=wignerWeight a p := by
  unfold wignerWeight lorentzJacobian
  field_simp [(energy_pos a (lorentzShellMap a L p)).ne',(energy_pos a p).ne']

theorem lorentzShellMap_preserves_wignerMeasure (a : Parameters) (L : ProperLorentzTransform) :
    MeasurePreserving (lorentzShellMap a L) (wignerMeasure a) (wignerMeasure a) := by
  have hF : Measurable (lorentzShellMap a L):=(lorentzShellMap_temperate a L).1.continuous.measurable
  refine ⟨hF,?_⟩
  apply map_weighted_of_jacobian volume (lorentzShellMap a L)
    (fun p => ENNReal.ofReal (lorentzJacobian a L p)) (wignerDensity a) hF
    (lorentzJacobian_continuous a L).measurable.ennreal_ofReal (wignerDensity_measurable a)
    (lorentz_map_jacobian_volume a L)
  intro p
  change ENNReal.ofReal (wignerWeight a (lorentzShellMap a L p))*
    ENNReal.ofReal (lorentzJacobian a L p)=ENNReal.ofReal (wignerWeight a p)
  rw [← ENNReal.ofReal_mul (wignerWeight_pos a _).le,lorentz_wigner_weight_jacobian]

end AASCKleinGordon
