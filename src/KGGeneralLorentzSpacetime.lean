import KGGeneralLorentzSchwartz
import KGSpacetimeAxisBoostMeasure
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped SchwartzMap FourierTransform
namespace AASCKleinGordon

def spacetimeLorentzCLE (L : ProperLorentzTransform) : Spacetime ≃L[ℝ] Spacetime :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).trans
    ((properLorentzFourCLE L).trans (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm)

@[simp] theorem spacetimeLorentzCLE_apply (L : ProperLorentzTransform) (x : Spacetime) (i : Fin 4) :
    spacetimeLorentzCLE L x i=L.val (fun j => x j) i := rfl

theorem spacetimeLorentz_one (x : Spacetime) : spacetimeLorentzCLE 1 x=x := by ext i; rfl

theorem spacetimeLorentz_mul (L M : ProperLorentzTransform) (x : Spacetime) :
    spacetimeLorentzCLE (L*M) x=spacetimeLorentzCLE L (spacetimeLorentzCLE M x) := by ext i; rfl

theorem spacetimeLorentz_inverse (L : ProperLorentzTransform) (x : Spacetime) :
    spacetimeLorentzCLE L⁻¹ (spacetimeLorentzCLE L x)=x := by
  rw [← spacetimeLorentz_mul,inv_mul_cancel,spacetimeLorentz_one]

theorem spacetimeLorentz_det (L : ProperLorentzTransform) :
    LinearMap.det (spacetimeLorentzCLE L).toLinearMap=1 := by
  have h:=LinearMap.det_conj (properLorentzFourCLE L).toLinearMap
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm.toLinearEquiv
  change LinearMap.det (spacetimeLorentzCLE L).toLinearMap=LinearMap.det L.val.toLinearMap at h
  rw [h,properLorentz_det]

theorem spacetimeLorentz_preserves_volume (L : ProperLorentzTransform) :
    MeasurePreserving (spacetimeLorentzCLE L) := by
  refine ⟨(spacetimeLorentzCLE L).continuous.measurable,?_⟩
  have h:=Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure Spacetime)
    (f:=(spacetimeLorentzCLE L).toLinearMap) (by rw [spacetimeLorentz_det]; norm_num)
  simpa only [spacetimeLorentz_det,inv_one,abs_one,ENNReal.ofReal_one,one_smul] using h

def spacetimeLorentzTranspose (L : ProperLorentzTransform) : Spacetime →L[ℝ] Spacetime :=
  (spacetimeLorentzCLE L).toContinuousLinearMap.adjoint

theorem spacetimeLorentz_inner_transpose (L : ProperLorentzTransform) (x y : Spacetime) :
    inner ℝ (spacetimeLorentzCLE L x) y=inner ℝ x (spacetimeLorentzTranspose L y) :=
  (ContinuousLinearMap.adjoint_inner_right (spacetimeLorentzCLE L).toContinuousLinearMap x y).symm

theorem inner_shellCovector_eq_minkowski (a : Parameters) (x : Spacetime) (p : Momentum) :
    inner ℝ x (shellCovector a p)=minkowskiDot (fun i => x i) (massShell a p) := by
  rw [shellCovector_eq_join]
  simp only [PiLp.inner_apply,RCLike.inner_apply]
  simp [Fin.sum_univ_succ,minkowskiDot,massShell,fourCoordinateJoin,fourCoordinateCons]
  ring

theorem spacetimeLorentz_inner_shellCovector (a : Parameters) (L : ProperLorentzTransform)
    (x : Spacetime) (p : Momentum) :
    inner ℝ (spacetimeLorentzCLE L x) (shellCovector a p)=
      inner ℝ x (shellCovector a (lorentzShellMap a L⁻¹ p)) := by
  rw [inner_shellCovector_eq_minkowski,inner_shellCovector_eq_minkowski,massShell_lorentzShellMap]
  change minkowskiDot (L.val (fun i => x i)) (massShell a p)=
    minkowskiDot (fun i => x i) (L.val.symm (massShell a p))
  have h:=properLorentz_metric L (fun i => x i) (L.val.symm (massShell a p))
  simpa only [L.val.apply_symm_apply] using h

theorem shellFrequency_lorentz_transpose (a : Parameters) (L : ProperLorentzTransform) (p : Momentum) :
    shellFrequency a (lorentzShellMap a L⁻¹ p)=spacetimeLorentzTranspose L (shellFrequency a p) := by
  apply ext_inner_left ℝ
  intro x
  rw [← spacetimeLorentz_inner_transpose]
  simp only [shellFrequency,inner_smul_right,spacetimeLorentz_inner_shellCovector]

def spacetimeLorentzTestCLM (L : ProperLorentzTransform) : 𝓢(Spacetime,ℂ) →L[ℂ] 𝓢(Spacetime,ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (spacetimeLorentzCLE L⁻¹)

@[simp] theorem spacetimeLorentzTest_apply (L : ProperLorentzTransform) (h : 𝓢(Spacetime,ℂ)) (x : Spacetime) :
    spacetimeLorentzTestCLM L h x=h (spacetimeLorentzCLE L⁻¹ x) := rfl

theorem fourier_spacetimeLorentzTest (L : ProperLorentzTransform)
    (h : 𝓢(Spacetime,ℂ)) (q : Spacetime) :
    𝓕 (spacetimeLorentzTestCLM L h) q=𝓕 h (spacetimeLorentzTranspose L q) := by
  change 𝓕 (spacetimeLorentzTestCLM L h : Spacetime → ℂ) q=
    𝓕 (h : Spacetime → ℂ) (spacetimeLorentzTranspose L q)
  rw [Real.fourier_eq,Real.fourier_eq]
  have hc:=(spacetimeLorentz_preserves_volume L).integral_comp
    (spacetimeLorentzCLE L).toHomeomorph.measurableEmbedding
    (fun x : Spacetime => Real.fourierChar (-inner ℝ x q) • h (spacetimeLorentzCLE L⁻¹ x))
  calc
    _=∫ x : Spacetime, Real.fourierChar (-inner ℝ (spacetimeLorentzCLE L x) q) • h x := by
      simpa only [spacetimeLorentzTest_apply,spacetimeLorentz_inverse] using hc.symm
    _=_ := by simp only [spacetimeLorentz_inner_transpose]

theorem spacetimeSmearing_lorentz (a : Parameters) (L : ProperLorentzTransform) (h : 𝓢(Spacetime,ℂ)) :
    spacetimeSmearingCLM a (spacetimeLorentzTestCLM L h)=
      lorentzSchwartzCLM a L (spacetimeSmearingCLM a h) := by
  ext p
  change 𝓕 (spacetimeLorentzTestCLM L h) (shellFrequency a p)=
    𝓕 h (shellFrequency a (lorentzShellMap a L⁻¹ p))
  rw [fourier_spacetimeLorentzTest,shellFrequency_lorentz_transpose]

end AASCKleinGordon
