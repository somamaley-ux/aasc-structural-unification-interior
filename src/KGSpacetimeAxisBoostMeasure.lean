import KGSpacetimeAxisBoost

noncomputable section
set_option maxHeartbeats 600000
open MeasureTheory
open scoped FourierTransform
namespace AASCKleinGordon

theorem axisBoostFour_det (r : ℝ) : LinearMap.det (axisBoostFourCLE r).toLinearMap=1 := by
  have hm : LinearMap.toMatrix' (axisBoostFourCLE r).toLinearMap=
      !![Real.cosh r,Real.sinh r,0,0;
         Real.sinh r,Real.cosh r,0,0;
         0,0,1,0;
         0,0,0,1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix'_apply,axisBoostFourCLE,axisBoostFour]
  rw [← LinearMap.det_toMatrix',hm,Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ,Matrix.det_fin_three]
  have hi : (1 : Fin 4).succAbove (2 : Fin 3)=(3 : Fin 4) := by decide
  have hv : (![0,0,0,1] : Fin 4 → ℝ) 3=1 := rfl
  rw [hi,hv,mul_one]
  nlinarith [Real.cosh_sq_sub_sinh_sq r]

theorem spacetimeAxisBoost_det (r : ℝ) : LinearMap.det (spacetimeAxisBoostCLE r).toLinearMap=1 := by
  have h := LinearMap.det_conj (axisBoostFourCLE r).toLinearMap
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm.toLinearEquiv
  change LinearMap.det (spacetimeAxisBoostCLE r).toLinearMap=
    LinearMap.det (axisBoostFourCLE r).toLinearMap at h
  rw [h,axisBoostFour_det]

theorem spacetimeAxisBoost_preserves_volume (r : ℝ) :
    MeasurePreserving (spacetimeAxisBoostCLE r) := by
  refine ⟨(spacetimeAxisBoostCLE r).continuous.measurable,?_⟩
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure Spacetime)
    (f := (spacetimeAxisBoostCLE r).toLinearMap) (by rw [spacetimeAxisBoost_det]; norm_num)
  simpa only [spacetimeAxisBoost_det,inv_one,abs_one,ENNReal.ofReal_one,one_smul] using h

theorem fourier_spacetimeAxisBoostTest (r : ℝ) (h : SchwartzMap Spacetime ℂ) (q : Spacetime) :
    𝓕 (spacetimeAxisBoostTestCLM r h) q=𝓕 h (spacetimeAxisBoostCLE r q) := by
  change 𝓕 (spacetimeAxisBoostTestCLM r h : Spacetime → ℂ) q=
    𝓕 (h : Spacetime → ℂ) (spacetimeAxisBoostCLE r q)
  rw [Real.fourier_eq,Real.fourier_eq]
  have hc := (spacetimeAxisBoost_preserves_volume r).integral_comp
    (spacetimeAxisBoostCLE r).toHomeomorph.measurableEmbedding
    (fun x : Spacetime => Real.fourierChar (-inner ℝ x q) • h (spacetimeAxisBoostCLE (-r) x))
  calc
    _ = ∫ x : Spacetime, Real.fourierChar (-inner ℝ (spacetimeAxisBoostCLE r x) q) • h x := by
      simpa only [spacetimeAxisBoostTestCLM_apply,spacetimeAxisBoost_neg_inverse] using hc.symm
    _ = _ := by simp only [spacetimeAxisBoost_transpose]

end AASCKleinGordon
