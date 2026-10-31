import C2MetricNormalChart

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0

/-- Local second derivative rules. No global regularity is required. -/
theorem c2_local_scalarSecondPartial_sum {ι : Type*} [Fintype ι]
    (f : ι → CoordinatePoint → ℝ) (p : CoordinatePoint)
    (smooth : ∀ i, ContDiffAt ℝ 2 (f i) p) (c d : Fin 4) :
    scalarSecondPartial (fun x => ∑ i, f i x) p c d =
      ∑ i, scalarSecondPartial (f i) p c d := by
  rw [c2_scalarSecondPartial_full_second_derivative _ p
    (ContDiffAt.sum (fun i _ => smooth i))]
  have hd : ∀ᶠ x in nhds p,
      fderiv ℝ (fun y => ∑ i, f i y) x = ∑ i, fderiv ℝ (f i) x := by
    have hs : ∀ᶠ x in nhds p, ∀ i, DifferentiableAt ℝ (f i) x := by
      apply Filter.eventually_all.mpr
      intro i
      exact ((smooth i).of_le (show (2 : WithTop ℕ∞) ≤ 2 by simp)).eventually
        (by simp) |>.mono (fun x h => h.differentiableAt (by norm_num))
    filter_upwards [hs] with x hx
    exact (HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hx i).hasFDerivAt)).fderiv
  rw [Filter.EventuallyEq.fderiv_eq hd]
  have hsum := (HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    ((smooth i).fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp) |>.hasFDerivAt)).fderiv
  rw [hsum]
  simp only [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact (c2_scalarSecondPartial_full_second_derivative (f i) p (smooth i) c d).symm

theorem c2_local_scalarSecondPartial_const_mul (r : ℝ) (f : CoordinatePoint → ℝ)
    (p : CoordinatePoint) (smooth : ContDiffAt ℝ 2 f p) (c d : Fin 4) :
    scalarSecondPartial (fun x => r * f x) p c d = r * scalarSecondPartial f p c d := by
  rw [c2_scalarSecondPartial_full_second_derivative _ p (contDiffAt_const.mul smooth)]
  have hd : ∀ᶠ x in nhds p,
      fderiv ℝ (fun y => r * f y) x = r • fderiv ℝ f x := by
    have hs := (smooth.of_le (show (2 : WithTop ℕ∞) ≤ 2 by simp)).eventually (by simp)
    filter_upwards [hs] with x hx
    exact ((hx.differentiableAt (by norm_num)).hasFDerivAt.const_mul r).fderiv
  rw [Filter.EventuallyEq.fderiv_eq hd]
  have hsmul := ((((smooth.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by simp)).hasFDerivAt).const_smul r).fderiv
  change fderiv ℝ (fun x => r • fderiv ℝ f x) p = _ at hsmul
  rw [hsmul]
  rw [c2_scalarSecondPartial_full_second_derivative f p smooth]
  simp

theorem c2_local_linear_composition_second (f : CoordinatePoint → ℝ)
    (A : CoordinatePoint →L[ℝ] CoordinatePoint) (p : CoordinatePoint)
    (smooth : ContDiffAt ℝ 2 f (A p)) (c d : Fin 4) :
    scalarSecondPartial (fun x => f (A x)) p c d =
      fderiv ℝ (fderiv ℝ f) (A p) (A (Pi.single d 1)) (A (Pi.single c 1)) := by
  have hcomp := smooth.comp p (A.contDiff.contDiffAt.of_le (show (2 : WithTop ℕ∞) ≤ ⊤ by simp))
  change ContDiffAt ℝ 2 (fun x => f (A x)) p at hcomp
  rw [c2_scalarSecondPartial_full_second_derivative _ p hcomp]
  have hd : ∀ᶠ x in nhds p,
      fderiv ℝ (fun y => f (A y)) x = (fderiv ℝ f (A x)).comp A := by
    have hs := ((smooth.of_le (show (2 : WithTop ℕ∞) ≤ 2 by simp)).eventually
      (by simp)).filter_mono A.continuous.continuousAt
    filter_upwards [hs] with x hx
    change ContDiffAt ℝ 2 f (A x) at hx
    simpa only [Function.comp_def, A.hasFDerivAt.fderiv] using
      fderiv_comp x (hx.differentiableAt (by norm_num)) A.differentiableAt
  rw [Filter.EventuallyEq.fderiv_eq hd]
  have hdf := (smooth.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have hdc := hdf.hasFDerivAt.comp p A.hasFDerivAt
  have h := (ContinuousLinearMap.compL ℝ CoordinatePoint CoordinatePoint ℝ).flip A
    |>.hasFDerivAt.comp p hdc
  change HasFDerivAt (fun x => (fderiv ℝ f (A x)).comp A) _ p at h
  rw [h.fderiv]
  rfl

theorem c2_local_linear_composition_second_coordinates (f : CoordinatePoint → ℝ)
    (A : CoordinatePoint →L[ℝ] CoordinatePoint) (p : CoordinatePoint)
    (smooth : ContDiffAt ℝ 2 f (A p)) (c d : Fin 4) :
    scalarSecondPartial (fun x => f (A x)) p c d =
      ∑ u : Fin 4, ∑ v : Fin 4, scalarSecondPartial f (A p) u v *
        A (Pi.single c 1) u * A (Pi.single d 1) v := by
  rw [c2_local_linear_composition_second f A p smooth]
  rw [continuousBilinear_four_coordinates]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  rw [c2_scalarSecondPartial_full_second_derivative f (A p) smooth u v]
  ring

theorem c2_local_scalarPartial_differentiableAt (f : CoordinatePoint → ℝ)
    (p : CoordinatePoint) (smooth : ContDiffAt ℝ 2 f p) (c : Fin 4) :
    DifferentiableAt ℝ (fun x => scalarPartial f x c) p := by
  exact ((smooth.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by simp)).clm_apply (differentiableAt_const (Pi.single c 1))

theorem c2_local_scalarSecondPartial_mul (f h : CoordinatePoint → ℝ) (p : CoordinatePoint)
    (hf : ContDiffAt ℝ 2 f p) (hh : ContDiffAt ℝ 2 h p) (c d : Fin 4) :
    scalarSecondPartial (fun x => f x * h x) p c d =
      f p * scalarSecondPartial h p c d + h p * scalarSecondPartial f p c d +
        scalarPartial f p c * scalarPartial h p d +
          scalarPartial h p c * scalarPartial f p d := by
  have hs : ∀ᶠ x in nhds p,
      scalarPartial (fun y => f y * h y) x c =
        f x * scalarPartial h x c + h x * scalarPartial f x c := by
    have hf' := (hf.of_le (show (2 : WithTop ℕ∞) ≤ 2 by simp)).eventually (by simp)
    have hh' := (hh.of_le (show (2 : WithTop ℕ∞) ≤ 2 by simp)).eventually (by simp)
    filter_upwards [hf', hh'] with x hfx hhx
    unfold scalarPartial
    have hd := ((hfx.differentiableAt (by norm_num)).hasFDerivAt.mul
      (hhx.differentiableAt (by norm_num)).hasFDerivAt).fderiv
    change fderiv ℝ (fun y => f y * h y) x = _ at hd
    rw [hd]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hdf := c2_local_scalarPartial_differentiableAt f p hf c
  have hdh := c2_local_scalarPartial_differentiableAt h p hh c
  change fderiv ℝ (fun x => scalarPartial (fun y => f y * h y) x c) p (Pi.single d 1) = _
  rw [Filter.EventuallyEq.fderiv_eq hs]
  have hd := (((hf.differentiableAt (by simp)).hasFDerivAt.mul hdh.hasFDerivAt).add
    ((hh.differentiableAt (by simp)).hasFDerivAt.mul hdf.hasFDerivAt)).fderiv
  change fderiv ℝ (fun x => f x * scalarPartial h x c + h x * scalarPartial f x c) p = _ at hd
  rw [hd]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  change f p * scalarSecondPartial h p c d + scalarPartial h p c * scalarPartial f p d +
    (h p * scalarSecondPartial f p c d + scalarPartial f p c * scalarPartial h p d) = _
  ring

#print axioms c2_local_scalarSecondPartial_sum
#print axioms c2_local_scalarSecondPartial_const_mul
#print axioms c2_local_linear_composition_second
#print axioms c2_local_linear_composition_second_coordinates
#print axioms c2_local_scalarPartial_differentiableAt
#print axioms c2_local_scalarSecondPartial_mul
end
end AASCSemanticExhaustion
