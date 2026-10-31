import LocalSecondJetCalculus

namespace AASCSemanticExhaustion
noncomputable section
set_option maxHeartbeats 0

/-- The full actual second chain rule, with the first-derivative correction
retained. Both functions need only be smooth at their relevant points. -/
theorem local_scalarSecondPartial_comp (f : CoordinatePoint → ℝ)
    (F : CoordinatePoint → CoordinatePoint) (p : CoordinatePoint)
    (hf : ContDiffAt ℝ ⊤ f (F p)) (hF : ContDiffAt ℝ ⊤ F p) (c d : Fin 4) :
    scalarSecondPartial (fun x => f (F x)) p c d =
      fderiv ℝ f (F p) (fderiv ℝ (fderiv ℝ F) p (Pi.single d 1) (Pi.single c 1)) +
        fderiv ℝ (fderiv ℝ f) (F p)
          (fderiv ℝ F p (Pi.single d 1)) (fderiv ℝ F p (Pi.single c 1)) := by
  have hs : ∀ᶠ x in nhds p,
      scalarPartial (fun y => f (F y)) x c =
        fderiv ℝ f (F x) (fderiv ℝ F x (Pi.single c 1)) := by
    have hsF := (hF.of_le (show (2 : WithTop ℕ∞) ≤ ⊤ by simp)).eventually (by simp)
    have hsf := ((hf.of_le (show (2 : WithTop ℕ∞) ≤ ⊤ by simp)).eventually
      (by simp)).filter_mono hF.continuousAt
    filter_upwards [hsF, hsf] with x hx hx'
    change ContDiffAt ℝ 2 f (F x) at hx'
    have hd := fderiv_comp x (hx'.differentiableAt (by norm_num))
      (hx.differentiableAt (by norm_num))
    change fderiv ℝ (fun y => f (F y)) x = _ at hd
    simp only [scalarPartial, hd, ContinuousLinearMap.comp_apply]
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) (F p) :=
    (hf.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  have hdF : DifferentiableAt ℝ (fderiv ℝ F) p :=
    (hF.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  have hA := hdf.comp p (hF.differentiableAt (by simp))
  change DifferentiableAt ℝ (fun x => fderiv ℝ f (F x)) p at hA
  have hB := hdF.clm_apply (differentiableAt_const (Pi.single c (1 : ℝ)))
  change fderiv ℝ (fun x => scalarPartial (fun y => f (F y)) x c) p (Pi.single d 1) = _
  rw [Filter.EventuallyEq.fderiv_eq hs]
  rw [fderiv_clm_apply hA hB]
  have houter := fderiv_comp p hdf (hF.differentiableAt (by simp))
  change fderiv ℝ (fun x => fderiv ℝ f (F x)) p = _ at houter
  rw [houter, fderiv_clm_apply hdF (differentiableAt_const (Pi.single c (1 : ℝ)))]
  simp

theorem local_scalarSecondPartial_comp_flat_identity (f : CoordinatePoint → ℝ)
    (F : CoordinatePoint → CoordinatePoint)
    (hf : ContDiffAt ℝ ⊤ f 0) (hF : ContDiffAt ℝ ⊤ F 0)
    (Fzero : F 0 = 0) (DFzero : fderiv ℝ F 0 = ContinuousLinearMap.id ℝ CoordinatePoint)
    (first : fderiv ℝ f 0 = 0) (c d : Fin 4) :
    scalarSecondPartial (fun x => f (F x)) 0 c d = scalarSecondPartial f 0 c d := by
  have hs : ContDiffAt ℝ ⊤ f (F 0) := by simpa only [Fzero] using hf
  rw [local_scalarSecondPartial_comp f F 0 hs hF, Fzero, first, DFzero]
  simp only [ContinuousLinearMap.zero_apply, zero_add, ContinuousLinearMap.id_apply]
  exact (scalarSecondPartial_full_second_derivative f 0 hf c d).symm

theorem local_scalarFirstJet_comp_zero (f : CoordinatePoint → ℝ)
    (F : CoordinatePoint → CoordinatePoint)
    (hf : ContDiffAt ℝ ⊤ f 0) (hF : ContDiffAt ℝ ⊤ F 0)
    (Fzero : F 0 = 0) (first : fderiv ℝ f 0 = 0) :
    fderiv ℝ (fun x => f (F x)) 0 = 0 := by
  have hs : DifferentiableAt ℝ f (F 0) := by
    simpa only [Fzero] using hf.differentiableAt (by simp)
  have hd := fderiv_comp 0 hs (hF.differentiableAt (by simp))
  change fderiv ℝ (fun x => f (F x)) 0 = _ at hd
  simpa only [Fzero, first, ContinuousLinearMap.zero_comp] using hd

theorem local_scalarSecondPartial_triple_flat (f h k : CoordinatePoint → ℝ)
    (hf : ContDiffAt ℝ ⊤ f 0) (hh : ContDiffAt ℝ ⊤ h 0) (hk : ContDiffAt ℝ ⊤ k 0)
    (firstf : fderiv ℝ f 0 = 0) (firsth : fderiv ℝ h 0 = 0)
    (firstk : fderiv ℝ k 0 = 0) (c d : Fin 4) :
    scalarSecondPartial (fun x => f x * h x * k x) 0 c d =
      f 0 * h 0 * scalarSecondPartial k 0 c d +
        f 0 * k 0 * scalarSecondPartial h 0 c d +
          h 0 * k 0 * scalarSecondPartial f 0 c d := by
  have hd := ((hf.differentiableAt (by simp)).hasFDerivAt.mul
    (hh.differentiableAt (by simp)).hasFDerivAt).fderiv
  change fderiv ℝ (fun x => f x * h x) 0 = _ at hd
  simp only [firstf, firsth, smul_zero, add_zero] at hd
  rw [local_scalarSecondPartial_mul (fun x => f x * h x) k 0 (hf.mul hh) hk,
    local_scalarSecondPartial_mul f h 0 hf hh]
  simp only [scalarPartial, firstf, firsth, firstk, hd,
    ContinuousLinearMap.zero_apply, mul_zero, zero_mul, add_zero]
  ring

#print axioms local_scalarSecondPartial_comp
#print axioms local_scalarSecondPartial_comp_flat_identity
#print axioms local_scalarFirstJet_comp_zero
#print axioms local_scalarSecondPartial_triple_flat
end
end AASCSemanticExhaustion
