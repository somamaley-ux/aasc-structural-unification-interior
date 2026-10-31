import KGBosonicContractionIdentities

noncomputable section
open MeasureTheory
open scoped SchwartzMap
namespace AASCKleinGordon
open SchwartzOperations

theorem test_pair_integrable (a : Parameters) (f g : 𝓢(Momentum,ℂ)) :
    Integrable (fun p => star (f p) * g p) (wignerMeasure a) :=
  (SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) g.hasTemperateGrowth
    (postcomposeCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ) f)).integrable

theorem test_pair_integral_eq_inner (a : Parameters) (f g : 𝓢(Momentum,ℂ)) :
    (∫ p, star (f p) * g p ∂wignerMeasure a) =
      inner ℂ (oneParticleSchwartzToHilbert a f) (oneParticleSchwartzToHilbert a g) := by
  change _ = inner ℂ (f.toLp 2 (wignerMeasure a)) (g.toLp 2 (wignerMeasure a))
  simpa only [RCLike.inner_apply', RCLike.star_def] using
    (SchwartzMap.inner_toL2_toL2_eq f g (wignerMeasure a)).symm

theorem annihilation_creation_sector_apply (a : Parameters) (n : ℕ)
    (f g : 𝓢(Momentum,ℂ)) (H : bosonicSchwartz n) (y : ParticleConfiguration n) :
    (annihilationSectorCLM a n f (creationSectorCLM n g H)).val y =
      ∫ p, star (f p) * ∑ i : Fin (n+1),
        g (Fin.cons (α:=fun _ : Fin (n+1) => Momentum) p y i) *
          H.val (swapDelete n i (Fin.cons p y)) ∂wignerMeasure a := by
  rw [annihilationSectorCLM_apply]
  simp only [creationSectorCLM_apply, SchwartzMap.smul_apply, smul_eq_mul]
  simp_rw [symmetrizer_insert_apply]
  let c : ℂ := Real.sqrt (n+1)
  let d : ℂ := ((n+1 : ℕ) : ℂ)⁻¹
  let S (p : Momentum) := ∑ i : Fin (n+1),
    g (Fin.cons (α:=fun _ : Fin (n+1) => Momentum) p y i) * H.val (swapDelete n i (Fin.cons p y))
  change c * (∫ p, star (f p) * (c * (d * S p)) ∂wignerMeasure a) =
    ∫ p, star (f p) * S p ∂wignerMeasure a
  have he (p : Momentum) : star (f p) * (c * (d * S p)) =
      (c*d) * (star (f p) * S p) := by ring
  simp_rw [he]
  rw [integral_const_mul]
  calc
    _ = (c*c*d) * (∫ p, star (f p) * S p ∂wignerMeasure a) := by ring
    _ = _ := by rw [sqrt_particle_factor_cancel, one_mul]

theorem creation_annihilation_sector_apply (a : Parameters) (n : ℕ)
    (f g : 𝓢(Momentum,ℂ)) (H : bosonicSchwartz (n+1)) (y : ParticleConfiguration (n+1)) :
    (creationSectorCLM n g (annihilationSectorCLM a n f H)).val y =
      ∑ i : Fin (n+1), g (y i) *
        ∫ p, star (f p) * H.val (Fin.cons p (swapDelete n i y)) ∂wignerMeasure a := by
  rw [creationSectorCLM_apply]
  change (Real.sqrt (n+1) : ℂ) *
    schwartzSymmetrizer (n+1) (particleTensorInsertCLM n g
      (annihilationSectorCLM a n f H).val) y = _
  rw [symmetrizer_insert_apply]
  simp only [annihilationSectorCLM_apply]
  let c : ℂ := Real.sqrt (n+1)
  let d : ℂ := ((n+1 : ℕ) : ℂ)⁻¹
  let K (i : Fin (n+1)) := ∫ p, star (f p) * H.val (Fin.cons p (swapDelete n i y)) ∂wignerMeasure a
  change c * (d * ∑ i, g (y i) * (c * K i)) = ∑ i, g (y i) * K i
  have he : (∑ i, g (y i) * (c * K i)) = c * ∑ i, g (y i) * K i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he]
  calc
    _ = (c*c*d) * ∑ i, g (y i) * K i := by ring
    _ = _ := by rw [sqrt_particle_factor_cancel, one_mul]

theorem mixed_CCR_sector_succ (a : Parameters) (n : ℕ) (f g : 𝓢(Momentum,ℂ))
    (H : bosonicSchwartz (n+1)) :
    annihilationSectorCLM a (n+1) f (creationSectorCLM (n+1) g H) =
      (∫ p, star (f p) * g p ∂wignerMeasure a) • H +
        creationSectorCLM n g (annihilationSectorCLM a n f H) := by
  apply Subtype.ext
  ext y
  rw [annihilation_creation_sector_apply]
  have hsum (p : Momentum) : (∑ i : Fin (n+1+1),
      g (Fin.cons (α:=fun _ : Fin (n+1+1) => Momentum) p y i) *
        H.val (swapDelete (n+1) i (Fin.cons p y))) =
      g p * H.val y + ∑ i : Fin (n+1),
        g (y i) * H.val (Fin.cons p (swapDelete n i y)) := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, swapDelete_zero, bosonic_swapDelete_cons_succ]
  simp_rw [hsum]
  have hsplit (p : Momentum) :
      star (f p) * (g p * H.val y + ∑ i : Fin (n+1),
        g (y i) * H.val (Fin.cons p (swapDelete n i y))) =
      (star (f p) * g p) * H.val y + ∑ i : Fin (n+1),
        g (y i) * (star (f p) * H.val (Fin.cons p (swapDelete n i y))) := by
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro i hi
      ring
  simp_rw [hsplit]
  have hi (i : Fin (n+1)) : Integrable (fun p =>
      g (y i) * (star (f p) * H.val (Fin.cons p (swapDelete n i y)))) (wignerMeasure a) :=
    (contraction_kernel_integrable a n f H.val (swapDelete n i y)).const_mul _
  rw [integral_add ((test_pair_integrable a f g).mul_const (H.val y))
    (integrable_finset_sum _ fun i _ => hi i)]
  rw [integral_finset_sum _ fun i _ => hi i]
  simp_rw [integral_const_mul]
  rw [integral_mul_const]
  change _ = (∫ p, star (f p) * g p ∂wignerMeasure a) * H.val y +
    (creationSectorCLM n g (annihilationSectorCLM a n f H)).val y
  rw [creation_annihilation_sector_apply]

end AASCKleinGordon
