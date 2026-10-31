import OriginalEHCompactActionDerivative

/-! The literal variation current of the independent original gravitational
action. Its ingredients are the actual inverse, volume and already computed
Levi-Civita variation. No response identity or divergence decomposition is input. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Filter TopologicalSpace Set
open scoped Topology ContDiff BigOperators Matrix.Norms.Elementwise

def ehBoundaryCurrent (g h : MetricField) (p : CoordinatePoint) (c : Fin 4) : ℝ :=
  coordinateVolumeDensity g p *
    ((∑ a : Fin 4, ∑ b : Fin 4, (g p)⁻¹ a b * ehLCVariation g h p c a b) -
      (∑ a : Fin 4, ∑ b : Fin 4, (g p)⁻¹ a c * ehLCVariation g h p b a b))

theorem eh_inverse_component_smooth_at (g : MetricField)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b)) (p : CoordinatePoint)
    (hn : (g p).det ≠ 0) (a b : Fin 4) :
    ContDiffAt ℝ ∞ (fun x => (g x)⁻¹ a b) p := by
  have hi := (eh_jet_inverse_entry_contDiffAt (ehActualMetricJet g p) hn a b).of_le
    (show (∞ : WithTop ℕ∞) ≤ ⊤ from le_top)
  exact hi.comp p (eh_actual_metric_jet_contDiff g hg).contDiffAt

theorem eh_inverse_variation_smooth_at (g h : MetricField)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (hh : ∀ a b, ContDiff ℝ ∞ (fun x => h x a b)) (p : CoordinatePoint)
    (hn : (g p).det ≠ 0) (a b : Fin 4) :
    ContDiffAt ℝ ∞ (fun x => ehInverseVariation g h x a b) p := by
  simp only [ehInverseVariation,Matrix.mul_apply,Matrix.neg_apply]
  apply ContDiffAt.sum
  intro j _
  apply ContDiffAt.mul
  · apply ContDiffAt.sum
    intro i _
    exact (eh_inverse_component_smooth_at g hg p hn a i).neg.mul (hh i j).contDiffAt
  · exact eh_inverse_component_smooth_at g hg p hn j b

theorem eh_lc_variation_smooth_at (g h : MetricField)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (hh : ∀ a b, ContDiff ℝ ∞ (fun x => h x a b)) (p : CoordinatePoint)
    (hn : (g p).det ≠ 0) (a b c : Fin 4) :
    ContDiffAt ℝ ∞ (fun x => ehLCVariation g h x a b c) p := by
  unfold ehLCVariation
  apply ContDiffAt.sum
  intro d _
  exact ((eh_inverse_variation_smooth_at g h hg hh p hn a d).mul
    (smooth_lower_christoffel g hg d b c).contDiffAt).add
    ((eh_inverse_component_smooth_at g hg p hn a d).mul
      (smooth_lower_christoffel h hh d b c).contDiffAt)

theorem eh_volume_density_smooth_at (g : MetricField)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b)) (p : CoordinatePoint)
    (negative : (g p).det < 0) : ContDiffAt ℝ ∞ (coordinateVolumeDensity g) p := by
  have det : ContDiff ℝ ∞ (fun x => (g x).det) :=
    (eh_jet_determinant_contDiff.of_le (show (∞ : WithTop ℕ∞) ≤ ⊤ from le_top)).comp
      (eh_actual_metric_jet_contDiff g hg)
  exact det.contDiffAt.neg.sqrt (neg_ne_zero.mpr (ne_of_lt negative))

theorem eh_boundary_current_smooth_at (g h : MetricField)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (hh : ∀ a b, ContDiff ℝ ∞ (fun x => h x a b)) (p : CoordinatePoint)
    (negative : (g p).det < 0) (c : Fin 4) :
    ContDiffAt ℝ ∞ (fun x => ehBoundaryCurrent g h x c) p := by
  unfold ehBoundaryCurrent
  apply (eh_volume_density_smooth_at g hg p negative).mul
  apply ContDiffAt.sub
  · apply ContDiffAt.sum
    intro a _
    apply ContDiffAt.sum
    intro b _
    exact (eh_inverse_component_smooth_at g hg p (ne_of_lt negative) a b).mul
      (eh_lc_variation_smooth_at g h hg hh p (ne_of_lt negative) c a b)
  · apply ContDiffAt.sum
    intro a _
    apply ContDiffAt.sum
    intro b _
    exact (eh_inverse_component_smooth_at g hg p (ne_of_lt negative) a c).mul
      (eh_lc_variation_smooth_at g h hg hh p (ne_of_lt negative) b a b)

theorem eh_lc_variation_zero_of_germ_zero (g h : MetricField) (p : CoordinatePoint)
    (zero : h =ᶠ[𝓝 p] 0) (a b c : Fin 4) : ehLCVariation g h p a b c = 0 := by
  have hv : h p = (0 : Tensor2) := Filter.EventuallyEq.eq_of_nhds zero
  have jets := metric_twojet_of_eventuallyEq h 0 p zero
  have hl (i j k : Fin 4) : lowerChristoffel h p i j k = 0 := by
    rw [lowerChristoffel_metric_twojet_congr h 0 p jets]
    simp [lowerChristoffel,metricPartial]
  have hi : ehInverseVariation g h p = 0 := by
    simp only [ehInverseVariation,hv,mul_zero,zero_mul]
  simp only [ehLCVariation,hi,hl,Matrix.zero_apply,zero_mul,mul_zero,add_zero,Finset.sum_const_zero]

variable {Ω : Opens CoordinatePoint}

theorem eh_boundary_current_zero_outside_support (g : MetricField) (h : MetricSourceProbe Ω)
    (p : CoordinatePoint) (hp : p ∉ tsupport h) (c : Fin 4) :
    ehBoundaryCurrent g (ehProbeMetric h) p c = 0 := by
  have hz := eh_probe_metric_zero_near_outside_support h p hp
  simp only [ehBoundaryCurrent,eh_lc_variation_zero_of_germ_zero g (ehProbeMetric h) p hz,
    mul_zero,Finset.sum_const_zero,sub_self]

theorem eh_boundary_current_zero_near_outside_support (g : MetricField) (h : MetricSourceProbe Ω)
    (p : CoordinatePoint) (hp : p ∉ tsupport h) (c : Fin 4) :
    (fun x => ehBoundaryCurrent g (ehProbeMetric h) x c) =ᶠ[𝓝 p] 0 := by
  have near : ∀ᶠ x in 𝓝 p, x ∉ tsupport h :=
    (isClosed_tsupport h).isOpen_compl.mem_nhds hp
  filter_upwards [near] with x hx
  exact eh_boundary_current_zero_outside_support g h x hx c

theorem eh_boundary_current_tsupport_subset (g : MetricField) (h : MetricSourceProbe Ω) (c : Fin 4) :
    tsupport (fun p => ehBoundaryCurrent g (ehProbeMetric h) p c) ⊆ tsupport h := by
  apply closure_minimal
  · intro p hp
    by_contra hn
    exact hp (eh_boundary_current_zero_outside_support g h p hn c)
  · exact isClosed_tsupport h

theorem eh_boundary_current_compact_support (g : MetricField) (h : MetricSourceProbe Ω) (c : Fin 4) :
    HasCompactSupport (fun p => ehBoundaryCurrent g (ehProbeMetric h) p c) :=
  h.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _)
    (eh_boundary_current_tsupport_subset g h c)

/-- The current is smooth globally even if g degenerates outside Omega:
the actual compact operand makes the current identically zero near such points. -/
theorem eh_probe_boundary_current_smooth (g : MetricField)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (negative : ∀ p ∈ Ω, (g p).det < 0) (h : MetricSourceProbe Ω) (c : Fin 4) :
    ContDiff ℝ ∞ (fun p => ehBoundaryCurrent g (ehProbeMetric h) p c) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : p ∈ Ω
  · exact eh_boundary_current_smooth_at g (ehProbeMetric h) hg (eh_probe_metric_smooth h)
      p (negative p hp) c
  · have outside : p ∉ tsupport h := fun hs => hp (h.tsupport_subset hs)
    exact contDiffAt_const.congr_of_eventuallyEq
      (eh_boundary_current_zero_near_outside_support g h p outside c)

def ehBoundaryCurrentTest (g : MetricField)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (negative : ∀ p ∈ Ω, (g p).det < 0) (h : MetricSourceProbe Ω) (c : Fin 4) :
    ScalarSourceProbe Ω where
  toFun := fun p => ehBoundaryCurrent g (ehProbeMetric h) p c
  contDiff' := eh_probe_boundary_current_smooth g hg negative h c
  hasCompactSupport' := eh_boundary_current_compact_support g h c
  tsupport_subset' := (eh_boundary_current_tsupport_subset g h c).trans h.tsupport_subset

end
end AASCSemanticExhaustion
