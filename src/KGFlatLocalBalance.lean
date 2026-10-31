import KGLocalizedEnergyIntegration
import Mathlib.Analysis.Calculus.FDeriv.Mul

noncomputable section
set_option maxHeartbeats 800000
namespace AASCKleinGordon

/-- Product rule for the actual KG flux, in the same Euclidean coordinate directions
used in the cutoff integration-by-parts theorem. -/
theorem flatKGFlux_divergence
    (v : KGSpatialSpace → ℝ) (w : KGSpatialSpace → KGSpatialSpace)
    (hv : Differentiable ℝ v)
    (hw : ∀ i : Fin 3, Differentiable ℝ (fun x => w x i))
    (x : KGSpatialSpace) (g : KGSpatialSpace)
    (hg : ∀ i : Fin 3, fderiv ℝ v x (kgSpatialDirection i)=g i) :
    kgSpatialDivergence (fun y => flatKGFlux (v y) (w y)) x =
      v x*kgSpatialDivergence w x+inner ℝ (w x) g := by
  have hi (i : Fin 3) :
      fderiv ℝ (fun y => flatKGFlux (v y) (w y) i) x (kgSpatialDirection i) =
        v x*fderiv ℝ (fun y => w y i) x (kgSpatialDirection i)+w x i*g i := by
    change fderiv ℝ (v*(fun y => w y i)) x (kgSpatialDirection i)=_
    rw [((hv x).hasFDerivAt.mul ((hw i x).hasFDerivAt)).fderiv]
    simp [hg]
  unfold kgSpatialDivergence
  simp_rw [hi]
  rw [Finset.sum_add_distrib,← Finset.mul_sum,spatial_inner_eq_sum]

/-- The local conservation identity is derived from the explicit first-order KG
equations and spatial product rule, rather than postulated as a conservation bridge. -/
theorem flatKG_local_energy_balance
    (μ : ℝ) (u v : ℝ → KGSpatialSpace → ℝ)
    (w : ℝ → KGSpatialSpace → KGSpatialSpace)
    (t : ℝ) (x g : KGSpatialSpace)
    (hvx : Differentiable ℝ (v t))
    (hwx : ∀ i : Fin 3, Differentiable ℝ (fun y => w t y i))
    (hg : ∀ i : Fin 3, fderiv ℝ (v t) x (kgSpatialDirection i)=g i)
    (hu : HasDerivAt (fun s => u s x) (v t x) t)
    (hv : HasDerivAt (fun s => v s x) (kgSpatialDivergence (w t) x-μ^2*u t x) t)
    (hw : HasDerivAt (fun s => w s x) g t) :
    HasDerivAt (fun s => flatKGEnergy μ (u s x) (v s x) (w s x))
      (kgSpatialDivergence (fun y => flatKGFlux (v t y) (w t y)) x) t := by
  rw [flatKGFlux_divergence (v t) (w t) hvx hwx x g hg]
  exact flatKGEnergy_hasDerivAt μ (fun s => u s x) (fun s => v s x)
    (fun s => w s x) t (kgSpatialDivergence (w t) x) g hu hv hw

end AASCKleinGordon
