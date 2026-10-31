import WickSchwartzSeminormBounds
import Mathlib.Analysis.Normed.Lp.lpSpace

noncomputable section
set_option maxHeartbeats 8000000
open scoped SchwartzMap NNReal BoundedContinuousFunction
namespace AASCKleinGordon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev WickJetTarget (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (m : ℕ) :=
  E →ᵇ (E [×m]→L[ℝ] ℂ)

/-- Actual weighted derivative jet, independent of every stress/source response. -/
def wickSchwartzJet (k m : ℕ) (f : 𝓢(E,ℂ)) : WickJetTarget E m :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => ‖x‖^k • iteratedFDeriv ℝ m f x)
    ((continuous_norm.pow k).smul ((f.smooth ⊤).continuous_iteratedFDeriv (by exact_mod_cast le_top)))
    (SchwartzMap.seminorm ℂ k m f)
    (fun x => by simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
      using SchwartzMap.le_seminorm ℂ k m f x)

lemma wick_schwartz_jet_apply (k m : ℕ) (f : 𝓢(E,ℂ)) (x : E) :
    wickSchwartzJet k m f x=‖x‖^k • iteratedFDeriv ℝ m f x := rfl

lemma wick_schwartz_jet_norm (k m : ℕ) (f : 𝓢(E,ℂ)) :
    ‖wickSchwartzJet k m f‖=SchwartzMap.seminorm ℂ k m f := by
  apply le_antisymm
  · apply (BoundedContinuousFunction.norm_le (apply_nonneg _ _)).mpr
    intro x
    simpa only [wick_schwartz_jet_apply,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (norm_nonneg _) _)] using SchwartzMap.le_seminorm ℂ k m f x
  · refine SchwartzMap.seminorm_le_bound ℂ k m f (M:=‖wickSchwartzJet k m f‖) (norm_nonneg (wickSchwartzJet k m f)) ?_
    intro x
    simpa only [wick_schwartz_jet_apply,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (norm_nonneg _) _)] using
        (wickSchwartzJet k m f).norm_coe_le_norm x

def wickSchwartzJetCLM (k m : ℕ) : 𝓢(E,ℂ) →L[ℂ] WickJetTarget E m :=
  SchwartzMap.mkCLMtoNormedSpace (σ:=RingHom.id ℂ) (wickSchwartzJet (E:=E) k m)
    (by
      intro f g
      apply BoundedContinuousFunction.ext
      intro x
      change ‖x‖^k • iteratedFDeriv ℝ m (f+g) x=
        ‖x‖^k • iteratedFDeriv ℝ m f x+‖x‖^k • iteratedFDeriv ℝ m g x
      have hcoe : (⇑(f+g) : E → ℂ)=⇑f+⇑g := by
        funext y
        simp only [SchwartzMap.add_apply,Pi.add_apply]
      rw [hcoe,iteratedFDeriv_add_apply (f.smooth _).contDiffAt (g.smooth _).contDiffAt]
      exact smul_add _ _ _)
    (by
      intro c f
      apply BoundedContinuousFunction.ext
      intro x
      change ‖x‖^k • iteratedFDeriv ℝ m (c • f) x= c • (‖x‖^k • iteratedFDeriv ℝ m f x)
      have hcoe : (⇑(c • f) : E → ℂ)=c • ⇑f := by
        funext y
        simp only [SchwartzMap.smul_apply,Pi.smul_apply]
      rw [hcoe,iteratedFDeriv_const_smul_apply (f.smooth _).contDiffAt]
      exact smul_comm _ _ _)
    ⟨{(k,m)},1,zero_le_one,by
      intro f
      rw [wick_schwartz_jet_norm]
      simp only [Finset.sup_singleton,one_mul]
      rfl⟩

lemma wick_schwartz_jet_CLM_apply (k m : ℕ) (f : 𝓢(E,ℂ)) :
    wickSchwartzJetCLM k m f=wickSchwartzJet k m f := rfl

end AASCKleinGordon
