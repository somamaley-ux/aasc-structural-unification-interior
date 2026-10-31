import KGL2ProductVectors
import Mathlib.Analysis.Normed.Module.Multilinear.Basic

noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Filter
namespace AASCKleinGordon

theorem particleProductFunction_update (a : Parameters) (n : ℕ)
    (f : Fin n → OneParticleHilbert a) (i : Fin n) (h : OneParticleHilbert a)
    (x : ParticleConfiguration n) :
    particleProductFunction a n (Function.update f i h) x=
      h (x i)*∏ j∈Finset.univ.erase i,f j (x j) := by
  classical
  have he : (fun j => Function.update f i h j (x j))=
      Function.update (fun j => f j (x j)) i (h (x i)) := by
    funext j
    by_cases hj : j=i
    · subst j; simp
    · simp [Function.update_of_ne hj,hj]
  unfold particleProductFunction
  rw [he,Finset.prod_update_of_mem (Finset.mem_univ i)]
  rw [Finset.sdiff_singleton_eq_erase]

theorem particleL2Product_update_add (a : Parameters) (n : ℕ)
    (f : Fin n → OneParticleHilbert a) (i : Fin n) (u v : OneParticleHilbert a) :
    particleL2Product a n (Function.update f i (u+v))=
      particleL2Product a n (Function.update f i u)+particleL2Product a n (Function.update f i v) := by
  apply Lp.ext
  have hf:=(Measure.quasiMeasurePreserving_eval (μ:=fun _ : Fin n => wignerMeasure a) i).ae
    (Lp.coeFn_add u v)
  filter_upwards [particleL2Product_ae a n (Function.update f i (u+v)),
    particleL2Product_ae a n (Function.update f i u),particleL2Product_ae a n (Function.update f i v),
    Lp.coeFn_add (particleL2Product a n (Function.update f i u))
      (particleL2Product a n (Function.update f i v)),hf] with x ha hb hc hd he
  rw [ha,hd]
  simp only [Pi.add_apply,hb,hc,particleProductFunction_update]
  change (u+v) (x i)=u (x i)+v (x i) at he
  rw [he,add_mul]

theorem particleL2Product_update_smul (a : Parameters) (n : ℕ)
    (f : Fin n → OneParticleHilbert a) (i : Fin n) (z : ℂ) (u : OneParticleHilbert a) :
    particleL2Product a n (Function.update f i (z • u))=
      z • particleL2Product a n (Function.update f i u) := by
  apply Lp.ext
  have hf:=(Measure.quasiMeasurePreserving_eval (μ:=fun _ : Fin n => wignerMeasure a) i).ae
    (Lp.coeFn_smul z u)
  filter_upwards [particleL2Product_ae a n (Function.update f i (z • u)),
    particleL2Product_ae a n (Function.update f i u),
    Lp.coeFn_smul z (particleL2Product a n (Function.update f i u)),hf] with x ha hb hc hd
  rw [ha,hc]
  simp only [Pi.smul_apply,smul_eq_mul,hb,particleProductFunction_update]
  change (z • u) (x i)=z*u (x i) at hd
  rw [hd,mul_assoc]

def particleL2ProductMultilinear (a : Parameters) (n : ℕ) :
    MultilinearMap ℂ (fun _ : Fin n => OneParticleHilbert a) (ParticleHilbert a n) where
  toFun:=particleL2Product a n
  map_update_add' := by
    intro _ f i u v
    convert particleL2Product_update_add a n f i u v
  map_update_smul' := by
    intro _ f i z u
    convert particleL2Product_update_smul a n f i z u

/-- The actual product map is continuous on the original one-particle Hilbert
space in every slot, with the sharp product norm bound. -/
def particleL2ProductCMLM (a : Parameters) (n : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => OneParticleHilbert a) (ParticleHilbert a n) :=
  (particleL2ProductMultilinear a n).mkContinuous 1 (fun f => by
    change ‖particleL2Product a n f‖≤1*∏ i,‖f i‖
    rw [particleL2Product_norm,one_mul])

@[simp] theorem particleL2ProductCMLM_apply (a : Parameters) (n : ℕ)
    (f : Fin n → OneParticleHilbert a) : particleL2ProductCMLM a n f=particleL2Product a n f := rfl

end AASCKleinGordon
