import KGSecondQuantizedWeylCovariance

noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap
namespace AASCKleinGordon
open SchwartzOperations

/-- Original test transform: h'(x)=h(L⁻¹(x-b)), preserving actual reality. -/
def realSpacetimePoincareTest (b : Spacetime) (L : ProperLorentzTransform)
    (h : realSpacetimeTestSpace) : realSpacetimeTestSpace :=
  ⟨spacetimeEventTranslationTestCLM b (spacetimeLorentzTestCLM L h.val),
    (mem_realSpacetimeTestSpace _).mpr (by
      rw [conjugate_spacetimeEventTranslationTest,conjugate_spacetimeLorentzTest,
        (mem_realSpacetimeTestSpace h.val).mp h.property])⟩

theorem realSpacetimePoincareTest_apply (b : Spacetime) (L : ProperLorentzTransform)
    (h : realSpacetimeTestSpace) (x : Spacetime) :
    (realSpacetimePoincareTest b L h).val x=h.val (spacetimeLorentzCLE L⁻¹ (x-b)) := rfl

theorem poincare_realFieldWeylLabel (a : Parameters) (b : Spacetime)
    (L : ProperLorentzTransform) (s : ℝ) (h : realSpacetimeTestSpace) :
    poincareSchwartzCLM a b L (realFieldWeylLabelCLM a s h)=
      realFieldWeylLabelCLM a s (realSpacetimePoincareTest b L h) := by
  change eventTranslationSchwartzCLM a b (lorentzSchwartzCLM a L
    ((Complex.I*(s : ℂ)) • spacetimeSmearingCLM a h.val))=
      (Complex.I*(s : ℂ)) • spacetimeSmearingCLM a
        (spacetimeEventTranslationTestCLM b (spacetimeLorentzTestCLM L h.val))
  rw [map_smul,map_smul,spacetimeSmearing_eventTranslation,spacetimeSmearing_lorentz]

theorem original_real_field_poincare_weyl_intertwine (a : Parameters) (b : Spacetime)
    (L : ProperLorentzTransform) (s t : ℝ) (h : realSpacetimeTestSpace) (v : FockHilbert a) :
    fockPoincareUnitary a b L (realFieldWeylGroup a s h t v)=
      realFieldWeylGroup a s (realSpacetimePoincareTest b L h) t
        (fockPoincareUnitary a b L v) := by
  change fockPoincareUnitary a b L
    (weylOperator a ((t : ℂ) • realFieldWeylLabelCLM a s h) v)=
      weylOperator a ((t : ℂ) • realFieldWeylLabelCLM a s (realSpacetimePoincareTest b L h))
        (fockPoincareUnitary a b L v)
  rw [fockPoincare_weyl_intertwine,map_smul,poincare_realFieldWeylLabel]

theorem original_real_field_poincare_weyl_conjugation (a : Parameters) (b : Spacetime)
    (L : ProperLorentzTransform) (s t : ℝ) (h : realSpacetimeTestSpace) (v : FockHilbert a) :
    fockPoincareUnitary a b L
      (realFieldWeylGroup a s h t ((fockPoincareUnitary a b L).symm v))=
        realFieldWeylGroup a s (realSpacetimePoincareTest b L h) t v := by
  rw [original_real_field_poincare_weyl_intertwine,LinearIsometryEquiv.apply_symm_apply]

end AASCKleinGordon
