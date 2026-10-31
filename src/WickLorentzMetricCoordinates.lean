import WickPoincarePairTransport

noncomputable section
set_option maxHeartbeats 1500000
open scoped BigOperators
open AASCSemanticExhaustion
namespace AASCKleinGordon

def wickLorentzMatrix (L : ProperLorentzTransform) : NativeRealMatrix :=
  LinearMap.toMatrix' L.val.toLinearMap

theorem wick_lorentz_matrix_apply (L : ProperLorentzTransform) (i j : Fin 4) :
    wickLorentzMatrix L i j=spacetimeLorentzCLE L (spacetimeCoordinateVector j) i := rfl

theorem wick_lorentz_matrix_det (L : ProperLorentzTransform) : (wickLorentzMatrix L).det=1 := by
  rw [wickLorentzMatrix, LinearMap.det_toMatrix', properLorentz_det]

theorem wick_flat_metric_basis (i j : Fin 4) :
    wickFlatMetric i j=minkowskiDot (Pi.single i 1) (Pi.single j 1) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [wickFlatMetric, nativeClockNormalMetric, Matrix.diagonal_apply, minkowskiDot,
      Pi.single_apply] <;> (try simp only [Fin.ext_iff]) <;> norm_num

theorem wick_lorentz_flat_metric (L : ProperLorentzTransform) :
    (wickLorentzMatrix L).transpose*wickFlatMetric*wickLorentzMatrix L=wickFlatMetric := by
  ext i j
  calc
    _=minkowskiDot (L.val (Pi.single i 1)) (L.val (Pi.single j 1)) := by
      norm_num [Matrix.mul_apply, Matrix.transpose_apply, wickFlatMetric,
        nativeClockNormalMetric, Matrix.diagonal_apply, Fin.sum_univ_four, minkowskiDot,
        wickLorentzMatrix, LinearMap.toMatrix'_apply] <;>
        (try simp only [Fin.ext_iff]) <;> norm_num
    _=minkowskiDot (Pi.single i 1) (Pi.single j 1) := properLorentz_metric L _ _
    _=wickFlatMetric i j := (wick_flat_metric_basis i j).symm

end AASCKleinGordon
