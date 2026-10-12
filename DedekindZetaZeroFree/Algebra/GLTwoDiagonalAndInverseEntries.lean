module

public import DedekindZetaZeroFree.Metaplectic.Kubota.AdelicCover.AdelicRestrictedProductTopology

@[expose] public section

noncomputable section
open scoped Matrix
namespace DedekindZetaZeroFree.KPGlobalTorusMatrixCertificates
variable {R : Type*} [CommRing R]
abbrev GLTwo := Matrix.GeneralLinearGroup (Fin 2) R
lemma diagonal_units (A : GLTwo (R := R)) (h10 : A 1 0 = 0) :
    IsUnit (A 0 0) ∧ IsUnit (A 1 1) := by
  have h := (Matrix.GeneralLinearGroup.det A).isUnit
  have hh : IsUnit (A 0 0 * A 1 1) := by
    simpa [Matrix.GeneralLinearGroup.det, Matrix.det_fin_two, h10] using h
  exact IsUnit.mul_iff.mp hh
lemma inv10 (A : GLTwo (R := R)) (h10 : A 1 0 = 0) : A⁻¹ 1 0 = 0 := by
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 1 0) A.val_inv
  have hh : A 1 1 * A⁻¹ 1 0 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, h10] using h
  exact (diagonal_units A h10).2.mul_left_cancel (by simpa using hh)
lemma inv01 (A : GLTwo (R := R)) (h10 : A 1 0 = 0) (h01 : A 0 1 = 0) : A⁻¹ 0 1 = 0 := by
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 0 1) A.val_inv
  have hh : A 0 0 * A⁻¹ 0 1 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, h01] using h
  exact (diagonal_units A h10).1.mul_left_cancel (by simpa using hh)
end DedekindZetaZeroFree.KPGlobalTorusMatrixCertificates

end
