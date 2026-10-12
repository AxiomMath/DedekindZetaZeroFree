module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.RationalCompositionScalarData

@[expose] public section

namespace DedekindZetaZeroFree.KPRankOneReversePairGeneric.GraphTwist
noncomputable section
open KubotaRankTwo Matrix
variable {K : Type*} [Field K]
lemma diagonal_injective (a b : Kˣ)
    (h : ProjGenLinGroup.mk (d K a 1) = ProjGenLinGroup.mk (d K b 1)) : a = b := by
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h
  have h1 := congrArg (fun g : GL2 K => (g : Matrix (Fin 2) (Fin 2) K) 1 1) hu
  have h0 := congrArg (fun g : GL2 K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) hu
  simp [d, GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_succ] at h1 h0
  exact Units.ext (by simpa [h1] using h0)

lemma weyl_diagonal (a : Kˣ) :
    ProjGenLinGroup.mk (w K)⁻¹ * ProjGenLinGroup.mk (d K a 1) *
      ProjGenLinGroup.mk (w K) = ProjGenLinGroup.mk (d K a⁻¹ 1) := by
  change ProjGenLinGroup.mk ((w K)⁻¹) * ProjGenLinGroup.mk (d K a 1) *
    ProjGenLinGroup.mk (w K) = _
  rw [← map_mul, ← map_mul]
  apply ProjGenLinGroup.mk_eq_mk_iff.mpr
  use a⁻¹
  apply Units.ext
  have hinv : (((w K)⁻¹ : GL2 K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; -1, 0] := by
    have h : (w K) * (-w K) = 1 := by
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [w, Matrix.mul_apply, Fin.sum_univ_succ]
    simpa [w] using congrArg (fun g : GL2 K => (g : Matrix (Fin 2) (Fin 2) K)) (inv_eq_of_mul_eq_one_right h)
  change (((w K)⁻¹ : GL2 K) : Matrix (Fin 2) (Fin 2) K) * (d K a 1 : Matrix (Fin 2) (Fin 2) K) *
    (w K : Matrix (Fin 2) (Fin 2) K) * (GeneralLinearGroup.scalar (Fin 2) a⁻¹ : Matrix (Fin 2) (Fin 2) K) = _
  rw [hinv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [d, w, hinv, GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_succ]
variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {G H D : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CommGroup D] [Finite D]
  {T : KPLocalStoneVonNeumann.LocalHeisenbergData H D}
open KPLocalPrincipalSeries
lemma coordinate_weyl_inverse (A : LocalBorelData (K := K) (G := G) T) (h : H) :
    A.coordinate (A.weyl h) = (A.coordinate h)⁻¹ := by
  apply diagonal_injective
  rw [← A.torus_projection, A.weyl_from_lift, map_mul, map_mul, map_inv,
    A.liftedW_projection, A.torus_projection]
  exact weyl_diagonal _
end
end DedekindZetaZeroFree.KPRankOneReversePairGeneric.GraphTwist
