module

public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.InductionReciprocity
public import DedekindZetaZeroFree.Metaplectic.Torus.Cubic.CubeClassesAndCenterCoordinates

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.ActualFiniteBorel.Geometry
noncomputable section
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : HeightOneSpectrum (𝓞 F))
open KPLocalSmoothRepresentation KPLocalInductionJacquetReciprocity

theorem root_ratio_one (x : Multiplicative (q.adicCompletion F)) :
    KPRankOneInduction.borelRatio F q
      ⟨projection F ζ hζ q (upperRoot F ζ hζ q x), upperRoot_mem_borel F ζ hζ q x⟩ = 1 := by
  apply Units.ext
  rw [KPRankOneInduction.borelRatio_eq F q _ (KubotaRankTwo.n _ x.toAdd) rfl]
  · simp [KubotaRankTwo.n, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  · simp [KubotaRankTwo.n, Matrix.GeneralLinearGroup.mkOfDetNeZero]

theorem retract_coordinate (b : Borel F ζ hζ q) :
    ActualFiniteTorus.coordinate F ζ hζ q (borelRetraction F ζ hζ q b) =
      KPRankOneInduction.borelRatio F q
        ⟨projection F ζ hζ q b.val, b.property⟩ := by
  obtain ⟨x, hx⟩ := borelRetraction_decomposition F ζ hζ q b
  let t : Borel F ζ hζ q :=
    ⟨(borelRetraction F ζ hζ q b).val,
      KPRankOneInduction.coveredTorus_le_Borel F q (projection F ζ hζ q)
        (borelRetraction F ζ hζ q b).property⟩
  let n : Borel F ζ hζ q := ⟨upperRoot F ζ hζ q x, upperRoot_mem_borel F ζ hζ q x⟩
  have hb : b = t * n := Subtype.ext hx
  let r := (KPRankOneInduction.borelRatio F q).comp
    (KPRankOneInduction.borelProjection F q (projection F ζ hζ q))
  change r t = r b
  rw [hb, map_mul]
  have hn : r n = 1 := root_ratio_one F ζ hζ q x
  rw [hn, mul_one]

theorem torus_projection (t : ActualFiniteTorus.H F ζ hζ q) :
    projection F ζ hζ q t.val = Matrix.ProjGenLinGroup.mk
      (KubotaRankTwo.d (q.adicCompletion F) (ActualFiniteTorus.coordinate F ζ hζ q t) 1) := by
  rw [(ActualFiniteTorus.actual_torus_normal_form F ζ hζ q).2.2.1 t]
  simp only [ActualFiniteTorus.normalWord, map_mul]
  change Matrix.ProjGenLinGroup.mk 1 * Matrix.ProjGenLinGroup.mk _ = _
  simp
  rfl
end
end DedekindZetaZeroFree.ActualFiniteBorel.Geometry
