module

public import DedekindZetaZeroFree.Eisenstein.Induction.Height.AdelicBottomRowHeight
public import DedekindZetaZeroFree.Adeles.Quotients.PGL.UpperRowHeightProducts

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField Matrix
namespace DedekindZetaZeroFree.KPLiteralExceptionalResidue
variable (F : Type) [Field F] [NumberField F]

 theorem baseRow_ne_zero : (![0, 1] : Fin 2 → F) ≠ 0 := by
  intro h
  have := congrFun h 1
  simpa using this

def actualBaseRowLine : KPChamberHeight.Line F :=
  Projectivization.mk F ![0, 1] (baseRow_ne_zero F)

variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem actualCompactHeightImage_isCompact
    (K : Subgroup (KPLiteralRaw.G F ζ hζ)) (hK : IsCompact (K : Set (KPLiteralRaw.G F ζ hζ))) :
    IsCompact ((coveredHeightProjection F ζ hζ) '' (K : Set _)) :=
  hK.image (coveredHeightProjection_continuous F ζ hζ)

theorem actualBaseRowHeight_compact_upper_bounds
    (K : Subgroup (KPLiteralRaw.G F ζ hζ)) (hK : IsCompact (K : Set (KPLiteralRaw.G F ζ hζ))) :
    ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧
      ∀ (B : KPChamberHeight.AdelGL F) (k : K), B 1 0 = 0 →
        m * KPChamberHeight.height F (actualBaseRowLine F) (ProjGenLinGroup.mk B) ≤
          KPChamberHeight.height F (actualBaseRowLine F)
            (ProjGenLinGroup.mk B * coveredHeightProjection F ζ hζ k.val) ∧
        KPChamberHeight.height F (actualBaseRowLine F)
            (ProjGenLinGroup.mk B * coveredHeightProjection F ζ hζ k.val) ≤
          M * KPChamberHeight.height F (actualBaseRowLine F) (ProjGenLinGroup.mk B) := by
  obtain ⟨m, M, hm, hmM, hb⟩ :=
    KPGlobalResidualKernel.ChamberNorm.rowHeight_upper_compact_bounds F
      ((coveredHeightProjection F ζ hζ) '' (K : Set _))
      (actualCompactHeightImage_isCompact F ζ hζ K hK)
  refine ⟨m, M, hm, hmM, fun B k h10 => ?_⟩
  obtain ⟨C, hC⟩ := ProjGenLinGroup.mk_surjective
    (coveredHeightProjection F ζ hζ k.val)
  have hh := hb B C h10 (by rw [hC]; exact ⟨k.val, k.property, rfl⟩)
  rw [← hC, ← map_mul]
  simpa only [actualBaseRowLine, KPChamberHeight.height_mk] using hh

end DedekindZetaZeroFree.KPLiteralExceptionalResidue

end
