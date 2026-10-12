module

public import DedekindZetaZeroFree.Eisenstein.Induction.RationalBorelCovariance
public import DedekindZetaZeroFree.Eisenstein.Induction.PGLAdelicRowHeight

@[expose] public section

noncomputable section
open scoped NumberField Classical
namespace DedekindZetaZeroFree.KPLiteralExceptionalResidue

variable (F : Type) [Field F] [NumberField F]

theorem height_borel_eq_rationalBorel :
    KPChamberHeight.borel F = KPChamberBruhatTwoCells.rationalBorel F := by
  unfold KPChamberHeight.borel KPChamberBruhatTwoCells.rationalBorel
  have he : {g | ∃ A : KPChamberHeight.RatGL F,
      Matrix.ProjGenLinGroup.mk A = g ∧ A 1 0 = 0} =
      ((KPRationalFlag.borel F).map Matrix.ProjGenLinGroup.mk : Set _) := by
    ext g
    constructor
    · rintro ⟨A, rfl, hA⟩
      exact ⟨A, hA, rfl⟩
    · rintro ⟨A, hA, rfl⟩
      exact ⟨A, rfl, hA⟩
  rw [he, Subgroup.closure_eq]

theorem bottomRow_eq_of_rationalCoset_eq
    (a b : Matrix.ProjGenLinGroup (Fin 2) F)
    (h : KPChamberBruhatTwoCells.rationalCoset F a =
      KPChamberBruhatTwoCells.rationalCoset F b) :
    KPChamberHeight.bottomRow F a = KPChamberHeight.bottomRow F b := by
  obtain ⟨e, he⟩ := KPChamberHeight.rational_bruhat_index F
  rw [← he a, ← he b]
  apply congrArg e
  apply Quotient.sound
  rw [height_borel_eq_rationalBorel]
  exact Quotient.exact h

theorem bottomRow_one_mulHeight :
    Projectivization.mulHeight (KPChamberHeight.bottomRow F 1) = 1 := by
  rw [← Matrix.ProjGenLinGroup.mk_one, KPChamberHeight.bottomRow_mk,
    Projectivization.mulHeight_mk]
  have he : (fun i : Fin 2 => (1 : KPChamberHeight.RatGL F) 1 i) =
      (![0, 1] : Fin 2 → F) := by
    funext i
    fin_cases i <;> simp
  rw [he, Height.mulHeight_swap]
  simp

theorem bottomRow_open_mulHeight (t : F) :
    Projectivization.mulHeight (KPChamberHeight.bottomRow F
      (KPChamberBruhatTwoCells.rationalWeyl F *
        KPChamberBruhatTwoCells.rationalUnipotent F t)) =
      Height.mulHeight (![t, 1] : Fin 2 → F) := by
  unfold KPChamberBruhatTwoCells.rationalWeyl KPChamberBruhatTwoCells.rationalUnipotent
  rw [← map_mul, KPChamberHeight.bottomRow_mk, Projectivization.mulHeight_mk]
  have he : (fun i : Fin 2 =>
      ((Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, -1; 1, 0] (by
        simp [Matrix.det_fin_two]) *
        Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, t; 0, 1] (by
          simp [Matrix.det_fin_two]) : KPChamberHeight.RatGL F) 1 i)) =
      (![1, t] : Fin 2 → F) := by
    funext i
    fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [he, Height.mulHeight_swap]

theorem fixed_parameter_height_lower_bound (g : KPChamberHeight.AdelPGL F) :
    ∃ m : ℝ, 0 < m ∧ ∀ ℓ : KPChamberHeight.Line F,
      m * Projectivization.mulHeight ℓ ≤ KPChamberHeight.height F ℓ g := by
  obtain ⟨m, M, hm, hmM, hb⟩ := KPChamberHeight.compact_uniform_height F
    {g} (isCompact_singleton)
  obtain ⟨C, hC, hcompare⟩ := KPChamberHeight.height_one_compare F
  refine ⟨m, hm, fun ℓ => ?_⟩
  exact (mul_le_mul_of_nonneg_left (hcompare ℓ).2.1 hm.le).trans
    (hb ℓ g (Set.mem_singleton g)).1

def adelicHeightProjection : KPAdelicCoverRestrictedProduct.AdelicPGL2 F →*
    KPChamberHeight.AdelPGL F :=
  QuotientGroup.map (KPAdelicCoverRestrictedProduct.scalarSubgroup F)
    (Subgroup.center (KPAdelicCoverRestrictedProduct.AdelicGL2 F))
    (MonoidHom.id _) (KPAdelicCoverRestrictedProduct.scalarSubgroup_central F)

theorem adelicHeightProjection_continuous : Continuous (adelicHeightProjection F) := by
  apply (QuotientGroup.isQuotientMap_mk
    (KPAdelicCoverRestrictedProduct.scalarSubgroup F)).continuous_iff.mpr
  exact QuotientGroup.continuous_mk

def coveredHeightProjection (ζ : F) (hζ : IsPrimitiveRoot ζ 12) :
    KPLiteralRaw.G F ζ hζ →* KPChamberHeight.AdelPGL F :=
  (adelicHeightProjection F).comp (KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ)

theorem coveredHeightProjection_continuous (ζ : F) (hζ : IsPrimitiveRoot ζ 12) :
    Continuous (coveredHeightProjection F ζ hζ) :=
  (adelicHeightProjection_continuous F).comp
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.2.continuous

theorem coveredHeightProjection_rationalLift (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (γ : Matrix.ProjGenLinGroup (Fin 2) F) :
    coveredHeightProjection F ζ hζ (KPLiteralRaw.rationalLift F ζ hζ γ) =
      KPChamberHeight.rationalDiagonal F γ := by
  unfold KPLiteralRaw.rationalLift coveredHeightProjection
  rw [MonoidHom.comp_apply]
  change adelicHeightProjection F
    (QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)
      (KPAdelicCoverRestrictedProduct.projection F ζ hζ
        (KPAdelicCoverRestrictedProduct.rationalSection F ζ hζ (Quotient.out γ)))) = _
  rw [KPAdelicCoverRestrictedProduct.projection_rationalSection]
  change Matrix.ProjGenLinGroup.mk
    (KPAdelicCoverRestrictedProduct.rationalBase F (Quotient.out γ)) = _
  have he : Matrix.ProjGenLinGroup.mk (Quotient.out γ) = γ := Quotient.out_eq γ
  conv_rhs => rw [← he]
  rfl

end DedekindZetaZeroFree.KPLiteralExceptionalResidue

end
