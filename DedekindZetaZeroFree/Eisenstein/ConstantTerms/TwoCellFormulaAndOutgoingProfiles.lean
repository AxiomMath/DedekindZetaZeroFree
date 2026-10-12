module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.BruhatTwoCellIntegral
public import DedekindZetaZeroFree.Eisenstein.Induction.CompactModels.SmoothAngularProfiles

@[expose] public section

noncomputable section
open MeasureTheory
open scoped NumberField Classical NNReal
namespace DedekindZetaZeroFree.KPGlobalResidualKernel.RawStageL2.Outgoing
namespace ChamberQuotient
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def rationalEquiv : Matrix.ProjGenLinGroup (Fin 2) F ≃* KPRationalAdelicSplitting.RationalPGL2 F :=
  QuotientGroup.quotientMulEquivOfEq Matrix.GeneralLinearGroup.center_eq_range_scalar
@[simp] theorem rationalEquiv_mk (m : Matrix.GeneralLinearGroup (Fin 2) F) :
    rationalEquiv F (Matrix.ProjGenLinGroup.mk m) = KPRationalAdelicSplitting.rationalPGLQuotient F m := by
  exact QuotientGroup.quotientMulEquivOfEq_mk _ m
@[simp] theorem rationalEquiv_lift (g : Matrix.ProjGenLinGroup (Fin 2) F) :
    KPRationalAdelicSplitting.rationalPGLHom F ζ hζ (rationalEquiv F g) = ActualBruhat.rational F ζ hζ g := by
  induction g using Matrix.ProjGenLinGroup.induction_on with
  | mk m => rw [rationalEquiv_mk]; rfl

private theorem raw_borel_mk (m : Matrix.GeneralLinearGroup (Fin 2) F) :
    KPRationalAdelicSplitting.rationalPGLQuotient F m ∈ rawRationalBorel F ζ hζ ↔ m 1 0 = 0 := by
  have hp := DFunLike.congr_fun (KPRationalAdelicSplitting.rationalPGL_splitting F ζ hζ).2
    (KPRationalAdelicSplitting.rationalPGLQuotient F m)
  change (KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ)
    (KPRationalAdelicSplitting.rationalPGLHom F ζ hζ (KPRationalAdelicSplitting.rationalPGLQuotient F m)) = _ at hp
  change (KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ)
    (KPRationalAdelicSplitting.rationalPGLHom F ζ hζ (KPRationalAdelicSplitting.rationalPGLQuotient F m)) ∈ KPGlobalTorusFunctionData.ordinaryBorel F ↔ _
  rw [hp]
  change (∃ a : KPAdelicCoverRestrictedProduct.AdelicGL2 F,
    QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) a =
      QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) (KPAdelicCoverRestrictedProduct.rationalBase F m) ∧ a 1 0 = 0) ↔ _
  constructor
  · rintro ⟨a, he, ha⟩
    obtain ⟨z, hz, hez⟩ := (QuotientGroup.mk'_eq_mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)).mp he
    obtain ⟨u, rfl⟩ := hz
    have hent := congrArg (fun a : KPAdelicCoverRestrictedProduct.AdelicGL2 F => a 1 0) hez
    have hzero : algebraMap F (KPGlobalTorusFunctionData.Adeles F) (m 1 0) = 0 := by
      simpa [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, ha,
        Matrix.GeneralLinearGroup.coe_scalar, KPAdelicCoverRestrictedProduct.rationalBase] using hent.symm
    exact (NumberField.AdeleRing.algebraMap_injective (𝓞 F) F) (by simpa using hzero)
  · intro hm
    exact ⟨_, rfl, by simpa [KPAdelicCoverRestrictedProduct.rationalBase] using congrArg (algebraMap F (KPGlobalTorusFunctionData.Adeles F)) hm⟩

private theorem matrix_borel_mk (m : Matrix.GeneralLinearGroup (Fin 2) F) :
    Matrix.ProjGenLinGroup.mk m ∈ KPChamberBruhatTwoCells.rationalBorel F ↔ m 1 0 = 0 := by
  constructor
  · rintro ⟨b, hb, he⟩
    obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp he
    have hc := congrArg (fun c : Matrix.GeneralLinearGroup (Fin 2) F => c 1 0) hu
    change b 1 0 = 0 at hb
    simpa [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.mul_apply, Fin.sum_univ_two, hb] using hc.symm
  · intro hm
    exact ⟨m, hm, rfl⟩

theorem rationalEquiv_borel (g : Matrix.ProjGenLinGroup (Fin 2) F) :
    g ∈ KPChamberBruhatTwoCells.rationalBorel F ↔ rationalEquiv F g ∈ rawRationalBorel F ζ hζ := by
  induction g using Matrix.ProjGenLinGroup.induction_on with
  | mk m => rw [matrix_borel_mk, rationalEquiv_mk, raw_borel_mk]

def cosetEquiv : KPChamberBruhatTwoCells.RationalQuotient F ≃ RawRationalQuotient F ζ hζ :=
  Quotient.congr (rationalEquiv F).toEquiv (by
    intro a b
    rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply]
    change b * a⁻¹ ∈ KPChamberBruhatTwoCells.rationalBorel F ↔
      (rationalEquiv F b) * (rationalEquiv F a)⁻¹ ∈ rawRationalBorel F ζ hζ
    rw [← map_inv, ← map_mul]
    exact rationalEquiv_borel F ζ hζ _)

end ChamberQuotient

end DedekindZetaZeroFree.KPGlobalResidualKernel.RawStageL2.Outgoing

end
