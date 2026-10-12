module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GreenIdentity.PairingsAndFluxDefinitions
public import DedekindZetaZeroFree.Theta.Periods.TranslatedStandardPeriodNonvanishing

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal NNReal Topology
open MeasureTheory
namespace DedekindZetaZeroFree.KPMsGreenFlux.FiniteSlabActualMean
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

 theorem cuspRepresentative_mem_rational (j : Cusps A) :
    cuspRepresentative A j ∈ KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ := by
  exact ⟨_, rfl⟩

 theorem root_mem_rational (t : F) :
    KPGlobalTorusFunctionData.N F ζ hζ
      (algebraMap F (KPGlobalTorusFunctionData.Adeles F) t) ∈
        KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ := by
  refine ⟨KPRationalAdelicSplitting.rationalPGLQuotient F (KubotaRankTwo.n F t), ?_⟩
  rw [KPRationalAdelicSplitting.rationalPGLHom_mk]
  change KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ _ =
    KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ _
  congr 1
  exact (KPRationalAdelicSplitting.N_rational F ζ hζ t).symm

theorem integrand_eq_of_additive_quotient_eq
    (j : Cusps A) (f : Cover F ζ hζ → ℂ)
    (hf : ∀ γ : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ, ∀ g,
      f (γ.val * g) = f g)
    (g : Cover F ζ hζ) (b c : KPGlobalTorusFunctionData.Adeles F)
    (hbc : (QuotientAddGroup.mk b : KPCompactFourier.AdditiveQuotient F) =
      QuotientAddGroup.mk c) :
    f (cuspRepresentative A j * KPGlobalTorusFunctionData.N F ζ hζ b *
      (cuspRepresentative A j)⁻¹ * g) =
    f (cuspRepresentative A j * KPGlobalTorusFunctionData.N F ζ hζ c *
      (cuspRepresentative A j)⁻¹ * g) := by
  obtain ⟨t, ht⟩ := QuotientAddGroup.eq.mp hbc
  have hcb : c = algebraMap F (KPGlobalTorusFunctionData.Adeles F) t + b := by
    change c = algebraMap F (NumberField.AdeleRing (𝓞 F) F) t + b
    rw [ht]
    abel
  rw [hcb, KPGlobalTorusFunctionData.N_add]
  let γ := cuspRepresentative A j *
    KPGlobalTorusFunctionData.N F ζ hζ
      (algebraMap F (KPGlobalTorusFunctionData.Adeles F) t) * (cuspRepresentative A j)⁻¹
  have hγ : γ ∈ KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ :=
    (KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ).mul_mem
      ((KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ).mul_mem
        (cuspRepresentative_mem_rational A j) (root_mem_rational t))
      ((KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ).inv_mem
        (cuspRepresentative_mem_rational A j))
  have he : cuspRepresentative A j *
      (KPGlobalTorusFunctionData.N F ζ hζ
        (algebraMap F (KPGlobalTorusFunctionData.Adeles F) t) *
          KPGlobalTorusFunctionData.N F ζ hζ b) * (cuspRepresentative A j)⁻¹ * g =
      γ * (cuspRepresentative A j * KPGlobalTorusFunctionData.N F ζ hζ b *
        (cuspRepresentative A j)⁻¹ * g) := by
    dsimp [γ]
    group
  rw [he]
  exact (hf ⟨γ, hγ⟩ _).symm

theorem integrand_joint_continuous
    (j : Cusps A) (f : Cover F ζ hζ → ℂ) (hcont : Continuous f)
    (hf : ∀ γ : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ, ∀ g,
      f (γ.val * g) = f g) :
    Continuous (fun p : KPCompactFourier.AdditiveQuotient F × Cover F ζ hζ =>
      f (cuspRepresentative A j * KPGlobalTorusFunctionData.N F ζ hζ
        (KPCompactFourier.representative F p.1) * (cuspRepresentative A j)⁻¹ * p.2)) := by
  letI : IsTopologicalGroup (Cover F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  apply (QuotientAddGroup.isOpenQuotientMap_mk.prodMap
    (IsOpenQuotientMap.id (X := Cover F ζ hζ))).continuous_comp_iff.mp
  have hout (z : KPGlobalTorusFunctionData.Adeles F × Cover F ζ hζ) :
      f (cuspRepresentative A j * KPGlobalTorusFunctionData.N F ζ hζ
        (KPCompactFourier.representative F (QuotientAddGroup.mk z.1)) *
          (cuspRepresentative A j)⁻¹ * z.2) =
      f (cuspRepresentative A j * KPGlobalTorusFunctionData.N F ζ hζ z.1 *
        (cuspRepresentative A j)⁻¹ * z.2) :=
    integrand_eq_of_additive_quotient_eq A j f hf z.2 _ _ (Quotient.out_eq _)
  change Continuous (fun z : KPGlobalTorusFunctionData.Adeles F × Cover F ζ hζ =>
    f (cuspRepresentative A j * KPGlobalTorusFunctionData.N F ζ hζ
      (KPCompactFourier.representative F (QuotientAddGroup.mk z.1)) *
        (cuspRepresentative A j)⁻¹ * z.2))
  simp_rw [hout]
  exact hcont.comp (((continuous_const.mul
    ((KPWildIndependentGenericity.NonzeroPeriod.actual_upper_root_continuous
      F ζ hζ).comp continuous_fst)).mul continuous_const).mul continuous_snd)

end DedekindZetaZeroFree.KPMsGreenFlux.FiniteSlabActualMean

end
