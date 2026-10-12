module

public import DedekindZetaZeroFree.Eisenstein.Sections.CanonicalFlatFamily
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.Iwasawa.SphericalCompactInvariance
public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.TwoCellFormulaAndOutgoingProfiles
public import DedekindZetaZeroFree.Metaplectic.Cubic.Haar.SphericalSectorRealization

@[expose] public section

noncomputable section
open scoped Classical NumberField

namespace DedekindZetaZeroFree.KPContFlatCommonLevelKernel

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private theorem exp_smul_eq_of_support (s : ℂ) (a b : ℝ) (c : ℂ)
    (h : ((a - b : ℝ) : ℂ) * c = 0) :
    Complex.exp (s * (a : ℂ)) * c = Complex.exp (s * (b : ℂ)) * c := by
  rcases mul_eq_zero.mp h with h | h
  · have hab : a = b := by
      have h' : (a - b : ℝ) = 0 := Complex.ofReal_injective h
      exact sub_eq_zero.mp h'
    rw [hab]
  · rw [h, mul_zero, mul_zero]

def CommonLevel (U : KPMsRationalCompactCrossPairing.Level F ζ hζ) :
    Submodule ℂ (KPMsRationalCompactCrossPairing.Vplus F ζ hζ
      (KPContFlatSourceRecipe.D F ζ hζ)) where
  carrier := {f | ∀ (g : KPGlobalTorusFunctionData.G F ζ hζ)
      (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ U),
    f.val.val (g * u.val) = f.val.val g ∧
      ((KPContFlatSourceRecipe.alpha F ζ hζ (g * u.val) -
        KPContFlatSourceRecipe.alpha F ζ hζ g : ℝ) : ℂ) * f.val.val g = 0}
  zero_mem' := by
    intro g u
    constructor <;> simp
  add_mem' := by
    intro f k hf hk g u
    obtain ⟨hf1, hf2⟩ := hf g u
    obtain ⟨hk1, hk2⟩ := hk g u
    constructor
    · simp only [Submodule.coe_add, Pi.add_apply, hf1, hk1]
    · simp only [Submodule.coe_add, Pi.add_apply, hf1, hk1, mul_add, hf2, hk2, add_zero]
  smul_mem' := by
    intro c f hf g u
    obtain ⟨hf1, hf2⟩ := hf g u
    constructor
    · simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hf1]
    · simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [mul_left_comm, hf2, mul_zero]

def rightKInfinityFixed :
    Submodule ℂ (KPMsRationalCompactCrossPairing.Vplus F ζ hζ
      (KPContFlatSourceRecipe.D F ζ hζ)) where
  carrier := {f | ∀ (g : KPGlobalTorusFunctionData.G F ζ hζ)
      (k : KPContSectorArchSphericalFibers.KInfinity F),
    f.val.val (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ k.val) =
      f.val.val g}
  zero_mem' := by
    intro g k
    simp
  add_mem' := by
    intro f k hf hk g u
    simp only [Submodule.coe_add, Pi.add_apply, hf g u, hk g u]
  smul_mem' := by
    intro c f hf g u
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hf g u]

def CommonSphericalStage (U : KPMsRationalCompactCrossPairing.Level F ζ hζ) :=
  CommonLevel F ζ hζ U ⊓ rightKInfinityFixed F ζ hζ

def L {S : Type*} [AddCommGroup S] [Module ℂ S]
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (ι : S →ₗ[ℂ] CommonSphericalStage F ζ hζ U) (s : ℂ) :
    S →ₗ[ℂ] (KPGlobalTorusFunctionData.G F ζ hζ → ℂ) :=
  (KPMsRationalCompactCrossPairing.Source F ζ hζ s).subtype.comp
    ((KPContFlatSourceRecipe.flatR F ζ hζ s).comp
      ((CommonSphericalStage F ζ hζ U).subtype.comp ι))

theorem L_formula {S : Type*} [AddCommGroup S] [Module ℂ S]
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (ι : S →ₗ[ℂ] CommonSphericalStage F ζ hζ U) (s : ℂ) (v : S)
    (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    L F ζ hζ U ι s v g =
      Complex.exp (s * (KPContFlatSourceRecipe.alpha F ζ hζ g : ℂ)) *
        (ι v).val.val.val g := by
  simp only [L, LinearMap.comp_apply, Submodule.coe_subtype]
  rw [KPContFlatSourceRecipe.flatR_formula]

theorem archimedeanInsertion_alpha_right
    (g : KPGlobalTorusFunctionData.G F ζ hζ)
    (k : KPContSectorArchSphericalFibers.KInfinity F) :
    KPContFlatSourceRecipe.alpha F ζ hζ
      (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ k.val) =
      KPContFlatSourceRecipe.alpha F ζ hζ g := by
  exact KPContinuation.ArchCompact.alpha_archimedeanInsertion_right F ζ hζ g k

theorem stage_properties {S : Type*} [AddCommGroup S] [Module ℂ S]
    [FiniteDimensional ℂ S]
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (ι : S →ₗ[ℂ] CommonSphericalStage F ζ hζ U)
    (s : ℂ) (hs : s ∈ KPContinuation.spectralDomain) :
    (∀ (v : S) (g : KPGlobalTorusFunctionData.G F ζ hζ)
      (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ U),
      L F ζ hζ U ι s v (g * u.val) = L F ζ hζ U ι s v g) ∧
    (∀ (v : S) (g : KPGlobalTorusFunctionData.G F ζ hζ)
      (k : KPContSectorArchSphericalFibers.KInfinity F),
      L F ζ hζ U ι s v
        (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ k.val) =
          L F ζ hζ U ι s v g) ∧
    (∀ (v : S) (ε : rootsOfUnity 3 F) (g : KPGlobalTorusFunctionData.G F ζ hζ),
      L F ζ hζ U ι s v (KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * g) =
        (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) *
          L F ζ hζ U ι s v g) ∧
    (∀ (v : S) (y : Fˣ) (x : F) (g : KPGlobalTorusFunctionData.G F ζ hζ),
      L F ζ hζ U ι s v
        (((KPGlobalTorusFunctionData.s F ζ hζ y).val *
          KPGlobalTorusFunctionData.N F ζ hζ
            (algebraMap F (KPGlobalTorusFunctionData.Adeles F) x)) * g) =
        L F ζ hζ U ι s v g) ∧
    (∀ (v : S) (h : (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ s).H)
      (x : KPGlobalTorusFunctionData.Adeles F) (g : KPGlobalTorusFunctionData.G F ζ hζ),
      L F ζ hζ U ι s v ((h.val.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g) =
        KPGlobalTorusFunctionData.deltaHalf F ζ hζ h.val *
          ((KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ s).character h : ℂ) *
            L F ζ hζ U ι s v g) := by
  have hCL : ∀ v : S, (ι v).val ∈ CommonLevel F ζ hζ U := fun v => (ι v).property.1
  have hKI : ∀ v : S, (ι v).val ∈ rightKInfinityFixed F ζ hζ :=
    fun v => (ι v).property.2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v g u
    rw [L_formula, L_formula]
    obtain ⟨h1, h2⟩ := hCL v g u
    rw [h1]
    exact exp_smul_eq_of_support s _ _ _ h2
  · intro v g k
    rw [L_formula, L_formula, hKI v g k, archimedeanInsertion_alpha_right F ζ hζ g k]
  · intro v ε g
    let t : KPGlobalTorusFunctionData.E F ζ hζ :=
      (KPGlobalCenterRationalCharacter.centralRoot F ζ hζ ε).val
    let h : (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ s).H :=
      ⟨t, (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ s).contains_center
        (KPGlobalCenterRationalCharacter.centralRoot F ζ hζ ε).property⟩
    have hN : KPGlobalTorusFunctionData.N F ζ hζ (0 : KPGlobalTorusFunctionData.Adeles F) = 1 :=
      (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
    have hp' : KPGlobalTorusFunctionData.p F ζ hζ
        (KPGlobalCenterRationalCharacter.centralRoot F ζ hζ ε).val = 1 := by
      unfold KPGlobalTorusFunctionData.p
      have hker : KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ ε ∈
          (KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ).ker := by
        rw [← KPAdelicCoverRestrictedProduct.pglCentralInjection_kernel F ζ hζ]
        exact ⟨ε, rfl⟩
      have hp : KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ
          (KPGlobalCenterRationalCharacter.centralRoot F ζ hζ ε).val.val = 1 := by
        rw [KPGlobalCenterRationalCharacter.centralRoot_formula]
        exact MonoidHom.mem_ker.mp hker
      have ht : ((KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ).restrict
          (fun t ht => ht)) (KPGlobalCenterRationalCharacter.centralRoot F ζ hζ ε).val =
            (1 : KPGlobalTorusFunctionData.ordinaryTorus F) := Subtype.ext hp
      change KPGlobalTorusFunctionData.torusRatio F _ = 1
      rw [ht, map_one]
    have hdelta : KPGlobalTorusFunctionData.delta F ζ hζ (h : KPGlobalTorusFunctionData.E F ζ hζ) = 1 := by
      change KPGlobalTorusFunctionData.delta F ζ hζ
        (KPGlobalCenterRationalCharacter.centralRoot F ζ hζ ε).val = 1
      simp only [KPGlobalTorusFunctionData.delta, MonoidHom.comp_apply, hp', map_one]
    have hdh : KPGlobalTorusFunctionData.deltaHalf F ζ hζ
        (h : KPGlobalTorusFunctionData.E F ζ hζ) = 1 := by
      simp only [KPGlobalTorusFunctionData.deltaHalf, hdelta, Units.val_one, NNReal.coe_one,
        Real.sqrt_one, Complex.ofReal_one]
    have hnc : ((KPGlobalTorusBorelTwistCompatibility.normCharacter F ζ hζ s
        (h : KPGlobalTorusFunctionData.E F ζ hζ) : ℂˣ) : ℂ) = 1 := by
      change KPGlobalTorusBorelTwistCompatibility.normPower F ζ hζ s
        (h : KPGlobalTorusFunctionData.E F ζ hζ) = 1
      simp only [KPGlobalTorusBorelTwistCompatibility.normPower, hdelta, Units.val_one,
        NNReal.coe_one, Real.log_one, mul_zero, Complex.ofReal_zero, Complex.exp_zero]
    have hlam : (KPGlobalTorusBorelTwistCompatibility.rationalModel F ζ hζ).character h =
        KPGlobalTorusFunctionData.iota F ζ hζ ε :=
      KPGlobalCenterRationalCharacter.lambdaR_genuine F ζ hζ ε h (by rfl)
    have hsplit : ((KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ s).character h : ℂˣ) =
        (KPGlobalTorusBorelTwistCompatibility.rationalModel F ζ hζ).character h *
          KPGlobalTorusBorelTwistCompatibility.normCharacter F ζ hζ s
            (h : KPGlobalTorusFunctionData.E F ζ hζ) := rfl
    have hcoef : KPGlobalTorusFunctionData.deltaHalf F ζ hζ
          (h : KPGlobalTorusFunctionData.E F ζ hζ) *
        ((KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ s).character h : ℂ) =
        ((KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : Circle) : ℂ) := by
      have h1 : (((KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ s).character h : ℂˣ) : ℂ)
          = (KPGlobalTorusFunctionData.iota F ζ hζ ε : ℂ) := by
        rw [hsplit, hlam, Units.val_mul, hnc, mul_one]
      rw [hdh, one_mul, h1]
      rfl
    have htv : (h : KPGlobalTorusFunctionData.E F ζ hζ).val =
        KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε :=
      KPGlobalCenterRationalCharacter.centralRoot_formula F ζ hζ ε
    have hprop := (KPContFlatSourceRecipe.flatR F ζ hζ s (ι v).val).property h 0 g
    rw [htv, hN, mul_one, hcoef] at hprop
    rw [L_formula, L_formula]
    change (KPContFlatSourceRecipe.flatR F ζ hζ s (ι v).val).val
        (KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * g) =
      (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) *
        (KPContFlatSourceRecipe.flatR F ζ hζ s (ι v).val).val g
    exact hprop
  · intro v y x g
    have hs : (KPGlobalTorusFunctionData.s F ζ hζ y).val =
        KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
          (KPAdelicCoverRestrictedProduct.rationalSection F ζ hζ (KubotaRankTwo.d F y 1)) := rfl
    have hN : KPGlobalTorusFunctionData.N F ζ hζ
          (algebraMap F (KPGlobalTorusFunctionData.Adeles F) x) =
        KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
          (KPAdelicCoverRestrictedProduct.rationalSection F ζ hζ (KubotaRankTwo.n F x)) := by
      rw [show KPGlobalTorusFunctionData.N F ζ hζ
            (algebraMap F (KPGlobalTorusFunctionData.Adeles F) x) =
          KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
            (KPRationalAdelicSplitting.N F ζ hζ
              (algebraMap F (KPGlobalTorusFunctionData.Adeles F) x)) from rfl,
        KPRationalAdelicSplitting.N_rational F ζ hζ x]
    have hmat : KubotaRankTwo.d F y 1 * KubotaRankTwo.n F x =
        Matrix.GeneralLinearGroup.mkOfDetNeZero !![(y : F), (y : F) * x; 0, 1]
          (by simpa [Matrix.det_fin_two] using Units.ne_zero y) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [KubotaRankTwo.d, KubotaRankTwo.n, Matrix.mul_apply, Fin.sum_univ_two]
    have hm : (Matrix.GeneralLinearGroup.mkOfDetNeZero
        !![(y : F), (y : F) * x; 0, 1]
        (by simpa [Matrix.det_fin_two] using Units.ne_zero y)) ∈
        KPRationalFlag.borel F := by
      change (Matrix.GeneralLinearGroup.mkOfDetNeZero
        !![(y : F), (y : F) * x; 0, 1] _ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
      simp
    have hb : Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.mkOfDetNeZero
        !![(y : F), (y : F) * x; 0, 1]
        (by simpa [Matrix.det_fin_two] using Units.ne_zero y)) ∈
        KPChamberBruhatTwoCells.rationalBorel F :=
      ⟨_, hm, rfl⟩
    have hkey : (KPGlobalTorusFunctionData.s F ζ hζ y).val *
        KPGlobalTorusFunctionData.N F ζ hζ
          (algebraMap F (KPGlobalTorusFunctionData.Adeles F) x) =
        DedekindZetaZeroFree.KPGlobalResidualKernel.RawStageL2.Outgoing.ActualBruhat.rational
          F ζ hζ
          (Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.mkOfDetNeZero
            !![(y : F), (y : F) * x; 0, 1]
            (by simpa [Matrix.det_fin_two] using Units.ne_zero y))) := by
      rw [hs, hN, ← map_mul, ← KPAdelicCoverRestrictedProduct.rationalSection_mul, hmat]
      rw [← DedekindZetaZeroFree.KPGlobalResidualKernel.RawStageL2.Outgoing.ChamberQuotient.rationalEquiv_lift
          F ζ hζ,
        DedekindZetaZeroFree.KPGlobalResidualKernel.RawStageL2.Outgoing.ChamberQuotient.rationalEquiv_mk]
      exact (KPRationalAdelicSplitting.rationalPGLHom_mk F ζ hζ _).symm
    rw [L_formula, L_formula, hkey]
    exact DedekindZetaZeroFree.KPGlobalResidualKernel.RawStageL2.Outgoing.ActualBruhat.scalar_rational_borel_invariant
      F ζ hζ s (KPContFlatSourceRecipe.flatR F ζ hζ s (ι v).val) ⟨_, hb⟩ g
  · intro v h x g
    rw [L_formula, L_formula]
    exact (KPContFlatSourceRecipe.flatR F ζ hζ s (ι v).val).property h x g

theorem commonLevel_eq_fixedPlus_of_le
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (hU : KPGlobalTorusFunctionData.globalLevel F ζ hζ U ≤
      (KPContFlatSourceRecipe.D F ζ hζ).K) :
    CommonLevel F ζ hζ U =
      KPMsRationalCompactCrossPairing.fixedPlus F ζ hζ
        (KPContFlatSourceRecipe.D F ζ hζ) U := by
  ext f
  constructor
  · intro hf g u
    exact (hf g u).1
  · intro hf g u
    refine ⟨hf g u, ?_⟩
    have hk : KPGlobalTorusFunctionData.globalLevel F ζ hζ U ≤
        (KPContFlatFullProductIwasawa.iwasawaData F ζ hζ).K := hU
    have hmem : u.val ∈ (KPContFlatFullProductIwasawa.iwasawaData F ζ hζ).K :=
      hk u.property
    have hα := KPContFlatFullProductIwasawa.alpha_mul_compact F ζ hζ g ⟨u.val, hmem⟩
    rw [sub_eq_zero.mpr hα, Complex.ofReal_zero, zero_mul]

end DedekindZetaZeroFree.KPContFlatCommonLevelKernel

end
