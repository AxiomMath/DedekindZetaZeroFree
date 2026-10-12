module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Residues.ArchimedeanTraceCofactor
public import DedekindZetaZeroFree.Eisenstein.Induction.FiniteExponentialParameterSections
public import DedekindZetaZeroFree.Metaplectic.Torus.RationalNormOneCofactors

@[expose] public section

noncomputable section
open scoped NumberField Classical BigOperators ENNReal
open MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.TransportedRationalCofactor
open KPLocalPrincipalSeries KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPRankOneShellRepair
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.ActualCofactor renaming actual_rational_family_regular → actual_rational_family_regular
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F ζ hζ)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F ζ hζ P)
variable (E : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (hE : C.exceptional ⊆ E)
variable (J : ∀ q : E, IwasawaData (C.canonical q.val).borel)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

private theorem transported_family_regular
    (φ : ∀ q : E, compactPicture (C.canonical q.val).borel (C.polarization q.val)
      (C.canonical q.val).iwasawa .plus)
    (t : KPGlobalTorusFunctionData.E F ζ hζ) :
    let μ : ∀ q : E, Measure (LocalField F q.val) := fun q =>
      Measure.addHaarMeasure (finiteCompletionIntegersPositiveCompacts F q.val)
    let c : ℂ → ℂ := fun s => ActualCofactor.rationalStageEval F ζ hζ P C E hE t
      (fun q => (localHalfDifferentFactor F q.val : ℂ) •
        (actualCanonicalContinued F q.val ζ hζ (C.canonical q.val) (C.polarization q.val)
          (μ q) (ActualCofactor.unit_mass F q.val) .plus s
          (FiniteSourceTransport.parameterSource (C.canonical q.val).borel
            (C.canonical q.val).iwasawa (J q) (C.polarization q.val) .plus (φ q) s)).val 1)
    MeromorphicOn c Set.univ ∧ AnalyticAt ℂ c 0 := by
  dsimp only
  let μ : ∀ q : E, Measure (LocalField F q.val) := fun q =>
    Measure.addHaarMeasure (finiteCompletionIntegersPositiveCompacts F q.val)
  let N (q : E) := FiniteSourceTransport.normValues (C.canonical q.val).borel
    (C.canonical q.val).iwasawa (J q)
  let v (q : E) (r : ℝ) := FiniteSourceTransport.normPiece (C.canonical q.val).borel
    (C.canonical q.val).iwasawa (J q) (C.polarization q.val) .plus (φ q) r
  let L := ActualCofactor.rationalStageEval F ζ hζ P C E hE t
  let f (s : ℂ) (q : E) := actualCanonicalContinued F q.val ζ hζ
    (C.canonical q.val) (C.polarization q.val) (μ q) (ActualCofactor.unit_mass F q.val) .plus s
  have he (s : ℂ) : L (fun q => (localHalfDifferentFactor F q.val : ℂ) •
      (f s q (FiniteSourceTransport.parameterSource (C.canonical q.val).borel
        (C.canonical q.val).iwasawa (J q) (C.polarization q.val) .plus (φ q) s)).val 1) =
      ∑ r ∈ Fintype.piFinset N, (∏ q : E, Complex.exp (s * (r q : ℂ))) *
        L (fun q => (localHalfDifferentFactor F q.val : ℂ) • (f s q (v q (r q))).val 1) := by
    have hh (q : E) : (localHalfDifferentFactor F q.val : ℂ) •
        (f s q (FiniteSourceTransport.parameterSource (C.canonical q.val).borel
          (C.canonical q.val).iwasawa (J q) (C.polarization q.val) .plus (φ q) s)).val 1 =
        ∑ r ∈ N q, Complex.exp (s * (r : ℂ)) •
          ((localHalfDifferentFactor F q.val : ℂ) • (f s q (v q r)).val 1) := by
      rw [FiniteSourceTransport.parameterSource_finite_expansion]
      simp only [map_sum, map_smul, Submodule.coe_sum, Finset.sum_apply,
        Submodule.coe_smul, Pi.smul_apply, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro r _
      exact smul_comm _ _ _
    simp_rw [hh]
    rw [L.map_sum_finset]
    apply Finset.sum_congr rfl
    intro r _
    exact L.map_smul_univ _ _
  have hr (r : ∀ q : E, ℝ) := actual_rational_family_regular F ζ hζ P C E hE μ
    (fun q => ActualCofactor.unit_mass F q.val) (fun q => v q (r q)) (fun _ => 1) t
  have ha (r : ∀ q : E, ℝ) (s : ℂ) : AnalyticAt ℂ
      (fun z => ∏ q : E, Complex.exp (z * (r q : ℂ))) s := by
    apply Finset.analyticAt_fun_prod
    intro q _
    fun_prop
  have hmer : MeromorphicOn (fun s => L (fun q => (localHalfDifferentFactor F q.val : ℂ) •
      (f s q (FiniteSourceTransport.parameterSource (C.canonical q.val).borel
        (C.canonical q.val).iwasawa (J q) (C.polarization q.val) .plus (φ q) s)).val 1)) Set.univ ∧
      AnalyticAt ℂ (fun s => L (fun q => (localHalfDifferentFactor F q.val : ℂ) •
        (f s q (FiniteSourceTransport.parameterSource (C.canonical q.val).borel
          (C.canonical q.val).iwasawa (J q) (C.polarization q.val) .plus (φ q) s)).val 1)) 0 := by
    simp_rw [he]
    constructor
    · intro s _
      exact MeromorphicAt.fun_sum (fun r _ => (ha r s).meromorphicAt.mul ((hr r).1 s (Set.mem_univ s)))
    · exact Finset.analyticAt_fun_sum _ (fun r _ => (ha r 0).mul (hr r).2)
  exact hmer

theorem exists_transported_norm_one_cofactor :
    let μ : ∀ q : E, Measure (LocalField F q.val) := fun q =>
      Measure.addHaarMeasure (finiteCompletionIntegersPositiveCompacts F q.val)
    ∃ (φ : ∀ q : E, compactPicture (C.canonical q.val).borel (C.polarization q.val)
        (C.canonical q.val).iwasawa .plus)
      (t : KPGlobalTorusFunctionData.E F ζ hζ) (b : ℂ → ℂ),
      KPGlobalTorusFunctionData.delta F ζ hζ t = 1 ∧
      MeromorphicOn b Set.univ ∧ AnalyticAt ℂ b 0 ∧ b 0 ≠ 0 ∧
      (∀ s : ℂ, b s = ActualCofactor.rationalStageEval F ζ hζ P C E hE t
        (fun q => (localHalfDifferentFactor F q.val : ℂ) •
          (actualCanonicalContinued F q.val ζ hζ (C.canonical q.val) (C.polarization q.val)
            (μ q) (ActualCofactor.unit_mass F q.val) .plus s
            (FiniteSourceTransport.parameterSource (C.canonical q.val).borel
              (C.canonical q.val).iwasawa (J q) (C.polarization q.val) .plus (φ q) s)).val 1) *
        ∏ _w : NumberField.InfinitePlace F, 2 * (Real.pi : ℂ) / ((1/3 : ℂ) + 2*s)) := by
  dsimp only
  let μ : ∀ q : E, Measure (LocalField F q.val) := fun q =>
    Measure.addHaarMeasure (finiteCompletionIntegersPositiveCompacts F q.val)
  obtain ⟨φ,t,b₀,ht,hm₀,ha₀,hn₀,hb₀⟩ := NormOneCofactor.exists_norm_one_rational_cofactor F ζ hζ P C E hE
  let c (s : ℂ) := ActualCofactor.rationalStageEval F ζ hζ P C E hE t
    (fun q => (localHalfDifferentFactor F q.val : ℂ) •
      (actualCanonicalContinued F q.val ζ hζ (C.canonical q.val) (C.polarization q.val)
        (μ q) (ActualCofactor.unit_mass F q.val) .plus s
        (FiniteSourceTransport.parameterSource (C.canonical q.val).borel
          (C.canonical q.val).iwasawa (J q) (C.polarization q.val) .plus (φ q) s)).val 1)
  let a (s : ℂ) := ∏ _w : NumberField.InfinitePlace F, 2 * (Real.pi : ℂ) / ((1/3 : ℂ) + 2*s)
  let b (s : ℂ) := c s * a s
  have hc : MeromorphicOn c Set.univ ∧ AnalyticAt ℂ c 0 :=
    transported_family_regular F ζ hζ P C E hE J φ t
  have ha : MeromorphicOn a Set.univ := by
    intro s _
    have hprod : MeromorphicAt (∏ _w : NumberField.InfinitePlace F,
        (fun s : ℂ => 2 * (Real.pi : ℂ) / ((1/3 : ℂ) + 2*s))) s :=
      MeromorphicAt.prod (fun _ _ => analyticAt_const.meromorphicAt.div (by fun_prop))
    convert hprod using 1
    funext s
    simp only [a,Finset.prod_apply]
  have ha0 : AnalyticAt ℂ a 0 := by
    apply Finset.analyticAt_fun_prod
    intro w _
    exact analyticAt_const.div (by fun_prop) (by norm_num)
  refine ⟨φ,t,b,ht,fun s hs => (hc.1 s hs).mul (ha s hs),hc.2.mul ha0,?_,fun _ => rfl⟩
  have he : b 0 = b₀ 0 := by
    dsimp [b,c,a]
    simp_rw [FiniteSourceTransport.parameterSource_zero]
    exact (hb₀ 0).symm
  exact he.symm ▸ hn₀

open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.ActualCofactor renaming actual_arch_trace_spherical_parameter_integral → actual_arch_trace_spherical_parameter_integral

theorem exists_transported_integral_cofactor :
    ∃ (φ : ∀ q : E, compactPicture (C.canonical q.val).borel (C.polarization q.val)
        (C.canonical q.val).iwasawa .plus)
      (t : KPGlobalTorusFunctionData.E F ζ hζ) (b : ℂ → ℂ),
      KPGlobalTorusFunctionData.delta F ζ hζ t = 1 ∧
      MeromorphicOn b Set.univ ∧ AnalyticAt ℂ b 0 ∧ b 0 ≠ 0 ∧
      (∀ s : ℂ, -(1/6 : ℝ) < s.re →
        Integrable (fun x : ∀ q : E, LocalField F q.val =>
          ActualCofactor.rationalStageEval F ζ hζ P C E hE t
            (fun q => Complex.exp (s * (FiniteSourceTransport.localLogNorm
                (C.canonical q.val).borel (J q)
                ((C.canonical q.val).borel.liftedW⁻¹ * (C.canonical q.val).borel.upperRoot
                  (Multiplicative.ofAdd (x q)) * 1) : ℂ)) •
              (compactTrivialization (C.canonical q.val).borel (C.polarization q.val)
                (C.canonical q.val).iwasawa .plus 0 (φ q)).val
                ((C.canonical q.val).borel.liftedW⁻¹ * (C.canonical q.val).borel.upperRoot
                  (Multiplicative.ofAdd (x q)) * 1)))
          (Measure.pi (fun q : E => localNormalizedHaar F q.val)) ∧
        b s =
          (∫ x : ∀ q : E, LocalField F q.val,
            ActualCofactor.rationalStageEval F ζ hζ P C E hE t
              (fun q => Complex.exp (s * (FiniteSourceTransport.localLogNorm
                  (C.canonical q.val).borel (J q)
                  ((C.canonical q.val).borel.liftedW⁻¹ * (C.canonical q.val).borel.upperRoot
                    (Multiplicative.ofAdd (x q)) * 1) : ℂ)) •
                (compactTrivialization (C.canonical q.val).borel (C.polarization q.val)
                  (C.canonical q.val).iwasawa .plus 0 (φ q)).val
                  ((C.canonical q.val).borel.liftedW⁻¹ * (C.canonical q.val).borel.upperRoot
                    (Multiplicative.ofAdd (x q)) * 1))
            ∂(Measure.pi (fun q : E => localNormalizedHaar F q.val))) *
          ∏ _w : NumberField.InfinitePlace F, ∫ x : ℂ,
            KPComplexIntertwinerParameterMajorant.forwardSection s
              KPComplexStandardIntertwinerGerm.compactSpherical
              (KPCplxCharacterHaar.weyl * KPCplxCharacterHaar.upperUnipotent x * 1)
              ∂((2 : ℝ≥0∞) • KPCplxCharacterHaar.euclideanArea)) := by
  obtain ⟨φ,t,b,ht,hm,ha,hn,hb⟩ := exists_transported_norm_one_cofactor F ζ hζ P C E hE J
  refine ⟨φ,t,b,ht,hm,ha,hn,?_⟩
  intro s hs
  let ψ (q : E) := FiniteSourceTransport.parameterSource (C.canonical q.val).borel
    (C.canonical q.val).iwasawa (J q) (C.polarization q.val) .plus (φ q) s
  have hf := ActualCofactor.rational_finite_chamber_integral F ζ hζ P C E hE ψ t s hs
  have he (x : ∀ q : E, LocalField F q.val) := fun q : E =>
    FiniteSourceTransport.parameterSource_extension (C.canonical q.val).borel
      (C.canonical q.val).iwasawa (J q) (C.polarization q.val) .plus (φ q) s
      ((C.canonical q.val).borel.liftedW⁻¹ * (C.canonical q.val).borel.upperRoot
        (Multiplicative.ofAdd (x q)) * 1)
  have hfun : (fun x : ∀ q : E, LocalField F q.val => ActualCofactor.rationalStageEval F ζ hζ P C E hE t
      (fun q => (compactTrivialization (C.canonical q.val).borel (C.polarization q.val)
        (C.canonical q.val).iwasawa .plus s (ψ q)).val
        ((C.canonical q.val).borel.liftedW⁻¹ * (C.canonical q.val).borel.upperRoot
          (Multiplicative.ofAdd (x q)) * 1))) =
      (fun x : ∀ q : E, LocalField F q.val => ActualCofactor.rationalStageEval F ζ hζ P C E hE t
        (fun q => Complex.exp (s * (FiniteSourceTransport.localLogNorm
            (C.canonical q.val).borel (J q)
            ((C.canonical q.val).borel.liftedW⁻¹ * (C.canonical q.val).borel.upperRoot
              (Multiplicative.ofAdd (x q)) * 1) : ℂ)) •
          (compactTrivialization (C.canonical q.val).borel (C.polarization q.val)
            (C.canonical q.val).iwasawa .plus 0 (φ q)).val
            ((C.canonical q.val).borel.liftedW⁻¹ * (C.canonical q.val).borel.upperRoot
              (Multiplicative.ofAdd (x q)) * 1))) := by
    funext x
    congr 1
    funext q
    exact he x q
  rw [hfun] at hf
  refine ⟨hf.1,?_⟩
  rw [hb, hf.2]
  congr 1
  apply Finset.prod_congr rfl
  intro w _
  exact (actual_arch_trace_spherical_parameter_integral s hs).symm

end DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.TransportedRationalCofactor

end
