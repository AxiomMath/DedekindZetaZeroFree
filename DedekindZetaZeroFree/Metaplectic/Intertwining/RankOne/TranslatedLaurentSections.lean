module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.SectionIntegralConvergenceAndEquivariance

@[expose] public section

section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneTranslatedLevel
open scoped NumberField Valued
open NumberField IsDedekindDomain ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneShellRepair

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)

def translatedCompact (δ : Sign) (s : ℂ) (g : ActualCover F ζ hζ q)
    (φ : compactPicture S.borel P S.iwasawa δ) :
    compactPicture S.borel P S.iwasawa δ :=
  (compactTrivialization S.borel P S.iwasawa δ s).symm
    (principalSeries S.borel P δ s g
      (compactTrivialization S.borel P S.iwasawa δ s φ))

def translatedLevel (J : CompactOpenLevel (ActualCover F ζ hζ q))
    (g : ActualCover F ζ hζ q) : CompactOpenLevel (ActualCover F ζ hζ q) :=
  let U := J.toOpenSubgroup.comap (MulAut.conj g⁻¹).toMonoidHom
    (by change Continuous (fun x : ActualCover F ζ hζ q => g⁻¹ * x * (g⁻¹)⁻¹); fun_prop)
  ⟨U ⊓ S.iwasawa.compact.toOpenSubgroup,
    S.iwasawa.compact.isCompact.of_isClosed_subset
      (U ⊓ S.iwasawa.compact.toOpenSubgroup).isClosed (fun _ hx => hx.2)⟩

theorem actual_translate_uniform_level (δ : Sign)
    (J : CompactOpenLevel (ActualCover F ζ hζ q))
    (hJ : (J.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤ S.iwasawa.compact.toOpenSubgroup)
    (g : ActualCover F ζ hζ q) :
    ((translatedLevel F ζ hζ q S J g).toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤
      S.iwasawa.compact.toOpenSubgroup ∧
    ∀ (s : ℂ) (φ : compactLevel S.borel P S.iwasawa δ J),
      translatedCompact F ζ hζ q S P δ s g φ.val ∈
        compactLevel S.borel P S.iwasawa δ (translatedLevel F ζ hζ q S J g) := by
  refine ⟨fun _ hj => hj.2, ?_⟩
  intro s φ j k k' hk
  let f := compactTrivialization S.borel P S.iwasawa δ s φ.val
  have hf := (compact_level_identification S.borel P S.iwasawa δ J hJ s φ.val).mp φ.property
  let jg : J.toOpenSubgroup := ⟨g⁻¹ * (j : ActualCover F ζ hζ q) * g, by
    have hj := j.property.1
    change g⁻¹ * (j : ActualCover F ζ hζ q) * (g⁻¹)⁻¹ ∈ J.toOpenSubgroup at hj
    simpa only [inv_inv] using hj⟩
  have he := congrArg (fun v : sectionSpace S.borel P δ s => v.val ((k : ActualCover F ζ hζ q) * g)) (hf jg)
  change f.val ((k' : ActualCover F ζ hζ q) * g) = f.val ((k : ActualCover F ζ hζ q) * g)
  change f.val (((k : ActualCover F ζ hζ q) * g) * (jg : ActualCover F ζ hζ q)) = _ at he
  rw [hk]
  simpa [jg, mul_assoc] using he

private theorem exponent_invariant
    (b : S.borel.B) (hb : localAbs (LocalField F q) (S.borel.coordinate (S.borel.retract b)) = 1)
    (x y : ActualCover F ζ hζ q) (k₀ : S.iwasawa.compact.toOpenSubgroup)
    (he : y = (b : ActualCover F ζ hζ q) * x * k₀) :
    initialExponent F ζ hζ q S y = initialExponent F ζ hζ q S x := by
  let d : S.borel.B := (b * S.iwasawa.borelPart x)⁻¹ * S.iwasawa.borelPart y
  have hd : (d : ActualCover F ζ hζ q) =
      (S.iwasawa.compactPart x : ActualCover F ζ hζ q) * k₀ *
        (S.iwasawa.compactPart y : ActualCover F ζ hζ q)⁻¹ := by
    calc
      (d : ActualCover F ζ hζ q) =
          ((b * S.iwasawa.borelPart x : S.borel.B) : ActualCover F ζ hζ q)⁻¹ * y *
            (S.iwasawa.compactPart y : ActualCover F ζ hζ q)⁻¹ := by
        nth_rw 1 [S.iwasawa.decomposition y]
        simp [d, mul_assoc]
      _ = _ := by
        calc
          _ = ((b * S.iwasawa.borelPart x : S.borel.B) : ActualCover F ζ hζ q)⁻¹ *
            ((b : ActualCover F ζ hζ q) *
              ((S.iwasawa.borelPart x : ActualCover F ζ hζ q) * S.iwasawa.compactPart x) * k₀) *
            (S.iwasawa.compactPart y : ActualCover F ζ hζ q)⁻¹ := by
              congr 2
              rw [← S.iwasawa.decomposition x, ← he]
          _ = _ := by simp [mul_assoc]
  have hdK : (d : ActualCover F ζ hζ q) ∈ S.iwasawa.compact.toOpenSubgroup := by
    rw [hd]
    exact S.iwasawa.compact.toOpenSubgroup.mul_mem
      (S.iwasawa.compact.toOpenSubgroup.mul_mem (S.iwasawa.compactPart x).property k₀.property)
      (S.iwasawa.compact.toOpenSubgroup.inv_mem (S.iwasawa.compactPart y).property)
  have hn := S.iwasawa.intersection_norm d hdK
  have hby : S.iwasawa.borelPart y = (b * S.iwasawa.borelPart x) * d := by simp [d, mul_assoc]
  have ha : localAbs (LocalField F q)
      (S.borel.coordinate (S.borel.retract (S.iwasawa.borelPart y))) =
      localAbs (LocalField F q) (S.borel.coordinate (S.borel.retract (S.iwasawa.borelPart x))) := by
    rw [hby, map_mul, map_mul, localAbs_mul, hn, mul_one,
      map_mul, map_mul, localAbs_mul, hb, one_mul]
  have hq : (1 : ℝ) < residueCardinality (LocalField F q) := by
    exact_mod_cast (Finite.one_lt_card (α := IsLocalRing.ResidueField (valuation (LocalField F q)).integer))
  unfold localAbs at ha
  have hh := (Real.rpow_right_inj (by linarith :
      (0 : ℝ) < residueCardinality (LocalField F q)) (ne_of_gt hq)).mp ha
  unfold initialExponent
  congr 1
  exact_mod_cast hh

 def spectralValue (δ : Sign) (g : ActualCover F ζ hζ q)
    (φ : compactPicture S.borel P S.iwasawa δ) (n : ℤ)
    (k : S.iwasawa.compact.toOpenSubgroup) : InducedModule P :=
  if initialExponent F ζ hζ q S ((k : ActualCover F ζ hζ q) * g) = n
  then (translatedCompact F ζ hζ q S P δ 0 g φ).val k else 0

 theorem spectralValue_level (δ : Sign)
    (J : CompactOpenLevel (ActualCover F ζ hζ q))
    (hJ : (J.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤ S.iwasawa.compact.toOpenSubgroup)
    (g : ActualCover F ζ hζ q)
    (φ : compactLevel S.borel P S.iwasawa δ J) (n : ℤ)
    (j : (translatedLevel F ζ hζ q S J g).toOpenSubgroup)
    (k k' : S.iwasawa.compact.toOpenSubgroup)
    (hk : (k' : ActualCover F ζ hζ q) = (k : ActualCover F ζ hζ q) * j) :
    spectralValue F ζ hζ q S P δ g φ.val n k' = spectralValue F ζ hζ q S P δ g φ.val n k := by
  have hj := j.property.1
  change g⁻¹ * (j : ActualCover F ζ hζ q) * (g⁻¹)⁻¹ ∈ J.toOpenSubgroup at hj
  have hjg : g⁻¹ * (j : ActualCover F ζ hζ q) * g ∈ S.iwasawa.compact.toOpenSubgroup :=
    hJ (by
      change g⁻¹ * (j : ActualCover F ζ hζ q) * g ∈ J.toOpenSubgroup
      simpa only [inv_inv] using hj)
  have he := exponent_invariant F ζ hζ q S 1 (by simp [localAbs_one])
    ((k : ActualCover F ζ hζ q) * g) ((k' : ActualCover F ζ hζ q) * g)
    ⟨g⁻¹ * (j : ActualCover F ζ hζ q) * g, hjg⟩ (by simp [hk, mul_assoc])
  unfold spectralValue
  rw [he]
  split_ifs
  · exact (actual_translate_uniform_level F ζ hζ q S P δ J hJ g).2 0 φ j k k' hk
  · rfl

 theorem spectralValue_borel (δ : Sign) (g : ActualCover F ζ hζ q)
    (φ : compactPicture S.borel P S.iwasawa δ) (n : ℤ)
    (b : S.borel.B) (k k' : S.iwasawa.compact.toOpenSubgroup)
    (hk : (k' : ActualCover F ζ hζ q) = (b : ActualCover F ζ hζ q) * k) :
    spectralValue F ζ hζ q S P δ g φ n k' =
      inducingAction S.borel P δ 0 b (spectralValue F ζ hζ q S P δ g φ n k) := by
  have hb : (b : ActualCover F ζ hζ q) ∈ S.iwasawa.compact.toOpenSubgroup := by
    rw [show (b : ActualCover F ζ hζ q) =
      (k' : ActualCover F ζ hζ q) * (k : ActualCover F ζ hζ q)⁻¹ by rw [hk, mul_inv_cancel_right]]
    exact S.iwasawa.compact.toOpenSubgroup.mul_mem k'.property
      (S.iwasawa.compact.toOpenSubgroup.inv_mem k.property)
  have he := exponent_invariant F ζ hζ q S b (S.iwasawa.intersection_norm b hb)
    ((k : ActualCover F ζ hζ q) * g) ((k' : ActualCover F ζ hζ q) * g) 1 (by simp [hk, mul_assoc])
  unfold spectralValue
  rw [he]
  split_ifs
  · exact (translatedCompact F ζ hζ q S P δ 0 g φ).property.1 b k k' hk
  · exact (map_zero _).symm

 def spectralVector (δ : Sign)
    (J : CompactOpenLevel (ActualCover F ζ hζ q))
    (hJ : (J.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤ S.iwasawa.compact.toOpenSubgroup)
    (g : ActualCover F ζ hζ q) (φ : compactLevel S.borel P S.iwasawa δ J) (n : ℤ) :
    compactLevel S.borel P S.iwasawa δ (translatedLevel F ζ hζ q S J g) := by
  let v := spectralValue F ζ hζ q S P δ g φ.val n
  have hlev := spectralValue_level F ζ hζ q S P δ J hJ g φ n
  have hsm : SmoothVector (vectorRightTranslation (G := S.iwasawa.compact.toOpenSubgroup)) v := by
    refine ⟨(translatedLevel F ζ hζ q S J g).toOpenSubgroup.comap
      S.iwasawa.compact.toOpenSubgroup.toSubgroup.subtype continuous_subtype_val, ?_⟩
    intro j hj
    funext k
    exact hlev ⟨j, hj⟩ k (k * j) rfl
  exact ⟨⟨v, spectralValue_borel F ζ hζ q S P δ g φ.val n, hsm⟩, hlev⟩

private theorem translated_monomial (ε : Sign) (g : ActualCover F ζ hζ q)
    (φ : compactPicture S.borel P S.iwasawa (sourceSign ε))
    (s : ℂ) (k : S.iwasawa.compact.toOpenSubgroup) :
    (translatedCompact F ζ hζ q S P (sourceSign ε) (sourceParameter ε s) g φ).val k =
      (evaluationUnit (LocalField F q) ε s : ℂ) ^
        initialExponent F ζ hζ q S ((k : ActualCover F ζ hζ q) * g) •
      (translatedCompact F ζ hζ q S P (sourceSign ε) 0 g φ).val k := by
  apply Subtype.ext
  funext h
  change ((compactTrivialization S.borel P S.iwasawa (sourceSign ε) (sourceParameter ε s) φ).val
    ((k : ActualCover F ζ hζ q) * g)).val h = _
  rw [initialCoordinate_monomial F ζ hζ q S P ε φ]
  have hz := initialCoordinate_monomial F ζ hζ q S P ε φ
    ((k : ActualCover F ζ hζ q) * g) h 0
  have hu : (evaluationUnit (LocalField F q) ε 0 : ℂ) = 1 := by
    cases ε <;> simp [evaluationUnit, KPRankOneRootParameter.rUnit, KPRankOneRootParameter.r]
  rw [hu, one_zpow, mul_one] at hz
  simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  change _ = (evaluationUnit (LocalField F q) ε s : ℂ) ^ _ *
    (((compactTrivialization S.borel P S.iwasawa (sourceSign ε) 0 φ).val
      ((k : ActualCover F ζ hζ q) * g)).val h)
  have hs0 : sourceParameter ε (0 : ℂ) = 0 := by cases ε <;> simp [sourceParameter]
  rw [hs0] at hz
  rw [hz]
  exact mul_comm _ _

theorem actual_translate_finite_laurent
    (J : CompactOpenLevel (ActualCover F ζ hζ q))
    (hJ : (J.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤ S.iwasawa.compact.toOpenSubgroup)
    (ε : Sign) (g : ActualCover F ζ hζ q)
    (φ : compactLevel S.borel P S.iwasawa (sourceSign ε) J) :
    ∃ (N : Finset ℤ)
      (v : ℤ → compactLevel S.borel P S.iwasawa (sourceSign ε) (translatedLevel F ζ hζ q S J g)),
      ∀ s : ℂ,
        translatedCompact F ζ hζ q S P (sourceSign ε) (sourceParameter ε s) g φ.val =
          ∑ n ∈ N, (evaluationUnit (LocalField F q) ε s : ℂ) ^ n • (v n).val := by
  classical
  let C : Set (ActualCover F ζ hζ q) :=
    (fun k : ActualCover F ζ hζ q => k * g) '' (S.iwasawa.compact.toOpenSubgroup : Set (ActualCover F ζ hζ q))
  have hC : IsCompact C := S.iwasawa.compact.isCompact.image (continuous_id.mul continuous_const)
  let hN := initialExponent_finite_on_compact F ζ hζ q S C hC
  let N := hN.toFinset
  refine ⟨N, spectralVector F ζ hζ q S P (sourceSign ε) J hJ g φ, ?_⟩
  intro s
  apply Subtype.ext
  funext k
  rw [translated_monomial F ζ hζ q S P ε g φ.val s k]
  have hn : initialExponent F ζ hζ q S ((k : ActualCover F ζ hζ q) * g) ∈ N := by
    apply hN.mem_toFinset.mpr
    exact ⟨(k : ActualCover F ζ hζ q) * g, ⟨k, k.property, rfl⟩, rfl⟩
  change _ = (∑ n ∈ N, (evaluationUnit (LocalField F q) ε s : ℂ) ^ n •
    (spectralVector F ζ hζ q S P (sourceSign ε) J hJ g φ n).val).val k
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply]
  rw [Finset.sum_eq_single (initialExponent F ζ hζ q S ((k : ActualCover F ζ hζ q) * g))]
  · simp [spectralVector, spectralValue]
  · intro n hn hne
    simp [spectralVector, spectralValue, Ne.symm hne]
  · exact fun h => (h hn).elim

end DedekindZetaZeroFree.KPRankOneTranslatedLevel

end

end

section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneTranslatedMeromorphy
open scoped NumberField Valued
open NumberField IsDedekindDomain ValuativeRel MeasureTheory
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneRootParameter KPRankOneShellRepair
open KPRankOneTranslatedLevel

private theorem unit_diff (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (ε : Sign) :
    Differentiable ℂ (fun s => (evaluationUnit K ε s : ℂ)) := by
  have hr : Differentiable ℂ (r K) := by unfold r; fun_prop
  cases ε with
  | plus => exact hr
  | minus => exact hr.inv (fun s => Complex.exp_ne_zero _)

private theorem denominator_diff (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (ε : Sign) :
    Differentiable ℂ (denominator K ε) := by
  cases ε with
  | plus => unfold denominator t r; simp only [if_pos rfl, if_true]; fun_prop
  | minus =>
    unfold denominator
    simp only [reduceCtorEq, if_false]
    apply Differentiable.sub (differentiable_const _)
    apply Differentiable.mul (differentiable_const _)
    apply Differentiable.pow
    exact (show Differentiable ℂ (r K) by unfold r; fun_prop).inv
      (fun s => Complex.exp_ne_zero _)

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
  (π : (LocalField F q)ˣ)
  (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
    (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))

private theorem level_coordinate_formula (J : CompactOpenLevel (ActualCover F ζ hζ q))
    (ε : Sign) (p : LevelLaurentOperator (LocalField F q) S.borel P S.iwasawa J ε)
    (φ : compactLevel S.borel P S.iwasawa (sourceSign ε) J)
    (k : S.iwasawa.compact.toOpenSubgroup) (h : actualTorus F ζ hζ q) (s : ℂ) :
    ((continuedLevel (LocalField F q) S.borel P S.iwasawa J ε p s φ).val.val k).val h =
      (denominator (LocalField F q) ε s)⁻¹ * ∑ n ∈ p.support,
        (evaluationUnit (LocalField F q) ε s : ℂ) ^ n * (((p n) φ).val.val k).val h := by
  classical
  simp only [continuedLevel, evaluate, Finsupp.sum, LinearMap.smul_apply,
    Submodule.coe_smul, Submodule.coe_sum, LinearMap.sum_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

private theorem level_numerator_diff (J : CompactOpenLevel (ActualCover F ζ hζ q))
    (ε : Sign) (p : LevelLaurentOperator (LocalField F q) S.borel P S.iwasawa J ε)
    (φ : compactLevel S.borel P S.iwasawa (sourceSign ε) J)
    (k : S.iwasawa.compact.toOpenSubgroup) (h : actualTorus F ζ hζ q) :
    Differentiable ℂ (fun s => ∑ n ∈ p.support,
      (evaluationUnit (LocalField F q) ε s : ℂ) ^ n * (((p n) φ).val.val k).val h) := by
  classical
  apply Differentiable.fun_sum
  intro n hn
  exact ((unit_diff (LocalField F q) ε).zpow (Or.inl (fun s => Units.ne_zero _))).mul
    (differentiable_const _)

theorem actual_coordinate_regular (ε : Sign)
    (φ : compactPicture S.borel P S.iwasawa (sourceSign ε))
    (k : S.iwasawa.compact.toOpenSubgroup) (h : actualTorus F ζ hζ q) :
    (Meromorphic (fun s : ℂ => ((actualContinued F ζ hζ q S P μ hμ π hπ ε s φ).val k).val h)) ∧
    (∀ s₀, denominator (LocalField F q) ε s₀ ≠ 0 →
      DifferentiableAt ℂ (fun s : ℂ => ((actualContinued F ζ hζ q S P μ hμ π hπ ε s φ).val k).val h) s₀) := by
  obtain ⟨J, hJ, hφ⟩ := actual_common_level F ζ hζ q S P (sourceSign ε) φ
  let p := actualLevelNumerator F ζ hζ q S P J hJ μ hμ π hπ ε
  have he (s : ℂ) : ((actualContinued F ζ hζ q S P μ hμ π hπ ε s φ).val k).val h =
      (denominator (LocalField F q) ε s)⁻¹ * ∑ n ∈ p.support,
        (evaluationUnit (LocalField F q) ε s : ℂ) ^ n * (((p n) ⟨φ, hφ⟩).val.val k).val h := by
    rw [actualContinued_eq_level F ζ hζ q S P μ hμ π hπ ε s J hJ ⟨φ, hφ⟩]
    exact level_coordinate_formula F ζ hζ q S P J ε p ⟨φ, hφ⟩ k h s
  simp_rw [he]
  have hd := denominator_diff (LocalField F q) ε
  have hn := level_numerator_diff F ζ hζ q S P J ε p ⟨φ, hφ⟩ k h
  constructor
  · intro s₀
    exact (hd.analyticAt s₀).meromorphicAt.inv.mul (hn.analyticAt s₀).meromorphicAt
  · intro s₀ hs₀
    exact ((hd.differentiableAt).inv hs₀).mul hn.differentiableAt

private theorem translated_continued_compact_regular (ε : Sign) (g : ActualCover F ζ hζ q)
    (φ : compactPicture S.borel P S.iwasawa (sourceSign ε))
    (k : S.iwasawa.compact.toOpenSubgroup) (h : actualTorus F ζ hζ q) :
    (Meromorphic (fun s : ℂ => ((actualContinued F ζ hζ q S P μ hμ π hπ ε s
      (translatedCompact F ζ hζ q S P (sourceSign ε) (sourceParameter ε s) g φ)).val k).val h)) ∧
    (∀ s₀, denominator (LocalField F q) ε s₀ ≠ 0 →
      DifferentiableAt ℂ (fun s : ℂ => ((actualContinued F ζ hζ q S P μ hμ π hπ ε s
        (translatedCompact F ζ hζ q S P (sourceSign ε) (sourceParameter ε s) g φ)).val k).val h) s₀) := by
  classical
  obtain ⟨J, hJ, hφ⟩ := actual_common_level F ζ hζ q S P (sourceSign ε) φ
  obtain ⟨N, v, hp⟩ := actual_translate_finite_laurent F ζ hζ q S P J hJ ε g ⟨φ, hφ⟩
  have he (s : ℂ) : ((actualContinued F ζ hζ q S P μ hμ π hπ ε s
      (translatedCompact F ζ hζ q S P (sourceSign ε) (sourceParameter ε s) g φ)).val k).val h =
      ∑ n ∈ N, (evaluationUnit (LocalField F q) ε s : ℂ) ^ n *
        ((actualContinued F ζ hζ q S P μ hμ π hπ ε s (v n).val).val k).val h := by
    rw [hp]
    let l : compactPicture S.borel P S.iwasawa (targetSign ε) →ₗ[ℂ] ℂ :=
      { toFun := fun v => (v.val k).val h
        map_add' := by intros; rfl
        map_smul' := by intros; rfl }
    change l (actualContinued F ζ hζ q S P μ hμ π hπ ε s
      (∑ n ∈ N, (evaluationUnit (LocalField F q) ε s : ℂ) ^ n • (v n).val)) = _
    simp only [Finsupp.sum, map_sum, map_smul, smul_eq_mul]
    rfl
  simp_rw [he]
  constructor
  · intro s₀
    rw [show (fun s : ℂ => ∑ n ∈ N, (evaluationUnit (LocalField F q) ε s : ℂ) ^ n *
        ((actualContinued F ζ hζ q S P μ hμ π hπ ε s (v n).val).val k).val h) =
      ∑ n ∈ N, (fun s : ℂ => (evaluationUnit (LocalField F q) ε s : ℂ) ^ n *
        ((actualContinued F ζ hζ q S P μ hμ π hπ ε s (v n).val).val k).val h) by
      funext s; simp only [Finset.sum_apply]]
    apply MeromorphicAt.sum
    intro n hn
    have hu := ((unit_diff (LocalField F q) ε).zpow (m := n)
      (Or.inl (fun s => Units.ne_zero _))).analyticAt s₀
    exact hu.meromorphicAt.mul ((actual_coordinate_regular F ζ hζ q S P μ hμ π hπ ε
      (v n).val k h).1 s₀)
  · intro s₀ hs₀
    apply DifferentiableAt.fun_sum
    intro n hn
    exact (((unit_diff (LocalField F q) ε).zpow (Or.inl (fun s => Units.ne_zero _))).differentiableAt).mul
      ((actual_coordinate_regular F ζ hζ q S P μ hμ π hπ ε (v n).val k h).2 s₀ hs₀)

 theorem section_coordinate_formula (ε : Sign) (s : ℂ)
    (v : compactPicture S.borel P S.iwasawa (targetSign ε))
    (x : ActualCover F ζ hζ q) (h : actualTorus F ζ hζ q) :
    ((compactTrivialization S.borel P S.iwasawa (targetSign ε) (targetParameter ε s) v).val x).val h =
      inducingScalar S.borel (targetParameter ε s) (S.iwasawa.borelPart x) *
        (v.val (S.iwasawa.compactPart x)).val
          (h * (if targetSign ε = .plus then S.borel.retract (S.iwasawa.borelPart x)
            else S.borel.weyl (S.borel.retract (S.iwasawa.borelPart x)))) := by
  cases ε <;> rfl

 theorem target_scalar_diff (ε : Sign) (b : S.borel.B) :
    Differentiable ℂ (fun s => inducingScalar S.borel (targetParameter ε s) b) := by
  cases ε <;> unfold targetParameter sourceParameter inducingScalar normPower <;>
    simp only [if_true, reduceCtorEq, if_false, neg_neg] <;> fun_prop

theorem continued_section_regular (ε : Sign)
    (φ : compactPicture S.borel P S.iwasawa (sourceSign ε))
    (x : ActualCover F ζ hζ q) (h : actualTorus F ζ hζ q) :
    (Meromorphic (fun s : ℂ =>
      ((transportToSections (LocalField F q) S.borel P S.iwasawa ε s
        (actualContinued F ζ hζ q S P μ hμ π hπ ε s)
        (compactTrivialization S.borel P S.iwasawa (sourceSign ε) (sourceParameter ε s) φ)).val x).val h)) ∧
    (∀ s₀, denominator (LocalField F q) ε s₀ ≠ 0 →
      ContinuousAt (fun s : ℂ =>
        ((transportToSections (LocalField F q) S.borel P S.iwasawa ε s
          (actualContinued F ζ hζ q S P μ hμ π hπ ε s)
          (compactTrivialization S.borel P S.iwasawa (sourceSign ε) (sourceParameter ε s) φ)).val x).val h) s₀) := by
  have he (s : ℂ) : ((transportToSections (LocalField F q) S.borel P S.iwasawa ε s
      (actualContinued F ζ hζ q S P μ hμ π hπ ε s)
      (compactTrivialization S.borel P S.iwasawa (sourceSign ε) (sourceParameter ε s) φ)).val x).val h =
      inducingScalar S.borel (targetParameter ε s) (S.iwasawa.borelPart x) *
        ((actualContinued F ζ hζ q S P μ hμ π hπ ε s φ).val (S.iwasawa.compactPart x)).val
          (h * (if targetSign ε = .plus then S.borel.retract (S.iwasawa.borelPart x)
            else S.borel.weyl (S.borel.retract (S.iwasawa.borelPart x)))) := by
    unfold transportToSections
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    exact section_coordinate_formula F ζ hζ q S P ε s _ x h
  simp_rw [he]
  have hc := actual_coordinate_regular F ζ hζ q S P μ hμ π hπ ε φ
    (S.iwasawa.compactPart x) (h * (if targetSign ε = .plus then S.borel.retract (S.iwasawa.borelPart x)
      else S.borel.weyl (S.borel.retract (S.iwasawa.borelPart x))))
  have hd := target_scalar_diff F ζ hζ q S ε (S.iwasawa.borelPart x)
  exact ⟨fun s₀ => (hd.analyticAt s₀).meromorphicAt.mul (hc.1 s₀),
    fun s₀ hs₀ => (hd.differentiableAt.mul (hc.2 s₀ hs₀)).continuousAt⟩

theorem translated_continued_section_regular (ε : Sign)
    (φ : compactPicture S.borel P S.iwasawa (sourceSign ε))
    (g x : ActualCover F ζ hζ q) (h : actualTorus F ζ hζ q) :
    (Meromorphic (fun s : ℂ =>
      ((transportToSections (LocalField F q) S.borel P S.iwasawa ε s
        (actualContinued F ζ hζ q S P μ hμ π hπ ε s)
        (principalSeries S.borel P (sourceSign ε) (sourceParameter ε s) g
          (compactTrivialization S.borel P S.iwasawa (sourceSign ε) (sourceParameter ε s) φ))).val x).val h)) ∧
    (∀ s₀, denominator (LocalField F q) ε s₀ ≠ 0 →
      ContinuousAt (fun s : ℂ =>
        ((transportToSections (LocalField F q) S.borel P S.iwasawa ε s
          (actualContinued F ζ hζ q S P μ hμ π hπ ε s)
          (principalSeries S.borel P (sourceSign ε) (sourceParameter ε s) g
            (compactTrivialization S.borel P S.iwasawa (sourceSign ε) (sourceParameter ε s) φ))).val x).val h) s₀) := by
  have he (s : ℂ) : ((transportToSections (LocalField F q) S.borel P S.iwasawa ε s
      (actualContinued F ζ hζ q S P μ hμ π hπ ε s)
      (principalSeries S.borel P (sourceSign ε) (sourceParameter ε s) g
        (compactTrivialization S.borel P S.iwasawa (sourceSign ε) (sourceParameter ε s) φ))).val x).val h =
      inducingScalar S.borel (targetParameter ε s) (S.iwasawa.borelPart x) *
        ((actualContinued F ζ hζ q S P μ hμ π hπ ε s
          (translatedCompact F ζ hζ q S P (sourceSign ε) (sourceParameter ε s) g φ)).val (S.iwasawa.compactPart x)).val
          (h * (if targetSign ε = .plus then S.borel.retract (S.iwasawa.borelPart x)
            else S.borel.weyl (S.borel.retract (S.iwasawa.borelPart x)))) := by
    unfold transportToSections
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    exact section_coordinate_formula F ζ hζ q S P ε s _ x h
  simp_rw [he]
  have hc := translated_continued_compact_regular F ζ hζ q S P μ hμ π hπ ε g φ
    (S.iwasawa.compactPart x) (h * (if targetSign ε = .plus then S.borel.retract (S.iwasawa.borelPart x)
      else S.borel.weyl (S.borel.retract (S.iwasawa.borelPart x))))
  have hd := target_scalar_diff F ζ hζ q S ε (S.iwasawa.borelPart x)
  exact ⟨fun s₀ => (hd.analyticAt s₀).meromorphicAt.mul (hc.1 s₀),
    fun s₀ hs₀ => (hd.differentiableAt.mul (hc.2 s₀ hs₀)).continuousAt⟩

end DedekindZetaZeroFree.KPRankOneTranslatedMeromorphy

end

end
