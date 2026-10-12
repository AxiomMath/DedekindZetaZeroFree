module

public import DedekindZetaZeroFree.CharacterSums.Gauss.SexticPairPhaseCancellation
public import DedekindZetaZeroFree.CharacterSums.Gauss.MaskedProductChineseRemainder

@[expose] public section

section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.GaussProductCancellation
noncomputable section
set_option autoImplicit false
variable {F : Type} [Field F] [NumberField F]

 def assemblyPhase (A : SArithmeticData F) (σ : F →+* ℂ) (p : A.Exterior) (x : A.R) : ℂ :=
  σ (A.sexticResidue p x)
private theorem assemblyPhase_mul (A : SArithmeticData F) (σ : F →+* ℂ) (p : A.Exterior) (x y : A.R) :
    assemblyPhase A σ p (x * y) = assemblyPhase A σ p x * assemblyPhase A σ p y := by
  unfold assemblyPhase SArithmeticData.sexticResidue SArithmeticData.residueValue
  simp only [map_mul]

variable {ι : Type*}
 def productExterior (A : SArithmeticData F) (p : ι → A.Exterior)
    (T : Finset ι) : A.Exterior :=
  ⟨∏ v ∈ T, (p v).val, by
    refine ⟨Finset.prod_ne_zero_iff.mpr (fun v _ => (p v).property.1), ?_⟩
    exact Ideal.prod_sup_eq_top (fun v _ => (p v).property.2)⟩
private theorem productExterior_generates (A : SArithmeticData F) (p : ι → A.Exterior)
    (π : ι → A.R) (hπ : ∀ v, A.Generates (p v) (π v)) (T : Finset ι) :
    A.Generates (productExterior A p T) (∏ v ∈ T, π v) := by
  refine ⟨Finset.prod_ne_zero_iff.mpr (fun v _ => (hπ v).1), ?_⟩
  rw [← Ideal.prod_span_singleton]
  simp_rw [(hπ _).2]
  change (∏ v ∈ T, A.extendIdeal (p v)) = _
  simp only [SArithmeticData.extendIdeal, productExterior]
  exact (map_prod (Ideal.mapHom (algebraMap (𝓞 F) A.R)) _ _).symm
private theorem assemblyPhase_modulus_prod (A : SArithmeticData F) (σ : F →+* ℂ)
    (p : ι → A.Exterior) (T : Finset ι) (x : A.R) :
    assemblyPhase A σ (productExterior A p T) x =
      ∏ v ∈ T, assemblyPhase A σ (p v) x := by
  induction T using Finset.induction_on with
  | empty =>
    unfold assemblyPhase SArithmeticData.sexticResidue
    rw [A.residueValue_top A.sexticResidueFamily _ (by simp [productExterior])]
    simp
  | @insert a T ha ih =>
    have hh : (productExterior A p (insert a T)).val =
        (p a).val * (productExterior A p T).val := by
      simp [productExterior, Finset.prod_insert, ha]
    change σ (A.residueValue A.sexticResidueFamily _ x) = _
    rw [A.sexticResidueFamily_normalized.2.2 (p a) (productExterior A p T) _ hh x,
      map_mul]
    change assemblyPhase A σ (p a) x * assemblyPhase A σ (productExterior A p T) x = _
    rw [ih, Finset.prod_insert ha]

private theorem assembly_finite_support_crt (A : SArithmeticData F) (σ : F →+* ℂ)
    (hS : A.ContainsTraceBadPlaces) (p : ι → A.Exterior)
    (π : ι → A.R) (hπ : ∀ v, A.Generates (p v) (π v)) (T : Finset ι)
    (hSquare : Squarefree (∏ v ∈ T, (p v).val))
    (hcop : ∀ v ∈ T, ∀ w ∈ T, v ≠ w → (p v).val ⊔ (p w).val = ⊤)
    (I : A.Exterior) (hI : I.val = ∏ v ∈ T, (p v).val)
    (hgen : A.Generates I (∏ v ∈ T, π v)) :
    A.idealGauss σ hS I (∏ v ∈ T, π v) hgen 2 =
      (∏ v ∈ T, A.idealGauss σ hS (p v) (π v) (hπ v) 2) *
      (∏ v ∈ T, assemblyPhase A σ (p v) (∏ w ∈ T.erase v, π w) ^ 2) := by
  have hIE : I = productExterior A p T := Subtype.ext hI
  subst I
  clear hI
  induction T using Finset.induction_on with
  | empty =>
    have ht : (productExterior A p ∅).val = ⊤ := by simp [productExterior]
    simpa using A.idealGauss_top σ hS (productExterior A p ∅) ht _ hgen 2
  | @insert a T ha ih =>
    have hPa : Squarefree (p a).val := hSquare.squarefree_of_dvd
      (by simp only [Finset.prod_insert ha]; exact dvd_mul_right _ _)
    have hPT : Squarefree (∏ v ∈ T, (p v).val) := hSquare.squarefree_of_dvd
      (by simp only [Finset.prod_insert ha]; exact dvd_mul_left _ _)
    have hcopT : ∀ v ∈ T, ∀ w ∈ T, v ≠ w → (p v).val ⊔ (p w).val = ⊤ :=
      fun v hv w hw => hcop v (Finset.mem_insert_of_mem hv) w (Finset.mem_insert_of_mem hw)
    have hcopA : (p a).val ⊔ (productExterior A p T).val = ⊤ := by
      apply Ideal.sup_prod_eq_top
      intro v hv
      exact hcop a (Finset.mem_insert_self _ _) v (Finset.mem_insert_of_mem hv)
        (fun he => ha (he ▸ hv))
    have hmul : (productExterior A p (insert a T)).val =
        (p a).val * (productExterior A p T).val := by
      simp [productExterior, Finset.prod_insert ha]
    have hgenT := productExterior_generates A p π hπ T
    have hgenAT : A.Generates (productExterior A p (insert a T))
        (π a * ∏ v ∈ T, π v) := by simpa only [Finset.prod_insert ha] using hgen
    have hcrt := A.idealGauss_squarefree_crt σ hS (p a) (productExterior A p T)
      (productExterior A p (insert a T)) hPa hPT hcopA hmul (π a) _ (hπ a) hgenT hgenAT 2
    norm_num [SArithmeticData.sexticExponent] at hcrt
    have hi := ih hPT hcopT hgenT
    have hexpand :
        (∏ v ∈ insert a T, assemblyPhase A σ (p v) (∏ w ∈ (insert a T).erase v, π w) ^ 2) =
        assemblyPhase A σ (p a) (∏ w ∈ T, π w) ^ 2 *
          ((∏ v ∈ T, assemblyPhase A σ (p v) (π a) ^ 2) *
            (∏ v ∈ T, assemblyPhase A σ (p v) (∏ w ∈ T.erase v, π w) ^ 2)) := by
      rw [Finset.prod_insert ha]
      simp only [Finset.erase_insert ha]
      congr 1
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro v hv
      have hva : v ≠ a := fun he => ha (he ▸ hv)
      rw [Finset.erase_insert_of_ne hva.symm, Finset.prod_insert (fun hh => ha (Finset.mem_of_mem_erase hh)),
        assemblyPhase_mul, mul_pow]
    rw [hexpand]
    simp only [Finset.prod_insert ha]
    rw [hcrt, hi]
    change assemblyPhase A σ (p a) (∏ v ∈ T, π v) ^ 2 *
      assemblyPhase A σ (productExterior A p T) (π a) ^ 2 * _ * _ = _
    rw [assemblyPhase_modulus_prod]
    simp only [Finset.prod_pow]
    ring

private theorem assembly_finite_support_reciprocal
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    [LocallyFiniteOrderTop ι] [LocallyFiniteOrderBot ι]
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (G : A.GaussCorrectionOutput σ η hS)
    (p : ι → A.Exterior) (π : ι → A.R)
    (hπ : ∀ v, A.Generates (p v) (π v))
    (aπ : ι → Fˣ) (haπ : ∀ v, (aπ v : F) = (π v : F))
    (hπAllowed : ∀ v, A.IsAllowed G.B (aπ v))
    (hcop : ∀ v w, v ≠ w → (p v).val ⊔ (p w).val = ⊤)
    (I : A.Exterior) (hI : I.val = ∏ v, (p v).val)
    (hSquare : Squarefree I.val)
    (hgen : A.Generates I (∏ v, π v)) :
    A.idealGauss σ hS I (∏ v, π v) hgen 2 =
      (∏ v, A.idealGauss σ hS (p v) (π v) (hπ v) 2) *
      (∏ v, ∏ w ∈ Finset.Ioi v, assemblyPhase A σ (p v) (π w) ^ 4) := by
  classical
  have hraw := assembly_finite_support_crt A σ hS p π hπ Finset.univ
    (hI ▸ hSquare) (fun v _ w _ => hcop v w) I hI hgen
  rw [hraw]
  congr 1
  letI : DecidableEq ι := Classical.decEq ι
  have hnum : ∀ v, assemblyPhase A σ (p v) (∏ w ∈ Finset.univ.erase v, π w) ^ 2 =
      ∏ w ∈ ({v}ᶜ : Finset ι), assemblyPhase A σ (p v) (π w) ^ 2 := by
    intro v
    unfold assemblyPhase SArithmeticData.sexticResidue SArithmeticData.residueValue
    simp only [map_prod, Finset.prod_pow]
    have hs : Finset.univ.erase v = ({v}ᶜ : Finset ι) := by ext w; simp
    rw [hs]
  calc
    (∏ v, assemblyPhase A σ (p v) (∏ w ∈ Finset.univ.erase v, π w) ^ 2) =
        (∏ v, ∏ w ∈ ({v}ᶜ : Finset ι), assemblyPhase A σ (p v) (π w) ^ 2) :=
      Finset.prod_congr rfl (fun v _ => hnum v)
    _ = _ := by
      have hcomb := Finset.prod_prod_Ioi_mul_eq_prod_prod_off_diag
        (fun v w => assemblyPhase A σ (p w) (π v) ^ 2)
      have hcomb' :
          (∏ v, ∏ w ∈ Finset.Ioi v,
            assemblyPhase A σ (p v) (π w) ^ 2 * assemblyPhase A σ (p w) (π v) ^ 2) =
          (∏ v, ∏ w ∈ ({v}ᶜ : Finset ι), assemblyPhase A σ (p v) (π w) ^ 2) := by
        refine hcomb.trans ?_
        apply Finset.prod_congr rfl
        intro v _
        apply Finset.prod_congr
        · ext w; simp
        · intro w _; rfl
      rw [← hcomb']
      apply Finset.prod_congr rfl
      intro v _
      apply Finset.prod_congr rfl
      intro w hw
      have hvw : v ≠ w := ne_of_lt (Finset.mem_Ioi.mp hw)
      have hrec := (ArithmeticContext.actual_hilbert_sextic_reciprocity
        A G.H G.B G.H_actual G.B_complement).1 (p v) (p w) (π v) (π w)
        (aπ v) (aπ w) (hπ v) (hπ w) (haπ v) (haπ w)
        (hπAllowed v) (hπAllowed w) (hcop v w hvw)
      have he : assemblyPhase A σ (p v) (π w) = assemblyPhase A σ (p w) (π v) :=
        congrArg σ hrec
      rw [← he]
      ring

theorem gauss_product_assembly
    (A : SArithmeticData F) (hCl : Subsingleton (ClassGroup A.R)) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (G : A.GaussCorrectionOutput σ η hS)
    (c : ExteriorSquarefreeIdeal A.cS) (a : A.R) (ha : A.Generates c.val a)
    (ac : Fˣ) (hac : (ac : F) = (a : F)) (hcAllowed : A.IsAllowed G.B ac)
    (P : Finset (HeightOneSpectrum (𝓞 F)))
    [LinearOrder P] [LocallyFiniteOrderTop P] [LocallyFiniteOrderBot P]
    (p : P → A.Exterior) (hp : ∀ v : P, (p v).val = v.val.asIdeal)
    (π : P → A.R) (hπ : ∀ v : P, A.Generates (p v) (π v))
    (aπ : P → Fˣ) (haπ : ∀ v : P, (aπ v : F) = (π v : F))
    (hπAllowed : ∀ v : P, A.IsAllowed G.B (aπ v))
    (hSupport : c.val.val =
      ∏ v : P, v.val.asIdeal ^ idealPrimeExponent v.val.asIdeal c.val.val) :
    A.idealGauss σ hS c.val a ha 2 =
      (∏ v : P, A.idealGauss σ hS (p v) (π v) (hπ v) 2 ^
        idealPrimeExponent v.val.asIdeal c.val.val) *
      (∏ v : P, ∏ w ∈ Finset.Ioi v,
        σ (A.sexticResidue (p v) (π w)) ^
          (4 * idealPrimeExponent v.val.asIdeal c.val.val *
            idealPrimeExponent w.val.asIdeal c.val.val)) := by
  classical
  let e : P → ℕ := fun v => idealPrimeExponent v.val.asIdeal c.val.val
  have he : ∀ v, e v = 0 ∨ e v = 1 := by
    intro v
    have hh := Multiset.nodup_iff_count_le_one.mp
      ((UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors c.val.property.1).mp
        c.property) v.val.asIdeal
    change e v ≤ 1 at hh
    omega
  let q : P → A.Exterior := fun v => if e v = 0 then (exteriorSquarefreeTop A.cS).val else p v
  let ρ : P → A.R := fun v => if e v = 0 then 1 else π v
  let b : P → Fˣ := fun v => if e v = 0 then 1 else aπ v
  have hρ : ∀ v, A.Generates (q v) (ρ v) := by
    intro v
    rcases he v with hz | ho
    · simp only [q, ρ, hz, ↓reduceIte]
      constructor
      · exact one_ne_zero
      · simp [SArithmeticData.extendIdeal, exteriorSquarefreeTop, Ideal.map_top]
    · simpa [q, ρ, ho] using hπ v
  have hb : ∀ v, (b v : F) = (ρ v : F) := by
    intro v
    rcases he v with hz | ho
    · simp [b, ρ, hz]
    · simpa [b, ρ, ho] using haπ v
  have hbAllowed : ∀ v, A.IsAllowed G.B (b v) := by
    intro v
    rcases he v with hz | ho
    · simp [b, hz, SArithmeticData.IsAllowed]
    · simpa [b, ho] using hπAllowed v
  have hq : c.val.val = ∏ v : P, (q v).val := by
    rw [hSupport]
    apply Finset.prod_congr rfl
    intro v _
    rcases he v with hz | ho
    · simp [q, ← show e v = idealPrimeExponent v.val.asIdeal c.val.val from rfl, hz,
        exteriorSquarefreeTop]
    · simp [q, ← show e v = idealPrimeExponent v.val.asIdeal c.val.val from rfl, ho, hp v]
  have hcop : ∀ v w, v ≠ w → (q v).val ⊔ (q w).val = ⊤ := by
    intro v w hvw
    rcases he v with hz | ho
    · simp [q, hz, exteriorSquarefreeTop]
    rcases he w with hz | ho'
    · simp [q, hz, exteriorSquarefreeTop]
    simp only [q, ho, ho', one_ne_zero, ↓reduceIte, hp]
    exact (v.val.isCoprime_of_ne w.val (fun h => hvw (Subtype.ext h))).sup_eq
  have hgen : A.Generates c.val (∏ v, ρ v) := by
    have hh := productExterior_generates A q ρ hρ Finset.univ
    have hi : productExterior A q Finset.univ = c.val := Subtype.ext hq.symm
    simpa only [hi] using hh
  have hbprod : ((∏ v, b v : Fˣ) : F) = ((∏ v, ρ v : A.R) : F) := by
    change (∏ v ∈ Finset.univ, b v : Fˣ).val =
      algebraMap A.R F (∏ v ∈ Finset.univ, ρ v)
    rw [Units.coe_prod, map_prod]
    exact Finset.prod_congr rfl (fun v _ => hb v)
  have hbprodAllowed : A.IsAllowed G.B (∏ v, b v) := by
    unfold SArithmeticData.IsAllowed
    rw [map_prod]
    apply prod_mem
    intro v _
    exact hbAllowed v
  have hchange := A.idealGauss_allowed_generator_independent σ hS hCl G.H G.B
    G.B_complement c.val (∏ v, ρ v) a hgen ha (∏ v, b v) ac hbprod hac
    hbprodAllowed hcAllowed 2
  rw [hchange, assembly_finite_support_reciprocal A σ η hS G q ρ hρ b hb hbAllowed
    hcop c.val hq c.property hgen]
  congr 1
  · apply Finset.prod_congr rfl
    intro v _
    rcases he v with hz | ho
    · have ht : (q v).val = ⊤ := by simp [q, hz, exteriorSquarefreeTop]
      rw [A.idealGauss_top σ hS (q v) ht (ρ v) (hρ v) 2]
      simp [← show e v = idealPrimeExponent v.val.asIdeal c.val.val from rfl, hz]
    · simp only [← show e v = idealPrimeExponent v.val.asIdeal c.val.val from rfl, ho,
        pow_one]
      simp only [q, ρ, ho, one_ne_zero, ↓reduceIte]
  · apply Finset.prod_congr rfl
    intro v _
    apply Finset.prod_congr rfl
    intro w _
    rcases he v with hz | ho
    · have ht : (q v).val = ⊤ := by simp [q, hz, exteriorSquarefreeTop]
      unfold assemblyPhase SArithmeticData.sexticResidue
      rw [A.residueValue_top A.sexticResidueFamily _ ht]
      simp [← show e v = idealPrimeExponent v.val.asIdeal c.val.val from rfl, hz]
    rcases he w with hz | ho'
    · unfold assemblyPhase SArithmeticData.sexticResidue SArithmeticData.residueValue
      simp [ρ, hz, ← show e w = idealPrimeExponent w.val.asIdeal c.val.val from rfl]
    · simp [assemblyPhase, q, ρ, ho, ho',
        ← show e v = idealPrimeExponent v.val.asIdeal c.val.val from rfl,
        ← show e w = idealPrimeExponent w.val.asIdeal c.val.val from rfl]

end
end DedekindZetaZeroFree.GaussProductCancellation

end

section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.GaussProductCancellation
noncomputable section
set_option autoImplicit false
variable {F : Type} [Field F] [NumberField F]

theorem prime_product_replacement
    (A : SArithmeticData F) (hCl : Subsingleton (ClassGroup A.R)) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (G : A.GaussCorrectionOutput σ η hS)
    (D : ComparisonPoissonCoefficientData F A)
    (hCompatible : GeneratorInvariance.HasCompatibleCharacters A D)
    (hGeneratorAllowed : ∀ I : A.Exterior, ∃ a : Fˣ,
      (a : F) = (D.generator I : F) ∧ A.IsAllowed G.B a)
    (c : ExteriorSquarefreeIdeal A.cS) (n s r : A.Exterior) (u : A.R)
    (P : Finset (HeightOneSpectrum (𝓞 F)))
    (p : P → A.Exterior) (hp : ∀ v : P, (p v).val = v.val.asIdeal)
    (π : P → A.R) (hπ : ∀ v : P, A.Generates (p v) (π v))
    (aπ : P → Fˣ) (haπ : ∀ v : P, (aπ v : F) = (π v : F))
    (hπAllowed : ∀ v : P, A.IsAllowed G.B (aπ v))
    (hSupport : ∀ I ∈ ({c.val, n, s, r} : Finset A.Exterior),
      I.val = ∏ v : P, v.val.asIdeal ^ idealPrimeExponent v.val.asIdeal I.val) :
    comparisonPoissonFiniteCoefficient F A D c n s (u * D.generator r ^ 6) =
      GeneratorInvariance.coefficient A D
        (∏ v : P, π v ^ idealPrimeExponent v.val.asIdeal s.val)
        (∏ v : P, π v ^ (idealPrimeExponent v.val.asIdeal c.val.val +
          3 * idealPrimeExponent v.val.asIdeal n.val))
        (u * (∏ v : P, π v ^ idealPrimeExponent v.val.asIdeal r.val) ^ 6)
        (Finset.prod_ne_zero_iff.mpr (fun v _ => pow_ne_zero _ (hπ v).1))
        (Finset.prod_ne_zero_iff.mpr (fun v _ => pow_ne_zero _ (hπ v).1)) := by
  let g : A.Exterior → A.R := fun I =>
    ∏ v : P, π v ^ idealPrimeExponent v.val.asIdeal I.val
  let ag : A.Exterior → Fˣ := fun I =>
    ∏ v : P, aπ v ^ idealPrimeExponent v.val.asIdeal I.val
  have hg (I : A.Exterior) (hI : I ∈ ({c.val, n, s, r} : Finset A.Exterior)) :
      A.Generates I (g I) := by
    refine ⟨Finset.prod_ne_zero_iff.mpr (fun v _ => pow_ne_zero _ (hπ v).1), ?_⟩
    dsimp only [g]
    rw [← Ideal.prod_span_singleton]
    simp_rw [← Ideal.span_singleton_pow, (hπ _).2]
    change (∏ v : P, Ideal.map (algebraMap (𝓞 F) A.R) (p v).val ^
      idealPrimeExponent v.val.asIdeal I.val) =
        Ideal.map (algebraMap (𝓞 F) A.R) I.val
    simp_rw [hp]
    simp only [← Ideal.map_pow]
    calc
      _ = Ideal.map (algebraMap (𝓞 F) A.R)
          (∏ v : P, v.val.asIdeal ^ idealPrimeExponent v.val.asIdeal I.val) :=
        (map_prod (Ideal.mapHom (algebraMap (𝓞 F) A.R)) _ _).symm
      _ = _ := congrArg (Ideal.map (algebraMap (𝓞 F) A.R)) (hSupport I hI).symm
  have hag (I : A.Exterior) : (ag I : F) = (g I : F) := by
    change (Units.coeHom F) (∏ v : P, aπ v ^ idealPrimeExponent v.val.asIdeal I.val) =
      A.R.subtype (∏ v : P, π v ^ idealPrimeExponent v.val.asIdeal I.val)
    simp only [map_prod, map_pow, Units.coeHom_apply]
    exact Finset.prod_congr rfl (fun v _ => congrArg (fun x : F => x ^
      idealPrimeExponent v.val.asIdeal I.val) (haπ v))
  have halg (I : A.Exterior) : A.IsAllowed G.B (ag I) := by
    change A.sClass (∏ v : P, aπ v ^ idealPrimeExponent v.val.asIdeal I.val) ∈ G.B
    rw [map_prod]
    apply _root_.prod_mem
    intro v _
    rw [map_pow]
    exact G.B.pow_mem (hπAllowed v) _
  obtain ⟨ac, hac, halc⟩ := hGeneratorAllowed c.val
  obtain ⟨an, han, haln⟩ := hGeneratorAllowed n
  obtain ⟨as_, has, hals⟩ := hGeneratorAllowed s
  obtain ⟨ar, har, halr⟩ := hGeneratorAllowed r
  have hc := hg c.val (by simp)
  have hn := hg n (by simp)
  have hs := hg s (by simp)
  have hr := hg r (by simp)
  have he := GeneratorInvariance.coefficient_allowed_generator_replacement A D
    hCompatible hCl G.H G.B G.B_complement c.val n s r
    (D.generator c.val) (D.generator n) (D.generator s) (D.generator r)
    (g c.val) (g n) (g s) (g r) u
    (D.generates c.val) (D.generates n) (D.generates s) (D.generates r)
    hc hn hs hr ac an as_ ar (ag c.val) (ag n) (ag s) (ag r)
    hac han has har (hag c.val) (hag n) (hag s) (hag r)
    ⟨halc, haln, hals, halr⟩ ⟨halg c.val, halg n, halg s, halg r⟩
  have hmod : g c.val * g n ^ 3 =
      ∏ v : P, π v ^ (idealPrimeExponent v.val.asIdeal c.val.val +
        3 * idealPrimeExponent v.val.asIdeal n.val) := by
    dsimp only [g]
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro v _
    rw [pow_add, Nat.mul_comm 3, pow_mul]
  rw [← GeneratorInvariance.coefficient_eq_comparison]
  simpa only [hmod, g] using he.symm

end
end DedekindZetaZeroFree.GaussProductCancellation

end

section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.GlobalPairCancel
noncomputable section
set_option autoImplicit false

variable {F : Type} [Field F] [NumberField F]

def principalCharacter (A : SArithmeticData F) (σ : F →+* ℂ)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a) :
    MulChar (FiniteTransform.Residue A.R.toSubring a) ℂ :=
  GeneratorInvariance.transportCharacter _ _ ha.2.symm
    (A.sexticResiduePowerChar σ I 1)

def HasArithmeticRecipes (A : SArithmeticData F) (σ : F →+* ℂ)
    (hS : A.ContainsTraceBadPlaces) (B : Subgroup A.V)
    (D : ComparisonPoissonCoefficientData F A) : Prop :=
  (∀ I : A.Exterior, ∃ a : Fˣ,
    (a : F) = (D.generator I : F) ∧ A.IsAllowed B a) ∧
  (∀ (I : A.Exterior) (a : A.R) (ha : A.Generates I a),
    D.character a = principalCharacter A σ I a ha) ∧
  (∀ x : F, D.additiveCharacter x = (A.fieldTraceCharacter x : ℂ)) ∧
  (∀ c : ExteriorSquarefreeIdeal A.cS,
    D.gammaTwo c = A.idealGauss σ hS c.val (D.generator c.val)
      (D.generates c.val) 2)

theorem principalCharacter_pow_six (A : SArithmeticData F) (σ : F →+* ℂ)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a) :
    principalCharacter A σ I a ha ^ 6 = 1 := by
  have hχ : A.sexticResiduePowerChar σ I 1 ^ 6 = 1 := by
    apply MulChar.ext
    intro x
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
    change (MulChar.ofUnitHom
      ((Units.map σ.toMonoidHom).comp (A.sexticResidueFamily I)) ^
        SArithmeticData.sexticExponent 1) (x : A.R ⧸ A.extendIdeal I) ^ 6 = 1
    rw [show SArithmeticData.sexticExponent 1 = 1 by decide, pow_one,
      MulChar.ofUnitHom_coe]
    change (σ (((A.sexticResidueFamily I) x : F))) ^ 6 = 1
    rw [← map_pow]
    have hh := congrArg (fun z : Fˣ => (z : F))
      (A.sexticResidueFamily_normalized.1 I x)
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at hh
    rw [hh, map_one]
  have transport : ∀ (J K : Ideal A.R) (h : J = K)
      (χ : MulChar (A.R ⧸ J) ℂ), χ ^ 6 = 1 →
      GeneratorInvariance.transportCharacter J K h χ ^ 6 = 1 := by
    intro J K h χ hχ
    subst K
    exact hχ
  exact transport _ _ ha.2.symm _ hχ

theorem HasArithmeticRecipes.compatible (A : SArithmeticData F) (σ : F →+* ℂ)
    (hS : A.ContainsTraceBadPlaces) (B : Subgroup A.V)
    (D : ComparisonPoissonCoefficientData F A)
    (hD : HasArithmeticRecipes A σ hS B D) :
    GeneratorInvariance.HasCompatibleCharacters A D := by
  have hex : ∀ (a : A.R) (ha : a ≠ 0), ∃ I : A.Exterior, A.Generates I a := by
    intro a ha
    refine ⟨A.exteriorIdealEquiv.symm ⟨Ideal.span {a}, by simpa using ha⟩,
      ha, ?_⟩
    rw [← A.exteriorIdealEquiv_apply]
    exact (congrArg Subtype.val (A.exteriorIdealEquiv.apply_symm_apply
      ⟨Ideal.span {a}, by simpa using ha⟩)).symm
  refine ⟨?_, ?_, ?_⟩
  · intro x
    rw [hD.2.2.1]
    exact congrArg (fun z : Circle => (z : ℂ)) (A.eS_integer hS x)
  · intro a ha
    obtain ⟨I, hI⟩ := hex a ha
    rw [hD.2.1 I a hI]
    exact principalCharacter_pow_six A σ I a hI
  · intro a b ha hb hab
    obtain ⟨I, hI⟩ := hex a ha
    have hJ : A.Generates I b := ⟨hb, hab.symm.trans hI.2⟩
    rw [hD.2.1 I a hI, hD.2.1 I b hJ]
    have ht : ∀ (J K L : Ideal A.R) (hJK : J = K) (hKL : K = L)
        (hJL : J = L) (χ : MulChar (A.R ⧸ J) ℂ),
        GeneratorInvariance.transportCharacter J L hJL χ =
          GeneratorInvariance.transportCharacter K L hKL
            (GeneratorInvariance.transportCharacter J K hJK χ) := by
      intro J K L hJK hKL hJL χ
      subst K
      subst L
      rfl
    exact ht _ _ _ hI.2.symm hab hJ.2.symm _

theorem HasArithmeticRecipes.coefficient_eq_crt
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (B : Subgroup A.V) (D : ComparisonPoissonCoefficientData F A)
    (hD : HasArithmeticRecipes A σ hS B D)
    (C : A.GeneralArithmeticContext σ η hS)
    (Is Ia : A.Exterior) (s a h : A.R)
    (hs : A.Generates Is s) (ha : A.Generates Ia a) :
    GeneratorInvariance.coefficient A D s a h hs.1 ha.1 =
      MaskedQuotientCRT.coefficient C Is Ia s a h hs ha := by
  unfold GeneratorInvariance.coefficient MaskedQuotientCRT.coefficient
  rw [hD.2.1 Is s hs, hD.2.1 Ia a ha]
  have he : D.additiveCharacter = Circle.coeHom.compAddChar A.fieldTraceCharacter := by
    ext x
    exact hD.2.2.1 x
  rw [he]
  congr 1 <;> exact Subsingleton.elim _ _

theorem HasArithmeticRecipes.coefficient_prime_power_crt
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (B : Subgroup A.V) (D : ComparisonPoissonCoefficientData F A)
    (hD : HasArithmeticRecipes A σ hS B D)
    (C : A.GeneralArithmeticContext σ η hS)
    (Is Ia Ih : A.Exterior) (s a h : A.R)
    (hs : A.Generates Is s) (ha : A.Generates Ia a) (hh : A.Generates Ih h)
    (hsAllowed : A.IsAllowed C.correction.B
      (Units.mk0 (s : F) (by exact_mod_cast hs.1)))
    (haAllowed : A.IsAllowed C.correction.B
      (Units.mk0 (a : F) (by exact_mod_cast ha.1)))
    (P : Finset (LocalFiniteSums.ExteriorPrime A))
    (hSupportS : ∀ p, MaskedQuotientCRT.primeExponent p Is ≠ 0 → p ∈ P)
    (hSupportA : ∀ p, MaskedQuotientCRT.primeExponent p Ia ≠ 0 → p ∈ P)
    (hSupportH : ∀ p, MaskedQuotientCRT.primeExponent p Ih ≠ 0 → p ∈ P) :
    GeneratorInvariance.coefficient A D s a h hs.1 ha.1 =
      ∏ p ∈ P, CompatiblePrimeRawLocal.R C p
        (MaskedQuotientCRT.primeExponent p Ia) (MaskedQuotientCRT.primeExponent p Is)
        (MaskedQuotientCRT.primeExponent p Ih)
        (MaskedQuotientCRT.localUnitPart C p Is s hs)
        (MaskedQuotientCRT.localUnitPart C p Ia a ha)
        (MaskedQuotientCRT.localUnitPart C p Ih h hh) := by
  rw [hD.coefficient_eq_crt A σ η hS B D C Is Ia s a h hs ha]
  exact MaskedQuotientCRT.full_prime_power_crt C Is Ia Ih s a h hs ha hh
    hsAllowed haAllowed P hSupportS hSupportA hSupportH

def primePowerSum (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (π : A.R) (hπ : π ≠ 0) (t k J : ℕ) : ℂ :=
  GeneratorInvariance.coefficient A D (π ^ k) (π ^ t) (π ^ J)
    (pow_ne_zero k hπ) (pow_ne_zero t hπ)

def frequencyTheta (A : SArithmeticData F) (σ : F →+* ℂ)
    (p : A.Exterior) (uPrimeFree : A.R) : ℂ :=
  σ (A.sexticResidue p uPrimeFree)

theorem frequencyTheta_unit (A : SArithmeticData F) (σ : F →+* ℂ)
    (p : A.Exterior) (x : A.R)
    (hx : IsUnit (Ideal.Quotient.mk (A.extendIdeal p) x)) :
    frequencyTheta A σ p x ≠ 0 ∧ frequencyTheta A σ p x ^ 6 = 1 := by
  let v := hx.unit
  have hv : (v : A.R ⧸ A.extendIdeal p) = Ideal.Quotient.mk (A.extendIdeal p) x :=
    hx.unit_spec
  have hroot := A.sexticResidueFamily_normalized.1 p v
  have hval : A.sexticResidue p x = (A.sexticResidueFamily p v : F) := by
    unfold SArithmeticData.sexticResidue SArithmeticData.residueValue
    rw [← hv, MulChar.ofUnitHom_coe]
  have hpow : frequencyTheta A σ p x ^ 6 = 1 := by
    unfold frequencyTheta
    rw [hval, ← map_pow]
    have hh := congrArg (fun z : Fˣ => (z : F)) hroot
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at hh
    rw [hh, map_one]
  exact ⟨fun hz => by simpa [hz] using hpow, hpow⟩

theorem frequencyTheta_mul (A : SArithmeticData F) (σ : F →+* ℂ)
    (p : A.Exterior) (x y : A.R) :
    frequencyTheta A σ p (x * y) =
      frequencyTheta A σ p x * frequencyTheta A σ p y := by
  unfold frequencyTheta SArithmeticData.sexticResidue SArithmeticData.residueValue
  rw [map_mul, map_mul, map_mul]

theorem actual_pair_phase_cancel
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (G : A.GaussCorrectionOutput σ η hS)
    (I J : A.Exterior) (a b : A.R) (ha : A.Generates I a) (hb : A.Generates J b)
    (ua ub : Fˣ) (hua : (ua : F) = (a : F)) (hub : (ub : F) = (b : F))
    (hBa : A.IsAllowed G.B ua) (hBb : A.IsAllowed G.B ub)
    (hcop : I.val ⊔ J.val = ⊤) (e₁ e₂ l₁ l₂ k₁ k₂ : ℕ) :
    let t₁ := e₁ + 3 * l₁
    let t₂ := e₂ + 3 * l₂
    σ (A.sexticResidue I b) ^ (4 * e₁ * e₂) *
      (σ (A.sexticResidue I b) ^
          ((t₁ : ℤ) * k₂ + ((t₁ : ℤ) - k₁) * t₂) *
        σ (A.sexticResidue J a) ^
          ((t₂ : ℤ) * k₁ + ((t₂ : ℤ) - k₂) * t₁)) = 1 := by
  have hrec := (ArithmeticContext.actual_hilbert_sextic_reciprocity
    A G.H G.B G.H_actual G.B_complement).1
    I J a b ua ub ha hb hua hub hBa hBb hcop
  have hcopR : IsCoprime a b := by
    apply (Ideal.sup_eq_top_iff_isCoprime a b).mp
    rw [ha.2, hb.2]
    change Ideal.map (algebraMap (𝓞 F) A.R) I.val ⊔
      Ideal.map (algebraMap (𝓞 F) A.R) J.val = ⊤
    rw [← Ideal.map_sup, hcop, Ideal.map_top]
  have hbu : IsUnit (Ideal.Quotient.mk (A.extendIdeal I) b) := by
    obtain ⟨r, s, hrs⟩ := hcopR
    have haz : Ideal.Quotient.mk (A.extendIdeal I) a = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [← ha.2]
      exact Ideal.subset_span (Set.mem_singleton a)
    apply IsUnit.of_mul_eq_one (Ideal.Quotient.mk (A.extendIdeal I) s)
    have hh := congrArg (Ideal.Quotient.mk (A.extendIdeal I)) hrs
    simpa only [map_add, map_mul, map_one, haz, zero_mul, zero_add, mul_comm] using hh
  have hroot := (frequencyTheta_unit A σ I b hbu).2
  dsimp only
  rw [SexticPairwiseExponent.raw_phase_cancel _ _ (congrArg σ hrec) hroot]
  rw [← pow_add, show 4 * e₁ * e₂ + 2 * (e₁ + 3 * l₁) * (e₂ + 3 * l₂) =
      6 * (e₁ * e₂ + e₁ * l₂ + e₂ * l₁ + 3 * l₁ * l₂) by
        have hh := SexticPairwiseExponent.exponent e₁ e₂ l₁ l₂
        omega, pow_mul]
  change (frequencyTheta A σ I b ^ 6) ^ _ = 1
  rw [hroot, one_pow]

theorem actual_cross_prime_product_cancel
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    [LocallyFiniteOrderTop ι] [LocallyFiniteOrderBot ι]
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (G : A.GaussCorrectionOutput σ η hS)
    (p : ι → A.Exterior) (π : ι → A.R)
    (hπ : ∀ v, A.Generates (p v) (π v))
    (aπ : ι → Fˣ) (haπ : ∀ v, (aπ v : F) = (π v : F))
    (hπAllowed : ∀ v, A.IsAllowed G.B (aπ v))
    (hcop : ∀ v w, v ≠ w → (p v).val ⊔ (p w).val = ⊤)
    (e l k : ι → ℕ) :
    (∏ v, ∏ w ∈ Finset.Ioi v,
      σ (A.sexticResidue (p v) (π w)) ^ (4 * e v * e w)) *
    (∏ v, ∏ w ∈ ({v}ᶜ : Finset ι),
      σ (A.sexticResidue (p v) (π w)) ^
        (((e v + 3 * l v : ℕ) : ℤ) * k w +
          (((e v + 3 * l v : ℕ) : ℤ) - k v) * (e w + 3 * l w))) = 1 := by
  let raw : ι → ι → ℂ := fun v w =>
    σ (A.sexticResidue (p v) (π w)) ^
      (((e v + 3 * l v : ℕ) : ℤ) * k w +
        (((e v + 3 * l v : ℕ) : ℤ) - k v) * (e w + 3 * l w))
  change _ * (∏ v, ∏ w ∈ ({v}ᶜ : Finset ι), raw v w) = 1
  rw [← Finset.prod_prod_Ioi_mul_eq_prod_prod_off_diag (fun v w => raw w v)]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro v _
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro w hw
  have hvw : v ≠ w := ne_of_lt (Finset.mem_Ioi.mp hw)
  exact actual_pair_phase_cancel A σ η hS G (p v) (p w) (π v) (π w)
    (hπ v) (hπ w) (aπ v) (aπ w) (haπ v) (haπ w)
    (hπAllowed v) (hπAllowed w) (hcop v w hvw)
    (e v) (e w) (l v) (l w) (k v) (k w)

variable {ι : Type*}
 def productExterior (A : SArithmeticData F) (p : ι → A.Exterior)
    (T : Finset ι) : A.Exterior :=
  ⟨∏ v ∈ T, (p v).val, by
    refine ⟨Finset.prod_ne_zero_iff.mpr (fun v _ => (p v).property.1), ?_⟩
    exact Ideal.prod_sup_eq_top (fun v _ => (p v).property.2)⟩
private theorem productExterior_generates (A : SArithmeticData F) (p : ι → A.Exterior)
    (π : ι → A.R) (hπ : ∀ v, A.Generates (p v) (π v)) (T : Finset ι) :
    A.Generates (productExterior A p T) (∏ v ∈ T, π v) := by
  refine ⟨Finset.prod_ne_zero_iff.mpr (fun v _ => (hπ v).1), ?_⟩
  rw [← Ideal.prod_span_singleton]
  simp_rw [(hπ _).2]
  change (∏ v ∈ T, A.extendIdeal (p v)) = _
  simp only [SArithmeticData.extendIdeal, productExterior]
  exact (map_prod (Ideal.mapHom (algebraMap (𝓞 F) A.R)) _ _).symm
private theorem frequencyTheta_modulus_prod (A : SArithmeticData F) (σ : F →+* ℂ)
    (p : ι → A.Exterior) (T : Finset ι) (x : A.R) :
    frequencyTheta A σ (productExterior A p T) x =
      ∏ v ∈ T, frequencyTheta A σ (p v) x := by
  induction T using Finset.induction_on with
  | empty =>
    unfold frequencyTheta SArithmeticData.sexticResidue
    rw [A.residueValue_top A.sexticResidueFamily _ (by simp [productExterior])]
    simp
  | @insert a T ha ih =>
    have hh : (productExterior A p (insert a T)).val =
        (p a).val * (productExterior A p T).val := by
      simp [productExterior, Finset.prod_insert, ha]
    change σ (A.residueValue A.sexticResidueFamily _ x) = _
    rw [A.sexticResidueFamily_normalized.2.2 (p a) (productExterior A p T) _ hh x,
      map_mul]
    change frequencyTheta A σ (p a) x * frequencyTheta A σ (productExterior A p T) x = _
    rw [ih, Finset.prod_insert ha]

theorem idealGauss_finite_support_crt (A : SArithmeticData F) (σ : F →+* ℂ)
    (hS : A.ContainsTraceBadPlaces) (p : ι → A.Exterior)
    (π : ι → A.R) (hπ : ∀ v, A.Generates (p v) (π v)) (T : Finset ι)
    (hSquare : Squarefree (∏ v ∈ T, (p v).val))
    (hcop : ∀ v ∈ T, ∀ w ∈ T, v ≠ w → (p v).val ⊔ (p w).val = ⊤)
    (I : A.Exterior) (hI : I.val = ∏ v ∈ T, (p v).val)
    (hgen : A.Generates I (∏ v ∈ T, π v)) :
    A.idealGauss σ hS I (∏ v ∈ T, π v) hgen 2 =
      (∏ v ∈ T, A.idealGauss σ hS (p v) (π v) (hπ v) 2) *
      (∏ v ∈ T, frequencyTheta A σ (p v) (∏ w ∈ T.erase v, π w) ^ 2) := by
  have hIE : I = productExterior A p T := Subtype.ext hI
  subst I
  clear hI
  induction T using Finset.induction_on with
  | empty =>
    have ht : (productExterior A p ∅).val = ⊤ := by simp [productExterior]
    simpa using A.idealGauss_top σ hS (productExterior A p ∅) ht _ hgen 2
  | @insert a T ha ih =>
    have hPa : Squarefree (p a).val := hSquare.squarefree_of_dvd
      (by simp only [Finset.prod_insert ha]; exact dvd_mul_right _ _)
    have hPT : Squarefree (∏ v ∈ T, (p v).val) := hSquare.squarefree_of_dvd
      (by simp only [Finset.prod_insert ha]; exact dvd_mul_left _ _)
    have hcopT : ∀ v ∈ T, ∀ w ∈ T, v ≠ w → (p v).val ⊔ (p w).val = ⊤ :=
      fun v hv w hw => hcop v (Finset.mem_insert_of_mem hv) w (Finset.mem_insert_of_mem hw)
    have hcopA : (p a).val ⊔ (productExterior A p T).val = ⊤ := by
      apply Ideal.sup_prod_eq_top
      intro v hv
      exact hcop a (Finset.mem_insert_self _ _) v (Finset.mem_insert_of_mem hv)
        (fun he => ha (he ▸ hv))
    have hmul : (productExterior A p (insert a T)).val =
        (p a).val * (productExterior A p T).val := by
      simp [productExterior, Finset.prod_insert ha]
    have hgenT := productExterior_generates A p π hπ T
    have hgenAT : A.Generates (productExterior A p (insert a T))
        (π a * ∏ v ∈ T, π v) := by simpa only [Finset.prod_insert ha] using hgen
    have hcrt := A.idealGauss_squarefree_crt σ hS (p a) (productExterior A p T)
      (productExterior A p (insert a T)) hPa hPT hcopA hmul (π a) _ (hπ a) hgenT hgenAT 2
    norm_num [SArithmeticData.sexticExponent] at hcrt
    have hi := ih hPT hcopT hgenT
    have hexpand :
        (∏ v ∈ insert a T, frequencyTheta A σ (p v) (∏ w ∈ (insert a T).erase v, π w) ^ 2) =
        frequencyTheta A σ (p a) (∏ w ∈ T, π w) ^ 2 *
          ((∏ v ∈ T, frequencyTheta A σ (p v) (π a) ^ 2) *
            (∏ v ∈ T, frequencyTheta A σ (p v) (∏ w ∈ T.erase v, π w) ^ 2)) := by
      rw [Finset.prod_insert ha]
      simp only [Finset.erase_insert ha]
      congr 1
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro v hv
      have hva : v ≠ a := fun he => ha (he ▸ hv)
      rw [Finset.erase_insert_of_ne hva.symm, Finset.prod_insert (fun hh => ha (Finset.mem_of_mem_erase hh)),
        frequencyTheta_mul, mul_pow]
    rw [hexpand]
    simp only [Finset.prod_insert ha]
    rw [hcrt, hi]
    change frequencyTheta A σ (p a) (∏ v ∈ T, π v) ^ 2 *
      frequencyTheta A σ (productExterior A p T) (π a) ^ 2 * _ * _ = _
    rw [frequencyTheta_modulus_prod]
    simp only [Finset.prod_pow]
    ring

theorem global_pair_cancel
    (A : SArithmeticData F) (hCl : Subsingleton (ClassGroup A.R)) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (G : A.GaussCorrectionOutput σ η hS)
    (D : ComparisonPoissonCoefficientData F A)
    (hD : HasArithmeticRecipes A σ hS G.B D)
    (c : ExteriorSquarefreeIdeal A.cS) (n s r Iu : A.Exterior)
    (u : A.R) (hu : A.Generates Iu u)
    (au : Fˣ) (hau : (au : F) = (u : F)) (huAllowed : A.IsAllowed G.B au)
    (huSixthFree : ∀ v : HeightOneSpectrum (𝓞 F),
      idealPrimeExponent v.asIdeal Iu.val ≤ 5)
    (P : Finset (HeightOneSpectrum (𝓞 F)))
    (p : P → A.Exterior) (hp : ∀ v : P, (p v).val = v.val.asIdeal)
    (π : P → A.R) (hπ : ∀ v : P, A.Generates (p v) (π v))
    (aπ : P → Fˣ) (haπ : ∀ v : P, (aπ v : F) = (π v : F))
    (hπAllowed : ∀ v : P, A.IsAllowed G.B (aπ v))
    (hSupport : ∀ I ∈ ({c.val, n, s, r, Iu} : Finset A.Exterior),
      I.val = ∏ v : P, v.val.asIdeal ^ idealPrimeExponent v.val.asIdeal I.val)
    (uPrimeFree : P → A.R)
    (hPrimeFree : ∀ v : P,
      u = π v ^ idealPrimeExponent v.val.asIdeal Iu.val * uPrimeFree v)
    (hPrimeUnit : ∀ v : P,
      IsUnit (Ideal.Quotient.mk (A.extendIdeal (p v)) (uPrimeFree v))) :
    (∀ v : P, frequencyTheta A σ (p v) (uPrimeFree v) ≠ 0 ∧
      frequencyTheta A σ (p v) (uPrimeFree v) ^ 6 = 1) ∧
    D.gammaTwo c * comparisonPoissonFiniteCoefficient F A D c n s
        (u * D.generator r ^ 6) =
      ∏ v : P,
        let e := idealPrimeExponent v.val.asIdeal c.val.val
        let l := idealPrimeExponent v.val.asIdeal n.val
        let t := e + 3 * l
        let k := idealPrimeExponent v.val.asIdeal s.val
        let j := idealPrimeExponent v.val.asIdeal Iu.val
        let m := idealPrimeExponent v.val.asIdeal r.val
        A.idealGauss σ hS (p v) (π v) (hπ v) 2 ^ e *
          frequencyTheta A σ (p v) (uPrimeFree v) ^ ((k : ℤ) - (t : ℤ)) *
          primePowerSum A D (π v) (hπ v).1 t k (j + 6 * m) := by
  refine ⟨fun v => frequencyTheta_unit A σ (p v) (uPrimeFree v) (hPrimeUnit v), ?_⟩
  classical

  letI : LinearOrder P := LinearOrder.lift' (Fintype.equivFin P)
    (Fintype.equivFin P).injective
  letI : LocallyFiniteOrderTop P := LocallyFiniteOrderTop.ofIci P
    (fun v => Finset.univ.filter (fun w => v ≤ w)) (by simp)
  letI : LocallyFiniteOrderBot P := LocallyFiniteOrderBot.ofIic P
    (fun v => Finset.univ.filter (fun w => w ≤ v)) (by simp)
  have hReplace := GaussProductCancellation.prime_product_replacement
    A hCl σ η hS G D (hD.compatible A σ hS G.B D) hD.1 c n s r u
    P p hp π hπ aπ haπ hπAllowed (by
      intro I hI
      apply hSupport I
      simp only [Finset.mem_insert, Finset.mem_singleton] at hI ⊢
      rcases hI with hI | hI | hI | hI <;> simp [hI])
  have hRaw := GaussProductCancellation.masked_product_assembly A σ η hS G D
    hD.2.1 hD.2.2.1 c.val n s r Iu u hu P p hp π hπ aπ haπ hπAllowed
    hSupport uPrimeFree hPrimeFree hPrimeUnit
  obtain ⟨ac, hac, hcAllowed⟩ := hD.1 c.val
  have hGauss := GaussProductCancellation.gauss_product_assembly
    A hCl σ η hS G c (D.generator c.val) (D.generates c.val)
    ac hac hcAllowed P p hp π hπ aπ haπ hπAllowed
    (hSupport c.val (by simp))
  have hcop : ∀ v w : P, v ≠ w → (p v).val ⊔ (p w).val = ⊤ := by
    intro v w hvw
    rw [hp v, hp w]
    exact Ideal.isCoprime_iff_sup_eq.mp
      (HeightOneSpectrum.isCoprime_of_ne v.val w.val
        (fun h => hvw (Subtype.ext h)))
  have hCancel := actual_cross_prime_product_cancel A σ η hS G p π hπ
    aπ haπ hπAllowed hcop
    (fun v => idealPrimeExponent v.val.asIdeal c.val.val)
    (fun v => idealPrimeExponent v.val.asIdeal n.val)
    (fun v => idealPrimeExponent v.val.asIdeal s.val)
  rw [hD.2.2.2 c, hGauss, hReplace, hRaw]
  dsimp only at hCancel ⊢
  simp only [frequencyTheta, primePowerSum]
  rw [mul_mul_mul_comm]
  have hCancel' :
      (∏ v : P, ∏ w ∈ Finset.Ioi v,
        σ (A.sexticResidue (p v) (π w)) ^
          (4 * idealPrimeExponent v.val.asIdeal c.val.val *
            idealPrimeExponent w.val.asIdeal c.val.val)) *
      (∏ v : P, ∏ w ∈ ({v}ᶜ : Finset P),
        σ (A.sexticResidue (p v) (π w)) ^
          (((idealPrimeExponent v.val.asIdeal c.val.val +
              3 * idealPrimeExponent v.val.asIdeal n.val : ℕ) : ℤ) *
              idealPrimeExponent w.val.asIdeal s.val +
            (((idealPrimeExponent v.val.asIdeal c.val.val +
                3 * idealPrimeExponent v.val.asIdeal n.val : ℕ) : ℤ) -
                idealPrimeExponent v.val.asIdeal s.val) *
              (idealPrimeExponent w.val.asIdeal c.val.val +
                3 * idealPrimeExponent w.val.asIdeal n.val))) = 1 := by
    convert hCancel using 1
    congr 1
    apply Finset.prod_congr rfl
    intro v _
    apply Finset.prod_congr
    · ext w
      simp only [Finset.mem_compl, Finset.mem_singleton]
    · intro w _
      rfl
  rw [hCancel', mul_one, ← Finset.prod_mul_distrib]
  simp only [mul_assoc]

end
end DedekindZetaZeroFree.GlobalPairCancel

end
