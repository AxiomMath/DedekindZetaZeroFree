module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Conductors.ResidueConductorMinimality
public import DedekindZetaZeroFree.CharacterSums.Gauss.SexticChineseRemainderReciprocity
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.ExteriorResidueCharacters

@[expose] public section

section

namespace DedekindZetaZeroFree.Detector.ExteriorDyadic.ResidueFiberAdapter

open scoped NumberField
open NumberField IsDedekindDomain

theorem exists_conductor_split
    (F : Type) [Field F] [NumberField F] (A : SArithmeticData F)
    (f : Ideal (𝓞 F)) (hf : f ≠ ⊥) :
    ∃ fS qO : Ideal (𝓞 F), FixedSResidue.ConductorSplit A f fS qO := by
  classical

  let g : HeightOneSpectrum (𝓞 F) → Ideal (𝓞 F) := fun v => v.maxPowDividing f
  have hgfin : (Function.mulSupport g).Finite := Ideal.hasFiniteMulSupport hf
  let M : Finset (HeightOneSpectrum (𝓞 F)) := hgfin.toFinset
  have hMsupp : Function.mulSupport g ⊆ (M : Set (HeightOneSpectrum (𝓞 F))) := by
    intro v hv; exact hgfin.mem_toFinset.mpr hv
  have hfac : ∏ v ∈ M, g v = f := by
    rw [← Ideal.finprod_heightOneSpectrum_factorization hf]
    exact (finprod_eq_prod_of_mulSupport_subset g hMsupp).symm

  let fS : Ideal (𝓞 F) := ∏ v ∈ M.filter (fun v => v ∈ A.Sf), g v
  let qO : Ideal (𝓞 F) := ∏ v ∈ M.filter (fun v => v ∉ A.Sf), g v
  have hsplit : f = fS * qO := by
    rw [← hfac]
    exact (Finset.prod_filter_mul_prod_filter_not M (fun v => v ∈ A.Sf) g).symm
  have hne : fS * qO ≠ ⊥ := by rw [← hsplit]; exact hf
  have hfS : fS ≠ ⊥ := fun h => hne (Ideal.mul_eq_bot.mpr (Or.inl h))
  have hqO : qO ≠ ⊥ := fun h => hne (Ideal.mul_eq_bot.mpr (Or.inr h))

  have hsupp : ∀ v : HeightOneSpectrum (𝓞 F), fS ≤ v.asIdeal → v ∈ A.Sf := by
    intro v hvle
    have hdvd : v.asIdeal ∣ fS := Ideal.dvd_iff_le.mpr hvle
    have hprime : Prime v.asIdeal := v.prime
    obtain ⟨v', hv'mem, hv'dvd⟩ := (Prime.dvd_finsetProd_iff hprime g).mp hdvd
    have hv'Sf : v' ∈ A.Sf := (Finset.mem_filter.mp hv'mem).2
    have hv'dvd' : v.asIdeal ∣ v'.asIdeal := by
      apply hprime.dvd_of_dvd_pow
      simpa [g, IsDedekindDomain.HeightOneSpectrum.maxPowDividing] using hv'dvd
    have hle : v'.asIdeal ≤ v.asIdeal := Ideal.dvd_iff_le.mp hv'dvd'
    have heq : v'.asIdeal = v.asIdeal := v'.isMaximal.eq_of_le v.isMaximal.ne_top hle
    have hv'v : v' = v := HeightOneSpectrum.ext heq
    rwa [hv'v] at hv'Sf

  have hqOsup : qO ⊔ A.cS = ⊤ := by
    apply Ideal.prod_sup_eq_top (I := A.cS) (s := M.filter (fun v => v ∉ A.Sf)) (J := g)
    intro v hv
    have hvnot : v ∉ A.Sf := (Finset.mem_filter.mp hv).2
    apply Ideal.sup_prod_eq_top (I := g v) (s := A.Sf) (J := fun v' => v'.asIdeal)
    intro v' hv'
    have hne' : v ≠ v' := fun h => hvnot (h ▸ hv')
    have hcop := HeightOneSpectrum.isCoprime_pow_of_ne v v' hne'
      ((Associates.mk v.asIdeal).count (Associates.mk f).factors) 1
    simpa [g, IsDedekindDomain.HeightOneSpectrum.maxPowDividing, pow_one] using
      Ideal.isCoprime_iff_sup_eq.mp hcop
  exact ⟨fS, qO, hf, hfS, hqO, hsplit, hsupp, hqOsup⟩

end DedekindZetaZeroFree.Detector.ExteriorDyadic.ResidueFiberAdapter

end

section

namespace DedekindZetaZeroFree.Detector.ExteriorDyadic.ResidueFiberAdapter

open scoped NumberField
open NumberField IsDedekindDomain FixedSResidue

variable {F : Type} [Field F] [NumberField F]

private theorem exponent_zero_iff (v : HeightOneSpectrum (𝓞 F))
    (f : Ideal (𝓞 F)) (hf : f ≠ ⊥) :
    idealPrimeExponent v.asIdeal f = 0 ↔ v.asIdeal ⊔ f = ⊤ := by
  rw [idealPrimeExponent, Multiset.count_eq_zero]
  rw [UniqueFactorizationMonoid.mem_normalizedFactors_iff hf]
  simp only [v.prime, true_and, Ideal.dvd_iff_le]
  constructor
  · intro h
    exact (Ideal.isMaximal_def.mp v.isMaximal).2 _ (show v.asIdeal < v.asIdeal ⊔ f from
      lt_of_le_of_ne le_sup_left (by
        intro he
        exact h (he ▸ le_sup_right)))
  · intro h hle
    have : v.asIdeal ⊔ f = v.asIdeal := sup_eq_left.mpr hle
    exact v.isPrime.ne_top (this.symm.trans h)

private theorem exponent_mul (v : HeightOneSpectrum (𝓞 F))
    (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    idealPrimeExponent v.asIdeal (I * J) =
      idealPrimeExponent v.asIdeal I + idealPrimeExponent v.asIdeal J := by
  simp [idealPrimeExponent, UniqueFactorizationMonoid.normalizedFactors_mul hI hJ,
    Multiset.count_add]

private theorem cS_le_asIdeal (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∈ A.Sf) : A.cS ≤ v.asIdeal := by
  rw [SArithmeticData.cS]
  exact (Ideal.prod_le_inf : (∏ w ∈ A.Sf, w.asIdeal) ≤ A.Sf.inf (fun w => w.asIdeal)).trans
    (Finset.inf_le hv)

private theorem pow_le_of_exponent (v : HeightOneSpectrum (𝓞 F)) (I : Ideal (𝓞 F))
    (hI : I ≠ ⊥) : I ≤ v.asIdeal ^ idealPrimeExponent v.asIdeal I := by
  rw [← Ideal.dvd_iff_le]
  rw [pow_dvd_iff_le_emultiplicity,
    UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors v.irreducible hI]
  simp [idealPrimeExponent]

theorem slocal_conductor_trivial_of_sprime_compatibility
    (F : Type) [Field F] [NumberField F] (A : SArithmeticData F)
    (f fS qO : Ideal (𝓞 F)) (omega : RayClassCharacter F f)
    (hsplit : FixedSResidue.ConductorSplit A f fS qO)
    (sigma : FixedSResidue.FullLocalCharacters A)
    (hinfinite : ∀ w : InfinitePlace F, sigma.1 w = 1)
    (hcompat : FixedSInjectivity.SPrimeCompatibility A f omega sigma) :
    FixedSResidue.SLocalConductorTrivial A fS sigma := by
  intro alpha n hn hfS hcS
  have halpha0 : alpha ≠ 0 := by
    intro h
    have h1 : (n.val : F) = 0 := by rw [hn, h]; simp
    exact n.property (Subtype.ext (by simpa using h1))
  have hlocal : ∀ v : {v // v ∈ A.Sf},
      CRTLocalHigherUnits F v.val (idealPrimeExponent v.val.asIdeal f)
        ((A.diagonal (fieldUnit A n)).2 v) := by
    intro v
    have hsup : Ideal.span {alpha} ⊔ v.val.asIdeal = ⊤ := by
      have hle := sup_le_sup_left (cS_le_asIdeal A v.val v.property) (Ideal.span {alpha})
      rw [hcS] at hle
      exact top_le_iff.mp hle
    have hmem : alpha ∉ v.val.asIdeal := by
      intro hmem
      have hle2 : Ideal.span {alpha} ≤ v.val.asIdeal :=
        Ideal.span_singleton_le_iff_mem _ |>.mpr hmem
      rw [sup_eq_right.mpr hle2] at hsup
      exact v.val.isPrime.ne_top hsup
    have hqO0 : idealPrimeExponent v.val.asIdeal qO = 0 := by
      rw [exponent_zero_iff v.val qO hsplit.2.2.1, sup_comm]
      have hle : qO ⊔ A.cS ≤ qO ⊔ v.val.asIdeal :=
        sup_le_sup_left (cS_le_asIdeal A v.val v.property) qO
      rw [hsplit.2.2.2.2.2] at hle
      exact top_le_iff.mp hle
    have hexp : idealPrimeExponent v.val.asIdeal f
        = idealPrimeExponent v.val.asIdeal fS := by
      rw [hsplit.2.2.2.1, exponent_mul v.val fS qO hsplit.2.1 hsplit.2.2.1, hqO0, add_zero]
    have hcong : alpha - 1 ∈ v.val.asIdeal ^ idealPrimeExponent v.val.asIdeal f := by
      rw [hexp]
      exact pow_le_of_exponent v.val fS hsplit.2.1 hfS
    let b : v.val.adicCompletionIntegers F :=
      algebraMap (𝓞 F) (v.val.adicCompletionIntegers F) alpha
    have hb1 : b - 1 ∈ IsLocalRing.maximalIdeal (v.val.adicCompletionIntegers F)
        ^ idealPrimeExponent v.val.asIdeal f := by
      have h := (CRT_completed_power_mem_iff F v.val (alpha - 1)
        (idealPrimeExponent v.val.asIdeal f)).mpr hcong
      simpa [b] using h
    have hbnot : b ∉ IsLocalRing.maximalIdeal (v.val.adicCompletionIntegers F) := by
      intro hb
      have h1 : algebraMap (𝓞 F) (v.val.adicCompletionIntegers F) alpha ∈
          IsLocalRing.maximalIdeal (v.val.adicCompletionIntegers F) ^ 1 := by
        simpa [b] using hb
      have h2 : alpha ∈ v.val.asIdeal ^ 1 :=
        (CRT_completed_power_mem_iff F v.val alpha 1).mp h1
      exact hmem (by simpa using h2)
    have hunit : IsUnit b := IsLocalRing.notMem_maximalIdeal.mp hbnot
    refine ⟨hunit.unit, ?_, ?_⟩
    · apply Units.ext
      rw [Units.coe_map, IsUnit.unit_spec]
      simp only [b, SArithmeticData.diagonal, MonoidHom.coe_mk, OneHom.coe_mk,
        FixedSResidue.fieldUnit, Units.val_mk0, hn]
      simp
      change ({toCompletion := ↑(WithVal.toVal (HeightOneSpectrum.valuation F v.val)
          (algebraMap (𝓞 F) F alpha))} : v.val.adicCompletion F)
        = algebraMap F (v.val.adicCompletion F) (algebraMap (𝓞 F) F alpha)
      rw [← IsScalarTower.algebraMap_apply (𝓞 F) F (v.val.adicCompletion F) alpha]
      rfl
    · simpa [IsUnit.unit_spec] using hb1
  have hinf : ∀ w : InfinitePlace F,
      ((sigma.1 w ((A.diagonal (fieldUnit A n)).1 w) : ℂ)⁻¹) = 1 := by
    intro w
    rw [hinfinite w]
    simp
  have hfin : ∀ v : {v // v ∈ A.Sf},
      ((sigma.2 v ((A.diagonal (fieldUnit A n)).2 v) : ℂ)⁻¹) = 1 := by
    intro v
    rw [(hcompat v).1 _ (hlocal v)]
    simp
  simp only [FixedSResidue.localInverseProduct, hinf, hfin, Finset.prod_const_one, mul_one]

end DedekindZetaZeroFree.Detector.ExteriorDyadic.ResidueFiberAdapter

end

section

namespace DedekindZetaZeroFree.Detector.ExteriorDyadic

noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain

theorem conductor_split_residue_modulus_bounds
    (F : Type) [Field F] [NumberField F] (A : SArithmeticData F)
    (f fS qO : Ideal (𝓞 F)) (hsplit : FixedSResidue.ConductorSplit A f fS qO) :
    FixedSResidue.residueModulus A qO ≠ ⊥ ∧
    Nonempty (Fintype (A.R ⧸ FixedSResidue.residueModulus A qO)) ∧
    Nat.card (A.R ⧸ FixedSResidue.residueModulus A qO) ≤ Ideal.absNorm f := by
  let Q : A.Exterior := ⟨qO, hsplit.2.2.1, hsplit.2.2.2.2.2⟩
  have hq : FixedSResidue.residueModulus A qO = A.extendIdeal Q := rfl
  rw [hq]
  letI := A.exteriorResidue_finite Q
  exact ⟨A.extendIdeal_ne_zero Q, ⟨Fintype.ofFinite _⟩, by
    rw [A.exteriorResidue_card Q]
    exact FixedSResidue.conductorSplit_norm_le A f fS qO hsplit⟩

open FixedSResidue FixedSInjectivity

theorem primitive_residue_fibers_of_decomposition
    (F : Type) [Field F] [NumberField F]
    (A : SArithmeticData F)
    (hprincipal : ExteriorPrincipalization A)
    (sigma : FullLocalCharacters A) (hSigma : HasFiniteOrder A sigma)
    (I : Type) [Fintype I] (omega : I → PrimitiveFrequencyCharacter F)
    (hdist : Pairwise (fun i j => ¬ samePrimitiveFrequencyCharacter F (omega i) (omega j)))
    (V : ℝ) (qO fS : I → Ideal (𝓞 F))
    (hsplit : ∀ i, ConductorSplit A (omega i).conductor (fS i) (qO i))
    (hlocal : ∀ i, SPrimeCompatibility A (omega i).conductor (omega i).character sigma)
    (htrivial : ∀ i, SLocalConductorTrivial A (fS i) sigma)
    (hfinite : ∀ i, Fintype (A.R ⧸ residueModulus A (qO i)))
    (hbound : ∀ i, (Nat.card (A.R ⧸ residueModulus A (qO i)) : ℝ) ≤ V)
    (lam : ∀ i, ResidueCharacter A (residueModulus A (qO i)))
    (hbridge : ∀ i, ExteriorDecomposition A (omega i).conductor
      (omega i).character sigma (residueModulus A (qO i)) (lam i)) :
    ∃ (r : ℕ) (g : I → Fin r) (q : Fin r → Ideal A.R)
      (hfinite : ∀ j, Fintype (A.R ⧸ q j))
      (chi : ∀ j, {i : I // g i = j} → MulChar (A.R ⧸ q j) ℂ),
      Function.Injective q ∧
      (∀ j, q j ≠ ⊥) ∧
      (∀ j, (Nat.card (A.R ⧸ q j) : ℝ) ≤ V) ∧
      (∀ j, Function.Injective (chi j)) ∧
      (∀ j i, IsPrimitiveResidueCharacter (chi j i)) ∧
      (∀ j (i : {i : I // g i = j}) (a : A.Exterior)
        (m : NonzeroSInteger A), Ideal.span {m.val} = A.extendIdeal a →
          (omega i).character a.val = localInverseProduct A sigma m *
            chi j i (Ideal.Quotient.mk (q j) m.val)) := by
  have transport_bridge (i : I) (Q : Ideal (𝓞 F)) (h : qO i = Q) :
      ExteriorDecomposition A (omega i).conductor (omega i).character sigma
        (residueModulus A Q)
        (Eq.mp (congrArg (fun Q => ResidueCharacter A (residueModulus A Q)) h) (lam i)) := by
    subst Q
    exact hbridge i
  have transport_primitive (i : I) (Q : Ideal (𝓞 F)) (h : qO i = Q) :
      IsPrimitiveResidueCharacter (residueZeroExtension A (residueModulus A Q)
        (Eq.mp (congrArg (fun Q => ResidueCharacter A (residueModulus A Q)) h) (lam i))) := by
    subst Q
    exact hecke_zeroExtension_isPrimitiveResidueCharacter A (omega i).conductor
      (fS i) (qO i) (omega i).character (omega i).primitive
      (hsplit i) sigma hSigma (lam i) (hbridge i) (htrivial i)
  let Q := Set.range qO
  letI : Fintype Q := (Set.finite_range qO).fintype
  let e : Q ≃ Fin (Fintype.card Q) := Fintype.equivFin Q
  let g : I → Fin (Fintype.card Q) := fun i => e ⟨qO i, i, rfl⟩
  let qO' : Fin (Fintype.card Q) → Ideal (𝓞 F) := fun j => (e.symm j).val
  let q : Fin (Fintype.card Q) → Ideal A.R := fun j => residueModulus A (qO' j)
  have hg : ∀ i j, g i = j → qO i = qO' j := by
    intro i j hij
    have h := congrArg (fun x => (e.symm x).val) hij
    simpa [g, qO'] using h
  let lift : ∀ j, {i : I // g i = j} → ResidueCharacter A (q j) :=
    fun j i => Eq.mp (congrArg (fun Q => ResidueCharacter A (residueModulus A Q))
      (hg i.val j i.property)) (lam i.val)
  have hq : ∀ j, qO' j ≠ ⊥ ∧ qO' j ⊔ A.cS = ⊤ := by
    intro j
    obtain ⟨i, hi⟩ := (e.symm j).property
    change (e.symm j).val ≠ ⊥ ∧ (e.symm j).val ⊔ A.cS = ⊤
    rw [← hi]
    exact ⟨(hsplit i).2.2.1, (hsplit i).2.2.2.2.2⟩
  refine ⟨Fintype.card Q, g, q, ?_, (fun j i => residueZeroExtension A (q j) (lift j i)),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    let i := Classical.choose (e.symm j).property
    have hi : qO i = (e.symm j).val := Classical.choose_spec (e.symm j).property
    change Fintype (A.R ⧸ residueModulus A (e.symm j).val)
    rw [← hi]
    exact hfinite i
  · intro j k hjk
    have he : qO' j = qO' k := by
      have h := congrArg (fun K : Ideal A.R => K.under (𝓞 F)) hjk
      dsimp [q, residueModulus] at h
      simpa only [SIntegerLocalization.under_map_exterior A.Sf _ (hq j).2,
        SIntegerLocalization.under_map_exterior A.Sf _ (hq k).2] using h
    exact e.symm.injective (Subtype.ext he)
  · intro j
    exact A.extendIdeal_ne_zero ⟨qO' j, hq j⟩
  · intro j
    obtain ⟨i, hi⟩ := (e.symm j).property
    change (Nat.card (A.R ⧸ residueModulus A (e.symm j).val) : ℝ) ≤ V
    rw [← hi]
    exact hbound i
  · intro j i k hik
    have hi := hg i.val j i.property
    have hk := hg k.val j k.property
    have hs := hsplit i.val
    have ht := hsplit k.val
    have hli := hlocal i.val
    have hlk := hlocal k.val
    have hp := (omega i.val).primitive
    have ht' := (omega k.val).primitive
    have hilam : lift j i = lift j k := by
      ext u
      have h := congrArg (fun c : MulChar (A.R ⧸ q j) ℂ => c (u : A.R ⧸ q j)) hik
      simpa only [residueZeroExtension_unit] using h
    have heq : (omega i.val).character.toFun = (omega k.val).character.toFun := by
      apply ideal_character_eq A hprincipal sigma hSigma
        (omega i.val).conductor (omega k.val).conductor (fS i.val) (fS k.val) (qO' j)
        (omega i.val).character (omega k.val).character hp ht'
        (hi ▸ hs) (hk ▸ ht) hli hlk (lift j i) (lift j k)
      · exact transport_bridge i.val (qO' j) hi
      · exact transport_bridge k.val (qO' j) hk
      · exact hilam
    apply Subtype.ext
    by_contra hn
    exact hdist hn (fun n => congrFun heq n)
  · intro j i
    exact transport_primitive i.val (qO' j) (hg i.val j i.property)
  · intro j i a m hm
    exact transport_bridge i.val (qO' j) (hg i.val j i.property) a m hm

theorem primitive_residue_fibers
    (F : Type) [Field F] [NumberField F]
    (A : SArithmeticData F)
    (hprincipal : FixedSInjectivity.ExteriorPrincipalization A)
    (sigma : FixedSResidue.FullLocalCharacters A)
    (hSigma : FixedSResidue.HasFiniteOrder A sigma)
    (I : Type) [Fintype I] (omega : I → PrimitiveFrequencyCharacter F)
    (hdist : Pairwise (fun i j =>
      ¬ samePrimitiveFrequencyCharacter F (omega i) (omega j)))
    (hlocal : ∀ i,
      (∀ w : InfinitePlace F, sigma.1 w = 1) ∧
        ∀ v : {v // v ∈ A.Sf},
          ∃ delta : (v.val.adicCompletion F)ˣ →ₜ* ℂˣ,
            delta.toMonoidHom = sigma.2 v ∧
              IsFrequencyLocalComponent F (omega i) v.val delta)
    (V : ℝ)
    (hconductor : ∀ i, (Ideal.absNorm (omega i).conductor : ℝ) ≤ V) :
    ∃ (r : ℕ) (g : I → Fin r) (q : Fin r → Ideal A.R)
      (hfinite : ∀ j, Fintype (A.R ⧸ q j))
      (chi : ∀ j, {i : I // g i = j} → MulChar (A.R ⧸ q j) ℂ),
      Function.Injective q ∧
      (∀ j, q j ≠ ⊥) ∧
      (∀ j, (Nat.card (A.R ⧸ q j) : ℝ) ≤ V) ∧
      (∀ j, Function.Injective (chi j)) ∧
      (∀ j i, IsPrimitiveResidueCharacter (chi j i)) ∧
      (∀ j (i : {i : I // g i = j}) (a : A.Exterior)
        (m : FixedSResidue.NonzeroSInteger A),
        Ideal.span {m.val} = A.extendIdeal a →
          (omega i).character a.val = FixedSResidue.localInverseProduct A sigma m *
            chi j i (Ideal.Quotient.mk (q j) m.val)) := by
  have hs : ∀ i, ∃ fS qO : Ideal (𝓞 F),
      ConductorSplit A (omega i).conductor fS qO := fun i =>
    ResidueFiberAdapter.exists_conductor_split F A (omega i).conductor
      (omega i).conductor_ne_zero
  choose fS qO hsplit using hs
  have hcompat : ∀ i, SPrimeCompatibility A (omega i).conductor
      (omega i).character sigma := fun i =>
    ResidueFiberAdapter.sprime_compatibility_of_frequency_local_components
      F A (omega i) sigma (hlocal i).2
  have htrivial : ∀ i, SLocalConductorTrivial A (fS i) sigma := fun i =>
    ResidueFiberAdapter.slocal_conductor_trivial_of_sprime_compatibility
      F A (omega i).conductor (fS i) (qO i) (omega i).character
      (hsplit i) sigma (hlocal i).1 (hcompat i)
  have hlam : ∀ i, ∃ lam : ResidueCharacter A (residueModulus A (qO i)),
      ExteriorDecomposition A (omega i).conductor (omega i).character sigma
        (residueModulus A (qO i)) lam := fun i =>
    ResidueFiberAdapter.exists_exterior_residue_character F A (omega i)
      (fS i) (qO i) (hsplit i) sigma (hlocal i).1 (hlocal i).2
  choose lam hbridge using hlam
  have hfinite : ∀ i, Fintype (A.R ⧸ residueModulus A (qO i)) := fun i =>
    Classical.choice (conductor_split_residue_modulus_bounds F A
      (omega i).conductor (fS i) (qO i) (hsplit i)).2.1
  have hbound : ∀ i, (Nat.card (A.R ⧸ residueModulus A (qO i)) : ℝ) ≤ V := by
    intro i
    exact (Nat.cast_le.mpr (conductor_split_residue_modulus_bounds F A
      (omega i).conductor (fS i) (qO i) (hsplit i)).2.2).trans (hconductor i)
  exact primitive_residue_fibers_of_decomposition F A hprincipal sigma hSigma
    I omega hdist V qO fS hsplit hcompat htrivial hfinite hbound lam hbridge

end
end DedekindZetaZeroFree.Detector.ExteriorDyadic

end
