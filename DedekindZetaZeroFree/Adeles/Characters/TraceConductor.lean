module

public import DedekindZetaZeroFree.Moments.Probes.PrincipalArithmeticEnlargement

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.PrincipalProbeConstruction
variable {F : Type} [Field F] [NumberField F]
private theorem prime_eq (v : HeightOneSpectrum (𝓞 F)) :
    ResidueTrace.rationalPrimeBelow v = PlaceTraceAdapter.prime F v := by
  apply Subtype.ext
  change ringChar (𝓞 F ⧸ v.asIdeal) = Rat.HeightOneSpectrum.natGenerator _
  rw [Ideal.ringChar_quot]
  have h := Rat.HeightOneSpectrum.span_natGenerator (PlaceTraceAdapter.rationalPlace F v)
  have he : (v.asIdeal.under ℤ) =
      (PlaceTraceAdapter.rationalPlace F v).asIdeal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) := by
    ext x
    rw [← Ideal.comap_symm]
    rw [Ideal.mem_comap]
    change algebraMap ℤ (𝓞 F) x ∈ v.asIdeal ↔
      algebraMap (𝓞 ℚ) (𝓞 F) ((Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm x) ∈ v.asIdeal
    rw [DFunLike.congr_fun (RingHom.ext_int (algebraMap ℤ (𝓞 F))
      ((algebraMap (𝓞 ℚ) (𝓞 F)).comp (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm.toRingHom)) x]
    rfl
  rw [he, ← h, Ideal.absNorm_span_singleton]
  simp
private theorem continuous_cast_map {p q : Nat.Primes} {K : Type} [Field K]
    [TopologicalSpace K] (h : p = q) (j : ℚ_[q] →+* K) (hc : Continuous j) :
    Continuous ((cast (congrArg (fun p : Nat.Primes => ℚ_[p] →+* K) h.symm) j) :
      ℚ_[p] →+* K) := by
  subst q
  exact hc

private theorem traceChar_cast {p q : Nat.Primes} {K : Type} [Field K]
    (h : p = q) (j : ℚ_[q] →+* K) :
    (letI := (cast (congrArg (fun p : Nat.Primes => ℚ_[p] →+* K) h.symm) j).toAlgebra
     letI : Fact p.1.Prime := ⟨p.2⟩
     (rationalPadicCharacter p).compAddMonoidHom (Algebra.trace ℚ_[p] K).toAddMonoidHom) =
    (letI := j.toAlgebra
     letI : Fact q.1.Prime := ⟨q.2⟩
     (rationalPadicCharacter q).compAddMonoidHom (Algebra.trace ℚ_[q] K).toAddMonoidHom) := by
  subst q
  rfl

private theorem char_eq (v : HeightOneSpectrum (𝓞 F)) :
    ResidueTrace.localTraceCharacter v = localFiniteCharacter F v := by
  have hp := prime_eq v
  have hmap : Continuous (PlaceTraceAdapter.padicMap F v) := by
    letI : Algebra ℚ ((PlaceTraceAdapter.rationalPlace F v).adicCompletion ℚ) :=
      HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ (PlaceTraceAdapter.rationalPlace F v)
    exact (finitePlaceAdicCompletionMap_continuous ℚ F
      (PlaceTraceAdapter.rationalPlace F v) ⟨v, rfl⟩).comp
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv
        (PlaceTraceAdapter.rationalPlace F v)).symm.continuous
  let j : ℚ_[ResidueTrace.rationalPrimeBelow v] →+* v.adicCompletion F :=
    cast (congrArg (fun p : Nat.Primes => ℚ_[p] →+* v.adicCompletion F) hp.symm)
      (PlaceTraceAdapter.padicMap F v)
  have hj (q : ℚ) : j (q : ℚ_[ResidueTrace.rationalPrimeBelow v]) =
      algebraMap F (v.adicCompletion F) (algebraMap ℚ F q) := by
    exact DFunLike.congr_fun (RingHom.ext_rat (j.comp (algebraMap ℚ _))
      ((algebraMap F _).comp (algebraMap ℚ F))) q
  have hc : Continuous j := continuous_cast_map hp _ hmap
  have hb : j = ResidueTrace.baseEmbedding v :=
    (Classical.choose_spec (ResidueTrace.existsUnique_baseEmbedding v)).2 j ⟨hc, hj⟩
  unfold ResidueTrace.localTraceCharacter localFiniteCharacter PlaceTraceAdapter.trace
  rw [← hb]
  exact traceChar_cast hp (PlaceTraceAdapter.padicMap F v)
private theorem phase_single (A : SArithmeticData F) (v : ↥A.Sf)
    (u : PoissonFinite.Space F A.Sf) (y : v.val.adicCompletion F) :
    PoissonS.finiteBallTraceCharacter F A.Sf
      (u * (Pi.single v y : PoissonFinite.Space F A.Sf)) =
      localFiniteCharacter F v.val (u v * y) := by
  rw [PoissonS.finiteBallTraceCharacter_apply, Finset.prod_eq_single v]
  · simp only [Pi.mul_apply, Pi.single_eq_same]
  · intro w hw hne
    have hs : (Pi.single v y : PoissonFinite.Space F A.Sf) w = 0 := by
      simp [Pi.single_eq_of_ne hne]
    simp only [Pi.mul_apply, hs, mul_zero]
    exact AddChar.map_zero_eq_one _
  · intro hn
    exact False.elim (hn (Finset.mem_univ v))

set_option backward.isDefEq.respectTransparency false in
private theorem conductor_localFinite (A : SArithmeticData F) :
    PoissonS.TraceConductor F A.Sf (fun v => localFiniteCharacter F v.val) := by
  intro v y
  have hball := congrArg (fun E : Set (PoissonFinite.Space F A.Sf) =>
      (Pi.single v y : PoissonFinite.Space F A.Sf) ∈ E)
    (PoissonS.finiteBallAnnihilator_eq F A.Sf (fun _ => 0))
  have hball' := Iff.of_eq hball
  simp only [PoissonS.finiteBallAnnihilator, PoissonS.finiteBall,
    Set.mem_setOf_eq, sub_zero, neg_neg, neg_zero, zpow_zero] at hball'
  constructor
  · intro h
    have ha := hball'.mp (fun u hu => by
      rw [phase_single A v]
      apply h
      simpa [PoissonS.finiteBall] using hu v)
    simpa only [Pi.single_eq_same] using ha v
  · intro h
    have ha := hball'.mpr (fun w => by
      by_cases hw : w = v
      · subst w
        simpa only [Pi.single_eq_same] using h
      · simp only [Pi.single_eq_of_ne hw, norm_zero]
        exact le_of_lt (zpow_pos (by exact_mod_cast
          (Nat.zero_lt_of_lt (NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm w.val))) _))
    intro x hx
    let u : PoissonFinite.Space F A.Sf := Pi.single v x
    have hu : u ∈ PoissonS.finiteBall F A.Sf (fun _ => 0) := by
      intro w
      by_cases hw : w = v
      · subst w
        simpa [u] using hx
      · simp [u, Pi.single_eq_of_ne hw]
    have hh := ha u hu
    simpa [phase_single A v, u] using hh

theorem canonical_trace_conductor (A : SArithmeticData F) :
    PoissonS.TraceConductor F A.Sf
      (fun v => ResidueTrace.localTraceCharacter v.val) := by
  have hc := conductor_localFinite A
  intro v y
  simpa only [char_eq] using hc v y

end DedekindZetaZeroFree.PrincipalProbeConstruction
