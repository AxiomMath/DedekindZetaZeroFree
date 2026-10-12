module

public import DedekindZetaZeroFree.Adeles.Characters.FiniteTraceCharacterContinuity

@[expose] public section

noncomputable section

open scoped NumberField BigOperators Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree

variable (F : Type) [Field F] [NumberField F]

def adelicTraceCharacter : AddChar (AdeleRing (𝓞 F) F) Circle where
  toFun x :=
    (∏ v : InfinitePlace F, archTraceCharacter v (x.1 v)) *
      (∏ᶠ v : HeightOneSpectrum (𝓞 F), localFiniteCharacter F v (x.2 v))
  map_zero_eq_one' := by
    change (∏ v : InfinitePlace F, archTraceCharacter v (0 : v.Completion)) *
      (∏ᶠ v : HeightOneSpectrum (𝓞 F), localFiniteCharacter F v (0 : v.adicCompletion F)) = 1
    simp
  map_add_eq_mul' := by
    intro x y
    change (∏ v : InfinitePlace F, archTraceCharacter v (x.1 v + y.1 v)) *
      (∏ᶠ v : HeightOneSpectrum (𝓞 F), localFiniteCharacter F v (x.2 v + y.2 v)) = _
    simp only [AddChar.map_add_eq_mul]
    rw [Finset.prod_mul_distrib, finprod_mul_distrib
      (localFiniteCharacter_adele_hasFiniteMulSupport F x)
      (localFiniteCharacter_adele_hasFiniteMulSupport F y)]
    ac_rfl

theorem adelicTraceCharacter_apply (x : AdeleRing (𝓞 F) F) :
    adelicTraceCharacter F x =
      (∏ v : InfinitePlace F, archTraceCharacter v (x.1 v)) *
        (∏ᶠ v : HeightOneSpectrum (𝓞 F), localFiniteCharacter F v (x.2 v)) := by
  rfl

theorem continuous_adelicTraceCharacter :
    Continuous (adelicTraceCharacter F : AdeleRing (𝓞 F) F → Circle) := by
  change Continuous (fun x : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F => _)
  apply Continuous.mul
  · apply continuous_finset_prod
    intro v hv
    exact (continuous_archTraceCharacter v).comp
      ((continuous_apply v).comp continuous_fst)
  · exact (RepresentationTheory.AdelicTraceCharacterHelpers.finiteCharacter_product_continuous F).comp
      continuous_snd

theorem adelicTraceCharacter_arch_single (v : InfinitePlace F)
    (z : v.Completion) :
    adelicTraceCharacter F ((Pi.single v z, 0) : AdeleRing (𝓞 F) F) =
      archTraceCharacter v z := by
  set_option backward.isDefEq.respectTransparency false in
    rw [adelicTraceCharacter_apply]
  change (∏ w : InfinitePlace F, archTraceCharacter w (Pi.single v z w)) *
    (∏ᶠ w : HeightOneSpectrum (𝓞 F),
      localFiniteCharacter F w (0 : w.adicCompletion F)) = _
  simp only [AddChar.map_zero_eq_one, finprod_one, mul_one]
  rw [Finset.prod_eq_single v]
  · simp
  · intro w hw hwv
    simp [Pi.single_eq_of_ne hwv]
  · simp

theorem adelicTraceCharacter_finite_single (v : HeightOneSpectrum (𝓞 F))
    (z : v.adicCompletion F) :
    adelicTraceCharacter F
      ((0, RestrictedProduct.single (fun w : HeightOneSpectrum (𝓞 F) =>
        w.adicCompletionIntegers F) v z) : AdeleRing (𝓞 F) F) =
      localFiniteCharacter F v z := by
  set_option backward.isDefEq.respectTransparency false in
    rw [adelicTraceCharacter_apply]
  change (∏ w : InfinitePlace F, archTraceCharacter w (0 : w.Completion)) *
    (∏ᶠ w : HeightOneSpectrum (𝓞 F), localFiniteCharacter F w
      (RestrictedProduct.single (fun w : HeightOneSpectrum (𝓞 F) =>
        w.adicCompletionIntegers F) v z w)) = _
  simp only [AddChar.map_zero_eq_one, Finset.prod_const_one, one_mul]
  rw [finprod_eq_single _ v]
  · simp
  · intro w hw
    simp [RestrictedProduct.single_eq_of_ne _ _ hw]

theorem adelicTraceCharacter_diagonal (t : F) :
    adelicTraceCharacter F (algebraMap F (AdeleRing (𝓞 F) F) t) = 1 := by
  exact traceCharacter_diagonal_product_formula F t

def adelicTraceQuotientCharacter :
    AddChar (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F) Circle :=
  AddChar.toAddMonoidHomEquiv.symm
    (QuotientAddGroup.lift (AdeleRing.principalSubgroup (𝓞 F) F)
      (adelicTraceCharacter F).toAddMonoidHom (by
          intro x hx
          obtain ⟨t, rfl⟩ := hx
          change adelicTraceCharacter F (algebraMap F (AdeleRing (𝓞 F) F) t) = 1
          exact adelicTraceCharacter_diagonal F t))

theorem adelicTraceQuotientCharacter_mk (x : AdeleRing (𝓞 F) F) :
    adelicTraceQuotientCharacter F
      (QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F) x) =
      adelicTraceCharacter F x := by
  rfl

theorem continuous_adelicTraceQuotientCharacter :
    Continuous (adelicTraceQuotientCharacter F :
      (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F) → Circle) := by
  apply (QuotientAddGroup.isQuotientMap_mk
    (AdeleRing.principalSubgroup (𝓞 F) F)).continuous_iff.mpr
  change Continuous (adelicTraceCharacter F : AdeleRing (𝓞 F) F → Circle)
  exact continuous_adelicTraceCharacter F

end DedekindZetaZeroFree

end
