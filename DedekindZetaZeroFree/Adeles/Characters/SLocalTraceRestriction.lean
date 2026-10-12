module

public import DedekindZetaZeroFree.Adeles.Characters.TraceCharacter
public import DedekindZetaZeroFree.Adeles.Lattices.SIntegerLocalProduct

@[expose] public section

noncomputable section

open scoped NumberField BigOperators Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree

variable (F : Type) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

def zeroExtendS : SLocalProduct F S →+ AdeleRing (𝓞 F) F where
  toFun x := (x.1, ∑ v : S, RestrictedProduct.single
    (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v.1 (x.2 v))
  map_zero' := by
    apply Prod.ext
    · rfl
    · change (∑ v : S, RestrictedProduct.single
        (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v.1 0) = 0
      simp
  map_add' := by
    intro x y
    apply Prod.ext
    · rfl
    · change (∑ v : S, RestrictedProduct.single
        (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v.1
        (x.2 v + y.2 v)) = _ + _
      simp only [RestrictedProduct.single_add, Finset.sum_add_distrib]
      rfl

@[simp] theorem zeroExtendS_infinite (x : SLocalProduct F S) (v : InfinitePlace F) :
    (zeroExtendS F S x).1 v = x.1 v := by
  rfl

@[simp] theorem zeroExtendS_finite (x : SLocalProduct F S) (v : S) :
    (zeroExtendS F S x).2 v.1 = x.2 v := by
  change (∑ w : S, RestrictedProduct.single
    (fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletionIntegers F) w.1 (x.2 w)) v.1 = _
  rw [show (∑ w : S, RestrictedProduct.single
      (fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletionIntegers F) w.1 (x.2 w)) v.1 =
      ∑ w : S, (RestrictedProduct.single
        (fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletionIntegers F) w.1 (x.2 w)) v.1
    from map_sum (RestrictedProduct.evalAddMonoidHom _ v.1) _ _]
  rw [Finset.sum_eq_single v]
  · exact RestrictedProduct.single_eq_same _ _ _
  · intro w hw hne
    exact RestrictedProduct.single_eq_of_ne _ _ (fun h => hne (Subtype.ext h.symm))
  · simp

@[simp] theorem zeroExtendS_finite_of_not_mem (x : SLocalProduct F S)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
    (zeroExtendS F S x).2 v = 0 := by
  change (∑ w : S, RestrictedProduct.single
    (fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletionIntegers F) w.1 (x.2 w)) v = 0
  rw [show (∑ w : S, RestrictedProduct.single
      (fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletionIntegers F) w.1 (x.2 w)) v =
      ∑ w : S, (RestrictedProduct.single
        (fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletionIntegers F) w.1 (x.2 w)) v
    from map_sum (RestrictedProduct.evalAddMonoidHom _ v) _ _]
  apply Finset.sum_eq_zero
  intro w hw
  exact RestrictedProduct.single_eq_of_ne _ _ (fun h => hv (h ▸ w.2))

private theorem continuous_finite_single (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (RestrictedProduct.single
      (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v) := by
  let t : v.adicCompletion F → RestrictedProduct
      (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      (fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F)))
      (Filter.principal {v}ᶜ) :=
    fun z => ⟨Pi.single v z, by
      intro w hw
      have hwv : w ≠ v := hw
      change Pi.single v z w ∈ w.adicCompletionIntegers F
      rw [Pi.single_eq_of_ne hwv]
      exact (w.adicCompletionIntegers F).zero_mem⟩
  have ht : Continuous t := by
    apply RestrictedProduct.continuous_rng_of_principal.mpr
    apply continuous_pi
    intro w
    change Continuous (fun z : v.adicCompletion F => Pi.single v z w)
    by_cases hw : w = v
    · subst w
      rw [show (fun z : v.adicCompletion F => Pi.single v z v) = id from
        funext (fun z => Pi.single_eq_same v z)]
      exact continuous_id
    · simpa only [Pi.single_eq_of_ne hw] using
        (continuous_const : Continuous (fun _ : v.adicCompletion F => (0 : w.adicCompletion F)))
  have h : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) := by
    simp
  exact (RestrictedProduct.continuous_inclusion h).comp ht

theorem continuous_zeroExtendS :
    Continuous (zeroExtendS F S : SLocalProduct F S → AdeleRing (𝓞 F) F) := by
  change Continuous (fun x : SLocalProduct F S => (x.1, ∑ v : S,
    RestrictedProduct.single
      (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v.1 (x.2 v)))
  letI : ContinuousAdd (RestrictedProduct
      (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      (fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F)))
      Filter.cofinite) := inferInstanceAs (ContinuousAdd (FiniteAdeleRing (𝓞 F) F))
  apply Continuous.prodMk continuous_fst
  apply continuous_finset_sum
  intro v hv
  exact (continuous_finite_single F v.1).comp ((continuous_apply v).comp continuous_snd)

def sLocalTraceCharacter : AddChar (SLocalProduct F S) Circle :=
  (adelicTraceCharacter F).compAddMonoidHom (zeroExtendS F S)

theorem sLocalTraceCharacter_zeroExtend (x : SLocalProduct F S) :
    sLocalTraceCharacter F S x = adelicTraceCharacter F (zeroExtendS F S x) := by
  rfl

theorem sLocalTraceCharacter_apply (x : SLocalProduct F S) :
    sLocalTraceCharacter F S x =
      (∏ v : InfinitePlace F, archTraceCharacter v (x.1 v)) *
        (∏ v : S, localFiniteCharacter F v.1 (x.2 v)) := by
  rw [sLocalTraceCharacter_zeroExtend, adelicTraceCharacter_apply]
  simp only [zeroExtendS_infinite]
  congr 1
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) (by
    intro v hv
    by_contra hvm
    have hzero := zeroExtendS_finite_of_not_mem F S x v hvm
    exact hv (by
      dsimp only
      rw [hzero]
      exact (localFiniteCharacter F v).map_zero_eq_one))]
  rw [← Finset.prod_coe_sort]
  apply Finset.prod_congr rfl
  intro v hv
  rw [zeroExtendS_finite]

theorem continuous_sLocalTraceCharacter :
    Continuous (sLocalTraceCharacter F S : SLocalProduct F S → Circle) := by
  exact (continuous_adelicTraceCharacter F).comp (continuous_zeroExtendS F S)

end DedekindZetaZeroFree

end
