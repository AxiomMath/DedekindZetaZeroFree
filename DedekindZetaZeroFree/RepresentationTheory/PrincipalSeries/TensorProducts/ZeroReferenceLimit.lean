module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.RestrictedTensorProduct
public import DedekindZetaZeroFree.Theta.Whittaker.LocalImageFactors

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.FourierContinuation.TensorActionSource
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

 def primeAbove {F : Type} [Field F] [NumberField F] (p : Nat.Primes) :
    HeightOneSpectrum (𝓞 F) := by
  letI : Fact p.val.Prime := ⟨p.property⟩
  let P : Ideal ℤ := Ideal.span {(p.val : ℤ)}
  letI : P.IsPrime := inferInstanceAs (Ideal.span {(p.val : ℤ)}).IsPrime
  let Q := Classical.choice (Ideal.nonempty_primesOver (S := 𝓞 F) P)
  refine ⟨Q.val, Q.property.1, ?_⟩
  intro hQ
  have he := Q.property.2.over
  rw [hQ, Ideal.under_bot] at he
  have hp0 := Ideal.span_singleton_eq_bot.mp he
  exact (by exact_mod_cast p.property.ne_zero : (p.val : ℤ) ≠ 0) hp0

private theorem primeAbove_under {F : Type} [Field F] [NumberField F] (p : Nat.Primes) :
    Ideal.under ℤ (primeAbove (F := F) p).asIdeal = Ideal.span {(p.val : ℤ)} := by
  letI : Fact p.val.Prime := ⟨p.property⟩
  exact (Classical.choice (Ideal.nonempty_primesOver (S := 𝓞 F)
    (Ideal.span {(p.val : ℤ)}))).property.2.over.symm

theorem finitePlaces_infinite (F : Type) [Field F] [NumberField F] :
    Infinite (KPFinitePlace F) := by
  apply Infinite.of_injective (primeAbove (F := F))
  intro p q hpq
  have he := congrArg (fun P : HeightOneSpectrum (𝓞 F) => Ideal.under ℤ P.asIdeal) hpq
  rw [primeAbove_under, primeAbove_under] at he
  apply Subtype.ext
  exact Int.associated_iff_natAbs.mp (Ideal.span_singleton_eq_span_singleton.mp he)

theorem zeroReferenceCore_subsingleton {J : Type*} [Infinite J]
    (V : J → Type*) [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
    (E : Finset J) : Subsingleton (RestrictedTensorSimple.Core V (fun _ => 0) E) := by
  suffices h : ∀ z : RestrictedTensorSimple.Core V (fun _ => 0) E, z = 0 from
    ⟨fun x y => (h x).trans (h y).symm⟩
  intro z
  letI : Nonempty (RestrictedTensorSimple.Level E) := ⟨⟨E, le_rfl⟩⟩
  obtain ⟨s, x, rfl⟩ := Module.DirectLimit.exists_of z
  have hex : ∃ j : J, j ∉ s.val := by
    by_contra h
    have hall : ∀ j : J, j ∈ s.val := by simpa using h
    have hf : (Set.univ : Set J).Finite :=
      s.val.finite_toSet.subset (fun j _ => hall j)
    exact Set.infinite_univ hf
  obtain ⟨j, hj⟩ := hex
  let t : RestrictedTensorSimple.Level E :=
    ⟨insert j s.val, s.property.trans (Finset.subset_insert j s.val)⟩
  have hst : s ≤ t := Finset.subset_insert j s.val
  have ht : RestrictedTensorSimple.transition V (fun _ => 0) E s t hst = 0 := by
    apply PiTensorProduct.ext
    ext u
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.zero_apply]
    rw [RestrictedTensorSimple.transition, RestrictedTensorSimple.insert_pure]
    have hu : (fun k : t.val => if h : (k : J) ∈ s.val then u ⟨k, h⟩ else (0 : V k))
        ⟨j, Finset.mem_insert_self _ _⟩ = 0 := by simp [hj]
    exact (PiTensorProduct.tprod ℂ).map_coord_zero ⟨j, Finset.mem_insert_self _ _⟩ hu
  change RestrictedTensorSimple.stageInclusion V (fun _ => 0) E s x = 0
  have hm : RestrictedTensorSimple.stageInclusion V (fun _ => 0) E t
      (RestrictedTensorSimple.transition V (fun _ => 0) E s t hst x) =
      RestrictedTensorSimple.stageInclusion V (fun _ => 0) E s x := Module.DirectLimit.of_f
  rw [← hm, ht, LinearMap.zero_apply, map_zero]

end DedekindZetaZeroFree.FourierContinuation.TensorActionSource

end
