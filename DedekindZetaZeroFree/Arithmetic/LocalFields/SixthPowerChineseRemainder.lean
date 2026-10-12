module

public import DedekindZetaZeroFree.Arithmetic.Units.SArithmeticData
public import DedekindZetaZeroFree.Algebra.PowerQuotientModules

@[expose] public section

namespace DedekindZetaZeroFree

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

 theorem cls_self (G : Type*) [CommGroup G] (n : ℕ) (g : G) :
    QuotientGroup.mk' (powMonoidHom (α := G) n).range (g ^ n) = 1 := by
  apply (QuotientGroup.eq_one_iff _).2
  exact ⟨g, rfl⟩
private theorem cls_congr (G : Type*) [CommGroup G] (n m k l : ℕ) (h : n*m=l*k)
    (a b : G) (hab : QuotientGroup.mk' (powMonoidHom (α := G) n).range a =
      QuotientGroup.mk' (powMonoidHom (α := G) n).range b) :
    QuotientGroup.mk' (powMonoidHom (α := G) k).range (a^m) =
      QuotientGroup.mk' (powMonoidHom (α := G) k).range (b^m) := by
  obtain ⟨z, hz, hab⟩ := (QuotientGroup.mk'_eq_mk' _).1 hab
  obtain ⟨t, rfl⟩ := hz
  rw [← hab, mul_pow, powMonoidHom_apply, ← pow_mul, h, pow_mul, map_mul, cls_self, mul_one]
 theorem cls_out (G : Type*) [CommGroup G] (n m k l : ℕ) (h : n*m=l*k) (a : G) :
    QuotientGroup.mk' (powMonoidHom (α := G) k).range
      ((Quotient.out (QuotientGroup.mk' (powMonoidHom (α := G) n).range a))^m) =
    QuotientGroup.mk' (powMonoidHom (α := G) k).range (a^m) := by
  apply cls_congr G n m k l h
  exact Quotient.out_eq _
 theorem cls_out_eq (G : Type*) [CommGroup G] (n : ℕ) (q : PowerQuotient G n) :
    QuotientGroup.mk' (powMonoidHom (α := G) n).range (Quotient.out q) = q :=
  Quotient.out_eq q

 theorem cls_ann (G : Type*) [CommGroup G] (n : ℕ)
    (q : PowerQuotient G n) : q ^ n = 1 := by
  induction q using Quotient.inductionOn with
  | h g =>
    change (QuotientGroup.mk' (powMonoidHom (α := G) n).range g)^n = 1
    rw [← map_pow]; exact cls_self G n g

 theorem crt_kernel (G : Type*) [CommGroup G] :
    (powMonoidHom (α := G) 6).range ≤
      (((QuotientGroup.mk' (powMonoidHom (α := G) 2).range).prod
        (QuotientGroup.mk' (powMonoidHom (α := G) 3).range))).ker := by
  rintro x ⟨g, rfl⟩
  apply Prod.ext
  · change QuotientGroup.mk' (powMonoidHom (α := G) 2).range (g^6) = 1
    convert cls_self G 2 (g^3) using 1 <;> rw [← pow_mul] <;> norm_num
  · change QuotientGroup.mk' (powMonoidHom (α := G) 3).range (g^6) = 1
    convert cls_self G 3 (g^2) using 1 <;> rw [← pow_mul] <;> norm_num

def sixthPowerCRT (G : Type*) [CommGroup G] :
    PowerQuotient G 6 ≃* PowerQuotient G 2 × PowerQuotient G 3 where
  toFun := QuotientGroup.lift (powMonoidHom (α := G) 6).range
    ((QuotientGroup.mk' (powMonoidHom (α := G) 2).range).prod
      (QuotientGroup.mk' (powMonoidHom (α := G) 3).range)) (crt_kernel G)
  invFun q := QuotientGroup.mk' (powMonoidHom (α := G) 6).range
    (Quotient.out q.1 ^ 3 * Quotient.out q.2 ^ 4)
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h g =>
      change QuotientGroup.mk' (powMonoidHom (α := G) 6).range
        (Quotient.out (QuotientGroup.mk' (powMonoidHom (α := G) 2).range g)^3 *
         Quotient.out (QuotientGroup.mk' (powMonoidHom (α := G) 3).range g)^4) = _
      rw [map_mul, cls_out G 2 3 6 1 (by decide), cls_out G 3 4 6 2 (by decide)]
      calc
        _ = QuotientGroup.mk' (powMonoidHom (α := G) 6).range (g * g^6) := by
          rw [← map_mul]; congr 1; group
        _ = _ := by rw [map_mul, cls_self, mul_one]; rfl
  right_inv := by
    rintro ⟨a, b⟩
    induction a using Quotient.inductionOn with
    | h a =>
      induction b using Quotient.inductionOn with
      | h b =>
        change (QuotientGroup.mk' (powMonoidHom (α := G) 2).range
          (Quotient.out (QuotientGroup.mk' (powMonoidHom (α := G) 2).range a)^3 *
           Quotient.out (QuotientGroup.mk' (powMonoidHom (α := G) 3).range b)^4),
          QuotientGroup.mk' (powMonoidHom (α := G) 3).range
          (Quotient.out (QuotientGroup.mk' (powMonoidHom (α := G) 2).range a)^3 *
           Quotient.out (QuotientGroup.mk' (powMonoidHom (α := G) 3).range b)^4)) = _
        apply Prod.ext
        · dsimp only [Prod.fst]
          rw [map_mul, map_pow, cls_out_eq]
          rw [show (3 : ℕ) = 1+2 from rfl, pow_add, cls_ann, mul_one, pow_one]
          rw [show (4 : ℕ) = 2*2 from rfl, pow_mul, map_pow, cls_self G 2, one_pow, mul_one]
          rfl
        · dsimp only [Prod.snd]
          rw [map_mul, cls_self G 3, one_mul, map_pow, cls_out_eq]
          rw [show (4 : ℕ) = 1+3 from rfl, pow_add, cls_ann, mul_one, pow_one]
          rfl
  map_mul' := by
    intro a b
    exact map_mul (QuotientGroup.lift (powMonoidHom (α := G) 6).range
      ((QuotientGroup.mk' (powMonoidHom (α := G) 2).range).prod
        (QuotientGroup.mk' (powMonoidHom (α := G) 3).range)) (crt_kernel G)) a b

 theorem pair_power_range (G H : Type*) [CommGroup G] [CommGroup H] (n : ℕ) :
    (powMonoidHom (α := G × H) n).range =
      ((powMonoidHom (α := G) n).range).prod ((powMonoidHom (α := H) n).range) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨⟨y.1, rfl⟩, ⟨y.2, rfl⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨(a,b), Prod.ext ha hb⟩
 def piPairPowerEquiv {I J : Type*} (G : I → Type*) (H : J → Type*)
    [∀ i, CommGroup (G i)] [∀ j, CommGroup (H j)] (n : ℕ) :
    PowerQuotient (((i : I) → G i) × ((j : J) → H j)) n ≃*
      (((i : I) → PowerQuotient (G i) n) × ((j : J) → PowerQuotient (H j) n)) :=
  (QuotientGroup.quotientMulEquivOfEq (pair_power_range _ _ n)).trans
    ((QuotientGroup.prodMulEquiv _ _).trans
      ((QuotientGroup.mulEquivPiModRangePowMonoidHom G n).prodCongr
       (QuotientGroup.mulEquivPiModRangePowMonoidHom H n)))
 theorem piPairPowerEquiv_apply {I J : Type*} (G : I → Type*) (H : J → Type*)
    [∀ i, CommGroup (G i)] [∀ j, CommGroup (H j)] (n : ℕ)
    (g : ((i : I) → G i) × ((j : J) → H j)) :
    piPairPowerEquiv G H n (QuotientGroup.mk' (powMonoidHom (α := (((i : I) → G i) × ((j : J) → H j))) n).range g) =
      (fun i => QuotientGroup.mk' (powMonoidHom (α := G i) n).range (g.1 i),
       fun j => QuotientGroup.mk' (powMonoidHom (α := H j) n).range (g.2 j)) := by
  rfl
namespace SArithmeticData

variable {F : Type} [Field F] [NumberField F]

abbrev LocalPowerClasses (A : SArithmeticData F) (n : ℕ) :=
  ((w : NumberField.InfinitePlace F) → PowerQuotient w.Completionˣ n) ×
  ((v : {v // v ∈ A.Sf}) → PowerQuotient (v.val.adicCompletion F)ˣ n)

abbrev V₂ (A : SArithmeticData F) := A.LocalPowerClasses 2

abbrev V₃ (A : SArithmeticData F) := A.LocalPowerClasses 3

def localPowerQuotientEquiv (A : SArithmeticData F) (n : ℕ) :
    PowerQuotient A.G n ≃* A.LocalPowerClasses n where
  toFun := QuotientGroup.lift (powMonoidHom (α := A.G) n).range
    { toFun := fun g =>
        ((fun w => QuotientGroup.mk' (powMonoidHom (α := w.Completionˣ) n).range (g.1 w)),
         (fun v => QuotientGroup.mk'
           (powMonoidHom (α := (v.val.adicCompletion F)ˣ) n).range (g.2 v)))
      map_one' := by ext <;> simp
      map_mul' := by intros; ext <;> simp }
    (by
      rintro g ⟨x, rfl⟩
      apply Prod.ext <;> funext i
      · change QuotientGroup.mk' (powMonoidHom (α := i.Completionˣ) n).range ((x.1 i)^n) = 1
        exact cls_self _ n _
      · change QuotientGroup.mk' (powMonoidHom (α := (i.val.adicCompletion F)ˣ) n).range ((x.2 i)^n) = 1
        exact cls_self _ n _)
  invFun q := QuotientGroup.mk' (powMonoidHom (α := A.G) n).range
    ((fun w => Quotient.out (q.1 w)), (fun v => Quotient.out (q.2 v)))
  left_inv := by
    intro q
    apply (piPairPowerEquiv (fun w : NumberField.InfinitePlace F => w.Completionˣ)
      (fun v : {v // v ∈ A.Sf} => (v.val.adicCompletion F)ˣ) n).injective
    induction q using Quotient.inductionOn with
    | h g =>
      rw [piPairPowerEquiv_apply]
      change (fun w => QuotientGroup.mk' (powMonoidHom (α := w.Completionˣ) n).range
          (Quotient.out (QuotientGroup.mk' (powMonoidHom (α := w.Completionˣ) n).range (g.1 w))),
        fun v => QuotientGroup.mk' (powMonoidHom (α := (v.val.adicCompletion F)ˣ) n).range
          (Quotient.out (QuotientGroup.mk' (powMonoidHom (α := (v.val.adicCompletion F)ˣ) n).range (g.2 v)))) = _
      change (fun w => QuotientGroup.mk' (powMonoidHom (α := w.Completionˣ) n).range
          (Quotient.out (QuotientGroup.mk' (powMonoidHom (α := w.Completionˣ) n).range (g.1 w))),
        fun v => QuotientGroup.mk' (powMonoidHom (α := (v.val.adicCompletion F)ˣ) n).range
          (Quotient.out (QuotientGroup.mk' (powMonoidHom (α := (v.val.adicCompletion F)ˣ) n).range (g.2 v)))) =
        (fun w => QuotientGroup.mk' (powMonoidHom (α := w.Completionˣ) n).range (g.1 w),
         fun v => QuotientGroup.mk' (powMonoidHom (α := (v.val.adicCompletion F)ˣ) n).range (g.2 v))
      apply Prod.ext <;> funext i <;> exact cls_out_eq _ n _
  right_inv := by
    intro q
    change (fun w => QuotientGroup.mk' (powMonoidHom (α := w.Completionˣ) n).range (Quotient.out (q.1 w)),
      fun v => QuotientGroup.mk' (powMonoidHom (α := (v.val.adicCompletion F)ˣ) n).range (Quotient.out (q.2 v))) = q
    apply Prod.ext <;> funext i <;> exact cls_out_eq _ n _
  map_mul' := by
    intro a b
    induction a using Quotient.inductionOn with
    | h a =>
      induction b using Quotient.inductionOn with
      | h b =>
        change (fun w => QuotientGroup.mk' (powMonoidHom (α := w.Completionˣ) n).range ((a*b).1 w),
          fun v => QuotientGroup.mk' (powMonoidHom (α := (v.val.adicCompletion F)ˣ) n).range ((a*b).2 v)) = _
        apply Prod.ext <;> funext i
        · change QuotientGroup.mk' (powMonoidHom (α := i.Completionˣ) n).range ((a.1 i)*(b.1 i)) =
            QuotientGroup.mk' (powMonoidHom (α := i.Completionˣ) n).range (a.1 i) *
            QuotientGroup.mk' (powMonoidHom (α := i.Completionˣ) n).range (b.1 i)
          exact map_mul _ _ _
        · change QuotientGroup.mk' (powMonoidHom (α := (i.val.adicCompletion F)ˣ) n).range ((a.2 i)*(b.2 i)) =
            QuotientGroup.mk' (powMonoidHom (α := (i.val.adicCompletion F)ˣ) n).range (a.2 i) *
            QuotientGroup.mk' (powMonoidHom (α := (i.val.adicCompletion F)ˣ) n).range (b.2 i)
          exact map_mul _ _ _

def localSixthPowerCRT (A : SArithmeticData F) : A.V ≃* A.V₂ × A.V₃ :=
  (sixthPowerCRT A.G).trans
    ((A.localPowerQuotientEquiv 2).prodCongr (A.localPowerQuotientEquiv 3))

theorem localSixthPowerCRT_apply (A : SArithmeticData F) (g : A.G) :
    A.localSixthPowerCRT (QuotientGroup.mk' A.sixthPowers g) =
      (((fun w => QuotientGroup.mk' (powMonoidHom (α := w.Completionˣ) 2).range (g.1 w)),
       (fun v => QuotientGroup.mk'
         (powMonoidHom (α := (v.val.adicCompletion F)ˣ) 2).range (g.2 v))),
       ((fun w => QuotientGroup.mk' (powMonoidHom (α := w.Completionˣ) 3).range (g.1 w)),
        (fun v => QuotientGroup.mk'
          (powMonoidHom (α := (v.val.adicCompletion F)ˣ) 3).range (g.2 v)))) := by
  rfl

end SArithmeticData
end
end DedekindZetaZeroFree
