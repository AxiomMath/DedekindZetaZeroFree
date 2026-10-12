module

public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.Hilbert.ProductFormula
public import DedekindZetaZeroFree.Arithmetic.LocalFields.ProductPowerClassRank

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.SArithmeticData
noncomputable section
set_option autoImplicit false
variable {F : Type} [Field F] [NumberField F]

def H_Sn (A : SArithmeticData F) (n : ℕ+) (hn : IsLocalRootOrder n) :
    Vn F A n →* Vn F A n →* rootsOfUnity n F where
  toFun x :=
    { toFun := fun y => ∏ v : {v // v ∈ A.Sf},
        A.actualLocalHilbert v.val n hn (x (Sum.inr v)) (y (Sum.inr v))
      map_one' := by simp
      map_mul' := by
        intro y z
        change (∏ v : {v // v ∈ A.Sf},
          A.actualLocalHilbert v.val n hn (x (Sum.inr v))
            (y (Sum.inr v) * z (Sum.inr v))) = _
        simp only [map_mul, Finset.prod_mul_distrib] }
  map_one' := by
    apply MonoidHom.ext
    intro y
    change (∏ v : {v // v ∈ A.Sf},
      A.actualLocalHilbert v.val n hn 1 (y (Sum.inr v))) = 1
    simp
  map_mul' := by
    intro x z
    apply MonoidHom.ext
    intro y
    change (∏ v : {v // v ∈ A.Sf},
      A.actualLocalHilbert v.val n hn (x (Sum.inr v) * z (Sum.inr v))
        (y (Sum.inr v))) = _
    simp only [map_mul, MonoidHom.mul_apply, Finset.prod_mul_distrib]
    rfl

theorem H_Sn_apply (A : SArithmeticData F) (n : ℕ+) (hn : IsLocalRootOrder n)
    (x y : Vn F A n) :
    A.H_Sn n hn x y = ∏ v : {v // v ∈ A.Sf},
      A.actualLocalHilbert v.val n hn (x (Sum.inr v)) (y (Sum.inr v)) := rfl

theorem H_Sn_mul_left (A : SArithmeticData F) (n : ℕ+) (hn : IsLocalRootOrder n)
    (x z y : Vn F A n) :
    A.H_Sn n hn (x * z) y = A.H_Sn n hn x y * A.H_Sn n hn z y := by
  exact congrArg (fun f => f y) (map_mul (A.H_Sn n hn) x z)

private theorem rawNegSelf (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (n : ℕ+) (hn : IsLocalRootOrder n)
    (a : (v.adicCompletion F)ˣ) :
    A.actualRawHilbert n hn v (ClassFieldTheory.powerClass _ n a)
      (ClassFieldTheory.powerClass _ n (-a)) = 1 := by
  let C := (HeightOneSpectrum.adicAbv F v).Completion
  letI : ValuativeRel C :=
    GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinCompletionValuativeRel v
  letI : IsNonarchimedeanLocalField C :=
    GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  letI : CharZero C := charZero_of_injective_algebraMap (algebraMap F C).injective
  let e := (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv
  let eu := Units.mapEquiv e.toMulEquiv
  have hroots : (primitiveRoots (n : ℕ) C).Nonempty := by
    obtain ⟨ζ, hζ⟩ := A.actualHilbert_roots n hn
    exact ⟨algebraMap F C ζ, (mem_primitiveRoots n.pos).2
      (((mem_primitiveRoots n.pos).1 hζ).map_of_injective (algebraMap F C).injective)⟩
  change ClassFieldTheory.hilbertPairingOfRingEquiv e n hroots
    (ClassFieldTheory.localHilbertPairing C n (Nat.cast_ne_zero.mpr n.ne_zero) hroots)
    (ClassFieldTheory.powerClass _ n a) (ClassFieldTheory.powerClass _ n (-a)) = 1
  rw [ClassFieldTheory.hilbertPairingOfRingEquiv_apply,
    ClassFieldTheory.powerClassGroupEquivOfRingEquiv_symm_powerClass,
    ClassFieldTheory.powerClassGroupEquivOfRingEquiv_symm_powerClass,
    ClassFieldTheory.localHilbertPairing_powerClass]
  have hneg : eu.symm (-a) = -(eu.symm a) := by
    apply Units.ext
    exact map_neg e.symm _
  change (ClassFieldTheory.rootsOfUnityEquivOfRingEquiv e n hroots)
    (KummerTheory.nthRootsSubgroupEquivRootsOfUnity C n
      (LocalClassFieldTheory.Kummer.localHilbertSymbol C n
        (Nat.cast_ne_zero.mpr n.ne_zero) hroots (eu.symm a) (eu.symm (-a)))) = 1
  rw [hneg, LocalClassFieldTheory.Kummer.localHilbertSymbol_neg_self,
    map_one, map_one]

private theorem localAlternating (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (n : ℕ+) (hn : IsLocalRootOrder n)
    (a : PowerQuotient (v.adicCompletion F)ˣ n) :
    A.actualLocalHilbert v n hn a a = 1 := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨r, hr⟩ := A.finite_neg_one_isPower v n hn
  have hr0 : r ≠ 0 := by
    intro h0
    simp [h0, n.ne_zero] at hr
  let ru : (v.adicCompletion F)ˣ := Units.mk0 r hr0
  have hru : ru ^ (n : ℕ) = -1 := Units.ext (by simpa [ru] using hr)
  have hneg : ClassFieldTheory.powerClass (v.adicCompletion F) n (-1) = 1 := by
    change QuotientGroup.mk' (powMonoidHom (α := (v.adicCompletion F)ˣ) n).range (-1) = 1
    exact (QuotientGroup.eq_one_iff _).2 ⟨ru, hru⟩
  have hclass : ClassFieldTheory.powerClass (v.adicCompletion F) n (-u) =
      ClassFieldTheory.powerClass (v.adicCompletion F) n u := by
    rw [show -u = (-1) * u by simp]
    change QuotientGroup.mk' _ ((-1) * u) = _
    rw [map_mul]
    change ClassFieldTheory.powerClass _ n (-1) * _ = _
    rw [hneg]
    exact one_mul _
  apply (A.finiteRootsEquiv v n hn).injective
  change A.finiteRootsEquiv v n hn (A.actualLocalHilbert v n hn
    (ClassFieldTheory.powerClass _ n u) (ClassFieldTheory.powerClass _ n u)) =
    A.finiteRootsEquiv v n hn 1
  have hs := rawNegSelf A v n hn u
  rw [hclass] at hs
  exact (A.actualLocalHilbert_local_value v n hn _ _).trans
    ((congrArg Inv.inv hs).trans (by simp))

theorem H_Sn_alternating (A : SArithmeticData F) (n : ℕ+)
    (hn : (n : ℕ) = 2 ∨ (n : ℕ) = 3) (x : Vn F A n) :
    A.H_Sn n (hn.elim Or.inl (fun h => Or.inr (Or.inl h))) x x = 1 := by
  rw [H_Sn_apply]
  apply Finset.prod_eq_one
  intro v hv
  exact localAlternating A v.val n _ _

private theorem localPerfect (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (n : ℕ+) (hn : IsLocalRootOrder n) :
    Function.Bijective (A.actualLocalHilbert v n hn) := by
  letI : ValuativeRel (v.adicCompletion F) :=
    ClassFieldTheory.finitePlaceCompletionValuativeRel F v
  letI : IsNonarchimedeanLocalField (v.adicCompletion F) :=
    ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F v
  letI : Finite (ClassFieldTheory.PowerClassGroup (v.adicCompletion F) n) :=
    ClassFieldTheory.powerClassGroup_finite _ n (A.finite_natCast_ne_zero v n hn)
  have hraw := (A.actualRawHilbert_isLocal n hn v).2.2.1.bijective
    ⟨_, (mem_primitiveRoots n.pos).2 (A.finite_primitive_root v n hn)⟩
  constructor
  · intro a b hab
    have hOne : A.actualLocalHilbert v n hn (a * b⁻¹) = 1 := by
      rw [map_mul, map_inv, hab, mul_inv_cancel]
    exact mul_inv_eq_one.mp (A.actualLocalHilbert_left_nondegenerate v n hn _
      (fun c => DFunLike.congr_fun hOne c))
  · intro f
    let e := A.finiteRootsEquiv v n hn
    obtain ⟨a, ha⟩ := hraw.2 (invMonoidHom.comp (e.toMonoidHom.comp f))
    refine ⟨a, MonoidHom.ext fun b => ?_⟩
    apply e.injective
    change A.finiteRootsEquiv v n hn (A.actualLocalHilbert v n hn a b) = e (f b)
    have hb := DFunLike.congr_fun ha b
    change A.actualRawHilbert n hn v a b = (e (f b))⁻¹ at hb
    exact (A.actualLocalHilbert_local_value v n hn a b).trans
      ((congrArg Inv.inv hb).trans (inv_inv _))

private theorem productSingle (A : SArithmeticData F) (n : ℕ+)
    (hn : IsLocalRootOrder n) (x : Vn F A n) (v : {v // v ∈ A.Sf})
    (b : PowerQuotient (v.val.adicCompletion F)ˣ n) :
    A.H_Sn n hn x (Pi.mulSingle (Sum.inr v) b) =
      A.actualLocalHilbert v.val n hn (x (Sum.inr v)) b := by
  rw [H_Sn_apply]
  rw [Finset.prod_eq_single v]
  · simp
  · intro w hw hwv
    rw [Pi.mulSingle_eq_of_ne (by simpa using hwv)]
    exact map_one _
  · simp

theorem H_Sn_perfect (A : SArithmeticData F) (n : ℕ+)
    (hn : (n : ℕ) = 2 ∨ (n : ℕ) = 3) :
    Function.Bijective (A.H_Sn n (hn.elim Or.inl (fun h => Or.inr (Or.inl h)))) := by
  let h : IsLocalRootOrder n := hn.elim Or.inl (fun h => Or.inr (Or.inl h))
  change Function.Bijective (A.H_Sn n h)
  constructor
  · intro x y hxy
    funext v
    cases v with
    | inl w =>
      letI := A.infinite_power_quotient_subsingleton w n h
      exact Subsingleton.elim _ _
    | inr v =>
      apply (localPerfect A v.val n h).1
      apply MonoidHom.ext
      intro b
      have hb := DFunLike.congr_fun hxy (Pi.mulSingle (Sum.inr v) b)
      simpa only [productSingle] using hb
  · intro f
    let M := fun v : A.Place => PowerQuotient (A.Completion v)ˣ n
    have hs (v : {v // v ∈ A.Sf}) :
        ∃ a, A.actualLocalHilbert v.val n h a =
          f.comp (MonoidHom.mulSingle M (Sum.inr v)) :=
      (localPerfect A v.val n h).2 _
    choose a ha using hs
    let x : Vn F A n := fun v => match v with
      | Sum.inl _ => 1
      | Sum.inr v => a v
    refine ⟨x, ?_⟩
    apply MonoidHom.functions_ext
    intro v b
    cases v with
    | inl w =>
      letI := A.infinite_power_quotient_subsingleton w n h
      have hb : b = 1 := Subsingleton.elim _ _
      simp [hb]
    | inr v =>
      rw [productSingle]
      exact DFunLike.congr_fun (ha v) b

def hilbertRootsZModEquiv (A : SArithmeticData F) (n : ℕ+)
    (hn : IsLocalRootOrder n) : ZMod n ≃+ Additive (rootsOfUnity n F) := by
  let ζ : Fˣ := ((A.primitive_root n hn).isUnit n.pos.ne').unit
  have hζ : IsPrimitiveRoot ζ (n : ℕ) :=
    (A.primitive_root n hn).isUnit_unit n.pos.ne'
  letI : NeZero (n : ℕ) := ⟨n.pos.ne'⟩
  exact hζ.zmodEquivZPowers.trans
    (MulEquiv.subgroupCongr hζ.zpowers_eq).toAdditive

end
end DedekindZetaZeroFree.SArithmeticData
