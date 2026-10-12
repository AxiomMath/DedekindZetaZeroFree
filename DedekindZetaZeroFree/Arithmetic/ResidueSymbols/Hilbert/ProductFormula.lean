module

public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.Hilbert.InverseNormalizedHilbertSymbols
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceAdicHilbertProductFormula
public import ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertExponentCompatibility
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.PowerResidueReciprocity

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.SArithmeticData
noncomputable section
set_option autoImplicit false
variable {F : Type} [Field F] [NumberField F]

theorem actualHilbert_roots (A : SArithmeticData F) (n : ℕ+)
    (hn : IsLocalRootOrder n) : (primitiveRoots (n : ℕ) F).Nonempty :=
  ⟨_, (mem_primitiveRoots n.pos).2 (A.primitive_root n hn)⟩

def actualRawHilbert (A : SArithmeticData F) (n : ℕ+)
    (hn : IsLocalRootOrder n) : ClassFieldTheory.GlobalHilbertPairingFamily F n :=
  ClassFieldTheory.finitePlaceAdicHilbertPairingFamily F n (A.actualHilbert_roots n hn)

def actualLocalHilbert (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F))
    (n : ℕ+) (hn : IsLocalRootOrder n) :
    PowerQuotient (v.adicCompletion F)ˣ n →*
      PowerQuotient (v.adicCompletion F)ˣ n →* rootsOfUnity n F :=
  A.finiteSymbolInverseTransport v n hn (A.actualRawHilbert n hn v)

def actualLocalSymbol (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F))
    (n : ℕ+) (hn : IsLocalRootOrder n) (a b : (v.adicCompletion F)ˣ) :
    rootsOfUnity n F :=
  A.actualLocalHilbert v n hn
    (QuotientGroup.mk' (powMonoidHom (α := (v.adicCompletion F)ˣ) n).range a)
    (QuotientGroup.mk' (powMonoidHom (α := (v.adicCompletion F)ˣ) n).range b)

def H_S (A : SArithmeticData F) (x y : A.G) : rootsOfUnity 6 F :=
  ∏ v : {v // v ∈ A.Sf}, A.actualLocalSymbol v.val 6 (Or.inr (Or.inr rfl))
    (x.2 v) (y.2 v)

theorem actualRawHilbert_isLocal (A : SArithmeticData F) (n : ℕ+)
    (hn : IsLocalRootOrder n) (v : HeightOneSpectrum (𝓞 F)) :
    ClassFieldTheory.HilbertPairing.IsLocalHilbertPairing (A.actualRawHilbert n hn v) :=
  ClassFieldTheory.finitePlaceAdicHilbertPairingFamily_isLocallyHilbert F n
    (A.actualHilbert_roots n hn) v

theorem actualLocalHilbert_local_value (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (n : ℕ+) (hn : IsLocalRootOrder n)
    (a b : PowerQuotient (v.adicCompletion F)ˣ n) :
    A.finiteRootsEquiv v n hn (A.actualLocalHilbert v n hn a b) =
      (A.actualRawHilbert n hn v a b)⁻¹ :=
  NormalizedSymbolTransport.map_inverseTransport _ _ _ _

theorem actualLocalHilbert_skew (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (n : ℕ+) (hn : IsLocalRootOrder n)
    (a b : PowerQuotient (v.adicCompletion F)ˣ n) :
    A.actualLocalHilbert v n hn a b = (A.actualLocalHilbert v n hn b a)⁻¹ :=
  NormalizedSymbolTransport.inverseTransport_skew _ _
    (A.actualRawHilbert_isLocal n hn v).2.1 a b

theorem actualLocalHilbert_left_nondegenerate (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (n : ℕ+) (hn : IsLocalRootOrder n)
    (a : PowerQuotient (v.adicCompletion F)ˣ n)
    (ha : ∀ b, A.actualLocalHilbert v n hn a b = 1) : a = 1 :=
  NormalizedSymbolTransport.inverseTransport_left_nondegenerate _ _
    (A.actualRawHilbert_isLocal n hn v).2.2.1.1 a ha

theorem H_S_mul_left (A : SArithmeticData F) (x z y : A.G) :
    A.H_S (x * z) y = A.H_S x y * A.H_S z y := by
  classical
  unfold H_S actualLocalSymbol
  simp only [Prod.snd_mul, Pi.mul_apply, map_mul, MonoidHom.mul_apply,
    Finset.prod_mul_distrib]
  exact Finset.prod_mul_distrib

theorem H_S_mul_right (A : SArithmeticData F) (x y z : A.G) :
    A.H_S x (y * z) = A.H_S x y * A.H_S x z := by
  classical
  unfold H_S actualLocalSymbol
  simp only [Prod.snd_mul, Pi.mul_apply, map_mul, Finset.prod_mul_distrib]
  exact Finset.prod_mul_distrib

theorem H_S_skew (A : SArithmeticData F) (x y : A.G) :
    A.H_S x y = (A.H_S y x)⁻¹ := by
  classical
  calc
    _ = ∏ v : {v // v ∈ A.Sf},
        (A.actualLocalSymbol v.val 6 (Or.inr (Or.inr rfl)) (y.2 v) (x.2 v))⁻¹ := by
      apply Finset.prod_congr rfl
      intro v hv
      exact A.actualLocalHilbert_skew v.val 6 (Or.inr (Or.inr rfl)) _ _
    _ = _ := Finset.prod_inv_distrib _

theorem actualLocalSymbol_diagonal (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (n : ℕ+) (hn : IsLocalRootOrder n) (a b : Fˣ) :
    A.actualLocalSymbol v n hn
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom b) =
    (ClassFieldTheory.GlobalHilbertPairingFamily.finiteFactor F
      (A.actualRawHilbert n hn) (A.actualHilbert_roots n hn) v a b)⁻¹ := by
  change (A.finiteRootsEquiv v n hn).symm (_⁻¹) = _
  rw [map_inv]
  rfl

theorem actualSextic_productFormula (A : SArithmeticData F) (a b : Fˣ) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 F), A.actualLocalSymbol v 6 (Or.inr (Or.inr rfl))
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom b)) = 1 := by
  have h := (ClassFieldTheory.finitePlaceAdicHilbertPairingFamily_productFormula
    F 6 (A.actualHilbert_roots 6 (Or.inr (Or.inr rfl)))).2.2 a b
  have hraw : (∏ᶠ v : HeightOneSpectrum (𝓞 F),
      ClassFieldTheory.GlobalHilbertPairingFamily.finiteFactor F
        (A.actualRawHilbert 6 (Or.inr (Or.inr rfl)))
        (A.actualHilbert_roots 6 (Or.inr (Or.inr rfl))) v a b) = 1 := by
    simpa only [ClassFieldTheory.globalInfinitePlaceHilbertSymbol,
      show ((6 : ℕ+) : ℕ) ≠ 2 by decide, dite_false,
      Finset.prod_const_one, one_mul, actualRawHilbert] using h
  calc
    _ = ∏ᶠ v : HeightOneSpectrum (𝓞 F),
        (ClassFieldTheory.GlobalHilbertPairingFamily.finiteFactor F
          (A.actualRawHilbert 6 (Or.inr (Or.inr rfl)))
          (A.actualHilbert_roots 6 (Or.inr (Or.inr rfl))) v a b)⁻¹ := by
      apply finprod_congr
      intro v
      exact A.actualLocalSymbol_diagonal v 6 (Or.inr (Or.inr rfl)) a b
    _ = 1 := by rw [finprod_inv_distrib, hraw, inv_one]

private theorem raw_exponent (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (m n : ℕ+)
    (hm : IsLocalRootOrder m) (hn : IsLocalRootOrder n)
    (hmn : (m : ℕ) ∣ (n : ℕ)) (a b : (v.adicCompletion F)ˣ) :
    (A.actualRawHilbert m hm v (ClassFieldTheory.powerClass _ m a)
      (ClassFieldTheory.powerClass _ m b)).1 =
    (A.actualRawHilbert n hn v (ClassFieldTheory.powerClass _ n a)
      (ClassFieldTheory.powerClass _ n b)).1 ^ ((n : ℕ) / (m : ℕ)) := by
  let C := (HeightOneSpectrum.adicAbv F v).Completion
  letI : ValuativeRel C :=
    GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinCompletionValuativeRel v
  letI : IsNonarchimedeanLocalField C :=
    GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  letI : CharZero C := charZero_of_injective_algebraMap (algebraMap F C).injective
  let e := (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv
  let eu : Cˣ ≃* (v.adicCompletion F)ˣ := Units.mapEquiv e.toMulEquiv
  have hroots (r : ℕ+) (hr : IsLocalRootOrder r) :
      (primitiveRoots (r : ℕ) C).Nonempty := by
    obtain ⟨ζ, hζ⟩ := A.actualHilbert_roots r hr
    exact ⟨algebraMap F C ζ, (mem_primitiveRoots r.pos).2
      (((mem_primitiveRoots r.pos).1 hζ).map_of_injective (algebraMap F C).injective)⟩
  have ht (r : ℕ+) (hr : IsLocalRootOrder r) (x : rootsOfUnity (r : ℕ) C) :
      (ClassFieldTheory.rootsOfUnityEquivOfRingEquiv e r (hroots r hr) x).1 = eu x.1 := by
    letI : NeZero (r : ℕ) := ⟨r.pos.ne'⟩
    apply Units.ext
    exact (val_rootsOfUnityEquivOfPrimitiveRoots_apply_coe e.injective (hroots r hr) x).symm
  change (ClassFieldTheory.hilbertPairingOfRingEquiv e m (hroots m hm)
      (ClassFieldTheory.localHilbertPairing C m (Nat.cast_ne_zero.mpr m.ne_zero) (hroots m hm))
      (ClassFieldTheory.powerClass _ m a) (ClassFieldTheory.powerClass _ m b)).1 =
    (ClassFieldTheory.hilbertPairingOfRingEquiv e n (hroots n hn)
      (ClassFieldTheory.localHilbertPairing C n (Nat.cast_ne_zero.mpr n.ne_zero) (hroots n hn))
      (ClassFieldTheory.powerClass _ n a) (ClassFieldTheory.powerClass _ n b)).1 ^ _
  rw [ClassFieldTheory.hilbertPairingOfRingEquiv_apply,
    ClassFieldTheory.powerClassGroupEquivOfRingEquiv_symm_powerClass,
    ClassFieldTheory.powerClassGroupEquivOfRingEquiv_symm_powerClass,
    ClassFieldTheory.hilbertPairingOfRingEquiv_apply,
    ClassFieldTheory.powerClassGroupEquivOfRingEquiv_symm_powerClass,
    ClassFieldTheory.powerClassGroupEquivOfRingEquiv_symm_powerClass,
    ht m hm, ht n hn, ClassFieldTheory.localHilbertPairing_powerClass,
    ClassFieldTheory.localHilbertPairing_powerClass]
  simpa [eu, Units.mapEquiv_symm, ClassFieldTheory.localHilbertSymbol,
    KummerTheory.nthRootsSubgroupEquivRootsOfUnity] using congrArg eu
    (LocalClassFieldTheory.Kummer.localHilbertSymbol_exponentCompatibility C m n
      (Nat.cast_ne_zero.mpr m.ne_zero) (Nat.cast_ne_zero.mpr n.ne_zero)
      (hroots m hm) (hroots n hn) hmn (eu.symm a) (eu.symm b))

theorem actualLocalSymbol_two_six (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (a b : (v.adicCompletion F)ˣ) :
    (A.finiteRootsEquiv v 2 (Or.inl rfl)
      (A.actualLocalSymbol v 2 (Or.inl rfl) a b) : (v.adicCompletion F)ˣ) =
    (A.finiteRootsEquiv v 6 (Or.inr (Or.inr rfl))
      (A.actualLocalSymbol v 6 (Or.inr (Or.inr rfl)) a b) : (v.adicCompletion F)ˣ) ^ 3 := by
  exact A.finiteSymbolInverseTransport_exponentCompatibility v 2 6 3
    (Or.inl rfl) (Or.inr (Or.inr rfl))
    (A.actualRawHilbert 2 (Or.inl rfl) v)
    (A.actualRawHilbert 6 (Or.inr (Or.inr rfl)) v) a b (by
      exact A.raw_exponent v 2 6
        (Or.inl rfl) (Or.inr (Or.inr rfl)) (by decide) a b)

theorem actualLocalSymbol_three_six (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (a b : (v.adicCompletion F)ˣ) :
    (A.finiteRootsEquiv v 3 (Or.inr (Or.inl rfl))
      (A.actualLocalSymbol v 3 (Or.inr (Or.inl rfl)) a b) : (v.adicCompletion F)ˣ) =
    (A.finiteRootsEquiv v 6 (Or.inr (Or.inr rfl))
      (A.actualLocalSymbol v 6 (Or.inr (Or.inr rfl)) a b) : (v.adicCompletion F)ˣ) ^ 2 := by
  exact A.finiteSymbolInverseTransport_exponentCompatibility v 3 6 2
    (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
    (A.actualRawHilbert 3 (Or.inr (Or.inl rfl)) v)
    (A.actualRawHilbert 6 (Or.inr (Or.inr rfl)) v) a b (by
      exact A.raw_exponent v 3 6 (Or.inr (Or.inl rfl))
        (Or.inr (Or.inr rfl)) (by decide) a b)

private theorem outside (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ A.Sf) (a b : A.U) :
    A.actualLocalSymbol v 6 (Or.inr (Or.inr rfl))
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a.val)
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom b.val) = 1 := by
  have hdiag := A.actualLocalSymbol_diagonal v 6 (Or.inr (Or.inr rfl)) a.val b.val
  rw [hdiag]
  have hn : v.valuation F (6 : F) = 1 := by
    have h6 : (6 : 𝓞 F) ∉ v.asIdeal := fun h => hv (A.above_six v h)
    convert (v.valuation_eq_one_iff_notMem (K := F) (r := (6 : 𝓞 F))).2 h6 using 1 <;> norm_cast
  have h := GlobalClassFieldTheory.Reciprocity.finitePlaceHilbertSymbol_eq_one_of_valuation_eq_one
    F 6 (by norm_num) (A.actualHilbert_roots 6 (Or.inr (Or.inr rfl))) a.val b.val v
    (a.property v hv) (b.property v hv) hn
  have hf := ClassFieldTheory.finitePlaceAdicHilbertPairingFamily_finiteFactor
    F 6 (by norm_num) (A.actualHilbert_roots 6 (Or.inr (Or.inr rfl))) v a.val b.val
  have hh : ClassFieldTheory.globalFinitePlaceHilbertSymbol F 6 (by norm_num)
      (A.actualHilbert_roots 6 (Or.inr (Or.inr rfl))) v a.val b.val = 1 := by
    change (KummerTheory.nthRootsSubgroupEquivRootsOfUnity F 6
    (GlobalClassFieldTheory.Reciprocity.finitePlaceHilbertSymbol F 6 (by norm_num)
      (A.actualHilbert_roots 6 (Or.inr (Or.inr rfl))) v a.val b.val)) = 1
    exact (congrArg (KummerTheory.nthRootsSubgroupEquivRootsOfUnity F 6) h).trans
      (map_one _)
  exact (congrArg Inv.inv (hf.trans hh)).trans (inv_one)

theorem H_S_sunit_isotropy (A : SArithmeticData F) (a b : A.U) :
    A.H_S (A.diagonal a.val) (A.diagonal b.val) = 1 := by
  let f : HeightOneSpectrum (𝓞 F) → rootsOfUnity 6 F := fun v =>
    A.actualLocalSymbol v 6 (Or.inr (Or.inr rfl))
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a.val)
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom b.val)
  have hsupport : Function.mulSupport f ⊆ A.Sf := by
    intro v hv
    by_contra hnot
    exact hv (outside A v hnot a b)
  have hprod := finprod_eq_prod_of_mulSupport_subset f hsupport
  have hformula := A.actualSextic_productFormula a.val b.val
  calc
    A.H_S (A.diagonal a.val) (A.diagonal b.val) = ∏ v ∈ A.Sf, f v := by
      exact Finset.prod_coe_sort A.Sf f
    _ = ∏ᶠ v, f v := hprod.symm
    _ = 1 := hformula

end
end DedekindZetaZeroFree.SArithmeticData
