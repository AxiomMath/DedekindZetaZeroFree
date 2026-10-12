module

public import DedekindZetaZeroFree.Arithmetic.Kummer.LocalNormCharacter

@[expose] public section

namespace DedekindZetaZeroFree.RMKummerLocalHilbertComparison

noncomputable section
open scoped NumberField Classical
open IsDedekindDomain Topology

theorem localTwo_ne_zero (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : (2 : v.adicCompletion F) ≠ 0 := by
  intro h
  apply rmKummerTwo_ne_zero F
  apply (algebraMap F (v.adicCompletion F)).injective
  simpa only [map_ofNat, map_zero] using h

def localPrimitiveTwo (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (v : HeightOneSpectrum (𝓞 F)) :
    (primitiveRoots 2 (v.adicCompletion F)).Nonempty := by
  obtain ⟨ζ, hζ⟩ := rmKummerPrimitiveTwo F h12
  refine ⟨algebraMap F (v.adicCompletion F) ζ, ?_⟩
  exact (mem_primitiveRoots (by decide)).2
    (((mem_primitiveRoots (by decide)).1 hζ).map_of_injective
      (algebraMap F (v.adicCompletion F)).injective)

private theorem quadratic_eq (a b : ℂˣ) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (h : a = 1 ↔ b = 1) : a = b := by
  apply Units.ext
  have ha' : (a : ℂ) ^ 2 = 1 := by exact congrArg Units.val ha
  have hb' : (b : ℂ) ^ 2 = 1 := by exact congrArg Units.val hb
  rcases sq_eq_one_iff.mp ha' with ha' | ha'
  · have ha1 : a = 1 := Units.ext ha'
    simpa [ha1, h.mp ha1]
  · rcases sq_eq_one_iff.mp hb' with hb' | hb'
    · have hb1 : b = 1 := Units.ext hb'
      simpa [h.mpr hb1, hb1]
    · exact ha'.trans hb'.symm

private theorem continuous_of_open_ker {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H]
    (f : G →* H) (h : IsOpen (f.ker : Set G)) : Continuous f := by
  apply IsLocallyConstant.continuous
  apply IsLocallyConstant.iff_isOpen_fiber_apply.mpr
  intro x
  have heq : f ⁻¹' {f x} = (fun y => y * x⁻¹) ⁻¹' (f.ker : Set G) := by
    ext y
    change f y = f x ↔ f (y * x⁻¹) = 1
    rw [map_mul, map_inv, mul_inv_eq_one]
  rw [heq]
  exact h.preimage (continuous_id.mul continuous_const)

private theorem dense_units (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    DenseRange (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom) := by
  apply dense_iff_inter_open.mpr
  intro U hU hUne
  have hval : IsOpenEmbedding (Units.val : (v.adicCompletion F)ˣ → v.adicCompletion F) :=
    IsOpenUnits.isOpenEmbedding_unitsVal
  obtain ⟨a, ha⟩ := (v.denseRange_algebraMap F).exists_mem_open
    (hval.isOpenMap U hU) (hUne.image _)
  obtain ⟨u, hu, hau⟩ := ha
  have hane : a ≠ 0 := by
    intro h
    have : (u : v.adicCompletion F) = 0 := by simpa [h] using hau
    exact u.ne_zero this
  refine ⟨u, hu, Units.mk0 a hane, ?_⟩
  apply Units.ext
  exact hau.symm
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
open GlobalClassFieldTheory.Reciprocity KummerTheory
private theorem global_trivial (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x a : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) :
    RMKummerLocalNormCharacter.lambda F h12 x v
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a) = 1 ↔
    finitePlaceHilbertSymbol F 2 (rmKummerTwo_ne_zero F) (rmKummerPrimitiveTwo F h12)
      v a x = 1 := by
  rw [← finitePlaceKummerRootCharacter_localGlobal F 2 (rmKummerTwo_ne_zero F)
    (rmKummerPrimitiveTwo F h12) v a x]
  unfold RMKummerLocalNormCharacter.lambda
  rw [MonoidHom.comp_apply, arithmeticChosenFinitePlaceArtinMonoidHom_apply, map_inv,
    inv_eq_one]
  let L := RMKummerConductor.E F h12 x
  let c := chosenSimpleKummerRootCharacter F 2 (rmKummerTwo_ne_zero F)
    (rmKummerPrimitiveTwo F h12) x
      (chosenFinitePlaceArtinMonoidHom (K := F) (L := L) v
        (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a))
  let e := nthRootsSubgroupEquivRootsOfUnity L 2
  let d := (nthRootsSubgroupEquivOfPrimitiveRoots F L 2 (rmKummerPrimitiveTwo F h12)).symm
  change rmKummerQuadraticRootsComplexMap F h12 L (e c) = 1 ↔ d c = 1
  rw [← map_one (rmKummerQuadraticRootsComplexMap F h12 L),
    (rmKummerQuadraticRootsComplexMap_injective F h12 L).eq_iff]
  erw [← map_one e, e.injective.eq_iff, ← map_one d, d.injective.eq_iff]
  rfl
open ClassFieldTheory
private theorem global_local_trivial (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x a : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) :
    letI : ValuativeRel (v.adicCompletion F) := finitePlaceCompletionValuativeRel F v
    letI : IsNonarchimedeanLocalField (v.adicCompletion F) :=
      finitePlaceCompletionIsNonarchimedeanLocalField F v
    finitePlaceHilbertSymbol F 2 (rmKummerTwo_ne_zero F) (rmKummerPrimitiveTwo F h12)
      v a x = 1 ↔
    localHilbertSymbol (v.adicCompletion F) 2 (localTwo_ne_zero F v)
      (localPrimitiveTwo F h12 v)
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom x) = 1 := by
  letI : ValuativeRel (v.adicCompletion F) := finitePlaceCompletionValuativeRel F v
  letI : IsNonarchimedeanLocalField (v.adicCompletion F) :=
    finitePlaceCompletionIsNonarchimedeanLocalField F v
  let B := finitePlaceAdicHilbertPairingFamily F 2 (rmKummerPrimitiveTwo F h12)
  let e := nthRootsSubgroupEquivRootsOfUnity F 2
  have hh := finitePlaceAdicHilbertPairingFamily_finiteFactor F 2
    (rmKummerTwo_ne_zero F) (rmKummerPrimitiveTwo F h12) v a x
  change GlobalHilbertPairingFamily.finiteFactor F B (rmKummerPrimitiveTwo F h12) v a x =
    e (finitePlaceHilbertSymbol F 2 (rmKummerTwo_ne_zero F) (rmKummerPrimitiveTwo F h12) v a x) at hh
  have he : finitePlaceHilbertSymbol F 2 (rmKummerTwo_ne_zero F) (rmKummerPrimitiveTwo F h12) v a x = 1 ↔
      GlobalHilbertPairingFamily.finiteFactor F B (rmKummerPrimitiveTwo F h12) v a x = 1 := by
    erw [hh, ← map_one e]
    exact e.injective.eq_iff.symm
  rw [he]
  let d := rootsOfUnityEquivOfPrimitiveRoots (algebraMap F (v.adicCompletion F)).injective
    (rmKummerPrimitiveTwo F h12)
  change d.symm (B v (powerClass _ 2 _) (powerClass _ 2 _)) = 1 ↔ _
  erw [← map_one d.symm, d.symm.injective.eq_iff]
  exact ((finitePlaceAdicHilbertPairingFamily_isLocallyHilbert F 2
    (rmKummerPrimitiveTwo F h12) v).2.2.2 _ _).trans
      (localHilbertSymbol_eq_one_iff_isKummerNorm _ 2 _ _ _ _).symm
private theorem hilbert_complex_continuous (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) :
    letI : ValuativeRel (v.adicCompletion F) := finitePlaceCompletionValuativeRel F v
    letI : IsNonarchimedeanLocalField (v.adicCompletion F) :=
      finitePlaceCompletionIsNonarchimedeanLocalField F v
    Continuous (fun t => rmKummerQuadraticRootsComplexMap F h12 (v.adicCompletion F)
      (localHilbertSymbol (v.adicCompletion F) 2 (localTwo_ne_zero F v)
        (localPrimitiveTwo F h12 v) t
        (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom x))) := by
  letI : ValuativeRel (v.adicCompletion F) := finitePlaceCompletionValuativeRel F v
  letI : IsNonarchimedeanLocalField (v.adicCompletion F) :=
    finitePlaceCompletionIsNonarchimedeanLocalField F v
  let K := v.adicCompletion F
  let b := Units.map (algebraMap F K).toMonoidHom x
  let H := LocalClassFieldTheory.Kummer.localHilbertSymbolHom K 2
    (localTwo_ne_zero F v) (localPrimitiveTwo F h12 v) b
  let e := nthRootsSubgroupEquivRootsOfUnity K 2
  let f := (rmKummerQuadraticRootsComplexMap F h12 K).comp (e.toMonoidHom.comp H)
  change Continuous f
  apply continuous_of_open_ker
  have he : f.ker = H.ker := by
    erw [MonoidHom.ker_comp_of_injective _ _
      (rmKummerQuadraticRootsComplexMap_injective F h12 K),
      MonoidHom.ker_comp_of_injective _ _ e.injective]
  rw [he]
  erw [LocalClassFieldTheory.Kummer.localHilbertSymbolHom_ker K 2
    (localTwo_ne_zero F v) (localPrimitiveTwo F h12 v) b]
  let L := chosenSimpleKummerExtension K 2 (localTwo_ne_zero F v) b
  letI : FiniteDimensional K L := chosenSimpleKummerExtension_finiteDimensional K 2 _ b
  letI : IsAbelianGalois K L := chosenSimpleKummerExtension_isAbelianGalois K 2 _
    (localPrimitiveTwo F h12 v) b
  exact LocalClassFieldTheory.localNormSubgroup_isOpen K L

theorem lambda_eq_inverse_localHilbertSymbol
    (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    letI : ValuativeRel (v.adicCompletion F) :=
      ClassFieldTheory.finitePlaceCompletionValuativeRel F v
    letI : IsNonarchimedeanLocalField (v.adicCompletion F) :=
      ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F v
    RMKummerLocalNormCharacter.lambda F h12 x v t =
      (rmKummerQuadraticRootsComplexMap F h12 (v.adicCompletion F)
        (ClassFieldTheory.localHilbertSymbol (v.adicCompletion F) (2 : ℕ+)
          (localTwo_ne_zero F v) (localPrimitiveTwo F h12 v) t
          (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom x)))⁻¹ := by
  letI : ValuativeRel (v.adicCompletion F) := finitePlaceCompletionValuativeRel F v
  letI : IsNonarchimedeanLocalField (v.adicCompletion F) :=
    finitePlaceCompletionIsNonarchimedeanLocalField F v
  let f := RMKummerLocalNormCharacter.lambda F h12 x v
  let g := fun t => rmKummerQuadraticRootsComplexMap F h12 (v.adicCompletion F)
    (localHilbertSymbol (v.adicCompletion F) 2 (localTwo_ne_zero F v)
      (localPrimitiveTwo F h12 v) t
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom x))
  have hglobal (a : Fˣ) : f (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a) =
      (g (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a))⁻¹ := by
    let z := localHilbertSymbol (v.adicCompletion F) 2 (localTwo_ne_zero F v)
      (localPrimitiveTwo F h12 v)
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom x)
    apply quadratic_eq
    · exact RMKummerLocalNormCharacter.lambda_pow_two F h12 x v _
    · rw [inv_pow]
      exact congrArg Inv.inv (rmKummerQuadraticRootsComplexMap_pow_two F h12 _ z)
    · rw [inv_eq_one]
      have he : rmKummerQuadraticRootsComplexMap F h12 _ z = 1 ↔ z = 1 := by
        erw [← map_one (rmKummerQuadraticRootsComplexMap F h12 (v.adicCompletion F)),
          (rmKummerQuadraticRootsComplexMap_injective F h12 (v.adicCompletion F)).eq_iff]
        rfl
      exact (global_trivial F h12 x a v).trans ((global_local_trivial F h12 x a v).trans he.symm)
  have heq : (f : (v.adicCompletion F)ˣ → ℂˣ) = fun t => (g t)⁻¹ :=
    (dense_units F v).equalizer
      (RMKummerLocalNormCharacter.lambda_continuous F h12 x v)
      (hilbert_complex_continuous F h12 x v).inv (funext hglobal)
  exact congrFun heq t

end
end DedekindZetaZeroFree.RMKummerLocalHilbertComparison
