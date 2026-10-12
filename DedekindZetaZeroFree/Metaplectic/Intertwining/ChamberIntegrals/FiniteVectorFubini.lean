module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Residues.RationalVectorCofactor

@[expose] public section

noncomputable section
open scoped Classical BigOperators NumberField
open MeasureTheory ValuativeRel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.ActualCofactor

private theorem finite_coordinate_multilinear_integral
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {J : ι → Type} [∀ i, Fintype (J i)] [∀ i, DecidableEq (J i)]
    {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    {X : ι → Type} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
    (e : ∀ i, V i ≃ₗ[ℂ] (J i → ℂ)) (L : MultilinearMap ℂ V ℂ)
    (f : ∀ i, X i → V i) (v : ∀ i, V i)
    (hf : ∀ i j, Integrable (fun x => e i (f i x) j) (μ i))
    (hv : ∀ i j, e i (v i) j = ∫ x, e i (f i x) j ∂μ i) :
    Integrable (fun x : ∀ i, X i => L (fun i => f i (x i))) (Measure.pi μ) ∧
      (∫ x : ∀ i, X i, L (fun i => f i (x i)) ∂(Measure.pi μ)) = L v := by
  let w (i : ι) (j : J i) := (e i).symm (Pi.single j 1)
  have he (y : ∀ i, V i) : L y =
      ∑ r : ∀ i, J i, (∏ i, e i (y i) (r i)) * L (fun i => w i (r i)) := by
    have hex (i : ι) : y i = ∑ j, e i (y i) j • w i j := by
      apply (e i).injective
      simp only [map_sum, map_smul, w, LinearEquiv.apply_symm_apply]
      rw [← Finset.univ_sum_single (e i (y i))]
      apply Finset.sum_congr rfl
      intro j _
      funext k
      simp [Pi.single_apply]
    calc
      L y = L (fun i => ∑ j, e i (y i) j • w i j) := congrArg L (funext hex)
      _ = ∑ r : ∀ i, J i, (∏ i, e i (y i) (r i)) * L (fun i => w i (r i)) := by
        rw [L.map_sum_finset]
        apply Finset.sum_congr rfl
        intro r _
        simpa only [smul_eq_mul] using
          L.map_smul_univ (fun i => e i (y i) (r i)) (fun i => w i (r i))
  have hi (r : ∀ i, J i) : Integrable
      (fun x : ∀ i, X i => (∏ i, e i (f i (x i)) (r i)) * L (fun i => w i (r i)))
      (Measure.pi μ) := (Integrable.fintype_prod_dep (fun i => hf i (r i))).mul_const _
  have hef : (fun x : ∀ i, X i => L (fun i => f i (x i))) =
      (fun x => ∑ r : ∀ i, J i, (∏ i, e i (f i (x i)) (r i)) * L (fun i => w i (r i))) :=
    funext (fun x => he (fun i => f i (x i)))
  constructor
  · rw [hef]
    exact integrable_finsetSum _ (fun r _ => hi r)
  · rw [hef, he v]
    rw [integral_finsetSum _ (fun r _ => hi r)]
    apply Finset.sum_congr rfl
    intro r _
    rw [integral_mul_const]
    have hp := integral_fintype_prod_eq_prod (fun i (x : X i) => e i (f i x) (r i)) (μ := μ)
    rw [hp]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    exact (hv i (r i)).symm

open KPLocalPrincipalSeries KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPRankOneShellRepair
open KPRankOneShellContinuation
open _root_.DedekindZetaZeroFree.KPLocalStoneVonNeumann renaming inducedCosetEquiv → inducedCosetEquiv

 theorem compact_forward_eq_integral
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
    (φ : compactPicture S.borel P S.iwasawa .plus)
    (k : S.iwasawa.compact.toOpenSubgroup) (t : actualTorus F ζ hζ q)
    (s : ℂ) (hs : convergenceHalfPlane .plus s) :
    ((actualCanonicalContinued F q ζ hζ S P μ hμ .plus s φ).val k).val t =
      ∫ x : LocalField F q,
        ((compactTrivialization S.borel P S.iwasawa .plus s φ).val
          (S.borel.liftedW⁻¹ * S.borel.upperRoot (Multiplicative.ofAdd x) * k)).val t ∂μ := by
  have h := actualCanonicalContinued_chamber F q ζ hζ S P μ hμ .plus s hs φ k t
  have hr (v : compactPicture S.borel P S.iwasawa .minus) :
      ((compactTrivialization S.borel P S.iwasawa .minus (-s) v).val k).val t = (v.val k).val t := by
    have he := (compactTrivialization S.borel P S.iwasawa .minus (-s)).symm_apply_apply v
    exact congrArg (fun v : compactPicture S.borel P S.iwasawa .minus => (v.val k).val t) he
  simp only [transportToSections, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h
  change ((compactTrivialization S.borel P S.iwasawa .minus (-s)
    (actualCanonicalContinued F q ζ hζ S P μ hμ .plus s φ)).val k).val t = _ at h
  rw [hr] at h
  exact h

 def actualFiberCoordinates
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg) :
    InducedModule P ≃ₗ[ℂ] ((actualTorus F ζ hζ q ⧸ P.L.comap S.heisenberg.π) → ℂ) :=
  inducedCosetEquiv (P.L.comap S.heisenberg.π) P.ωL.toMonoidHom

 theorem actual_fiber_coordinates_apply
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
    (v : InducedModule P) (j : actualTorus F ζ hζ q ⧸ P.L.comap S.heisenberg.π) :
    actualFiberCoordinates F ζ hζ q S P v j = v.val
      (Function.surjInv (QuotientGroup.mk'_surjective (P.L.comap S.heisenberg.π)) j) := rfl

theorem rational_finite_chamber_integral
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (P₀ : KPGlobalTorusFiniteStages.CompatibleModelData F ζ hζ)
    (C₀ : KPGlobalTorusFiniteStages.LocalFiberData F ζ hζ P₀)
    (E : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (hE : C₀.exceptional ⊆ E)
    (φ : ∀ q : E, compactPicture (C₀.canonical q.val).borel (C₀.polarization q.val)
      (C₀.canonical q.val).iwasawa .plus)
    (t : KPGlobalTorusFunctionData.E F ζ hζ) (s : ℂ) (hs : convergenceHalfPlane .plus s) :
    let μ : ∀ q : E, Measure (LocalField F q.val) := fun q =>
      Measure.addHaarMeasure (finiteCompletionIntegersPositiveCompacts F q.val)
    Integrable (fun x : ∀ q : E, LocalField F q.val => rationalStageEval F ζ hζ P₀ C₀ E hE t
      (fun q => ((compactTrivialization (C₀.canonical q.val).borel (C₀.polarization q.val)
        (C₀.canonical q.val).iwasawa .plus s (φ q)).val
        ((C₀.canonical q.val).borel.liftedW⁻¹ * (C₀.canonical q.val).borel.upperRoot
          (Multiplicative.ofAdd (x q)) * 1))))
      (Measure.pi (fun q : E => localNormalizedHaar F q.val)) ∧
    (∫ x : ∀ q : E, LocalField F q.val, rationalStageEval F ζ hζ P₀ C₀ E hE t
      (fun q => ((compactTrivialization (C₀.canonical q.val).borel (C₀.polarization q.val)
        (C₀.canonical q.val).iwasawa .plus s (φ q)).val
        ((C₀.canonical q.val).borel.liftedW⁻¹ * (C₀.canonical q.val).borel.upperRoot
          (Multiplicative.ofAdd (x q)) * 1)))
      ∂(Measure.pi (fun q : E => localNormalizedHaar F q.val))) =
        rationalStageEval F ζ hζ P₀ C₀ E hE t
          (fun q => (localHalfDifferentFactor F q.val : ℂ) •
            (actualCanonicalContinued F q.val ζ hζ (C₀.canonical q.val) (C₀.polarization q.val)
              (μ q) (unit_mass F q.val) .plus s (φ q)).val 1) := by
  dsimp only
  let μ : ∀ q : E, Measure (LocalField F q.val) := fun q =>
    Measure.addHaarMeasure (finiteCompletionIntegersPositiveCompacts F q.val)
  let : ∀ q : E, (μ q).IsAddHaarMeasure := fun _ => inferInstance
  let : ∀ q : E, (localNormalizedHaar F q.val).IsAddHaarMeasure :=
    fun q => localNormalizedHaar_isAddHaarMeasure F q.val
  let J (q : E) := actualTorus F ζ hζ q.val ⧸ (C₀.polarization q.val).L.comap (C₀.canonical q.val).heisenberg.π
  let : ∀ q : E, Fintype (J q) := fun q => Fintype.ofFinite _
  let : ∀ q : E, DecidableEq (J q) := fun _ => Classical.decEq _
  let f (q : E) (x : LocalField F q.val) : KPGlobalTorusFiniteStages.LocalFiber F ζ hζ P₀ C₀ q.val :=
    ((compactTrivialization (C₀.canonical q.val).borel (C₀.polarization q.val)
      (C₀.canonical q.val).iwasawa .plus s (φ q)).val
      ((C₀.canonical q.val).borel.liftedW⁻¹ * (C₀.canonical q.val).borel.upperRoot
        (Multiplicative.ofAdd x) * 1))
  let v (q : E) : KPGlobalTorusFiniteStages.LocalFiber F ζ hζ P₀ C₀ q.val :=
    (localHalfDifferentFactor F q.val : ℂ) •
      (actualCanonicalContinued F q.val ζ hζ (C₀.canonical q.val) (C₀.polarization q.val)
        (μ q) (unit_mass F q.val) .plus s (φ q)).val 1
  refine finite_coordinate_multilinear_integral (ι := E) (J := J)
    (V := fun q => KPGlobalTorusFiniteStages.LocalFiber F ζ hζ P₀ C₀ q.val)
    (X := fun q => LocalField F q.val)
    (fun q : E => localNormalizedHaar F q.val)
    (fun q => actualFiberCoordinates F ζ hζ q.val (C₀.canonical q.val) (C₀.polarization q.val))
    (rationalStageEval F ζ hζ P₀ C₀ E hE t) f v ?_ ?_
  · intro q j
    rw [show (fun x => actualFiberCoordinates F ζ hζ q.val (C₀.canonical q.val) (C₀.polarization q.val)
      (((compactTrivialization (C₀.canonical q.val).borel (C₀.polarization q.val)
        (C₀.canonical q.val).iwasawa .plus s (φ q)).val
        ((C₀.canonical q.val).borel.liftedW⁻¹ * (C₀.canonical q.val).borel.upperRoot
          (Multiplicative.ofAdd x) * 1))) j) = _ from rfl]
    have hi := actualCanonicalContinued_integrable F q.val ζ hζ (C₀.canonical q.val)
      (C₀.polarization q.val) (μ q) (unit_mass F q.val) .plus s hs
      (compactTrivialization (C₀.canonical q.val).borel (C₀.polarization q.val)
        (C₀.canonical q.val).iwasawa .plus s (φ q)) 1
      (Function.surjInv (QuotientGroup.mk'_surjective ((C₀.polarization q.val).L.comap (C₀.canonical q.val).heisenberg.π)) j)
    exact hi.smul_measure ENNReal.ofReal_ne_top
  · intro q j
    rw [actual_fiber_coordinates_apply]
    change (localHalfDifferentFactor F q.val : ℂ) * _ = _
    rw [compact_forward_eq_integral F ζ hζ q.val (C₀.canonical q.val) (C₀.polarization q.val)
      (μ q) (unit_mass F q.val) (φ q) 1 _ s hs]
    change _ = ∫ x, _ ∂(ENNReal.ofReal (localHalfDifferentFactor F q.val) • μ q)
    rw [integral_smul_measure, ENNReal.toReal_ofReal (localHalfDifferentFactor_pos F q.val).le]
    rfl

end DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.ActualCofactor

end
