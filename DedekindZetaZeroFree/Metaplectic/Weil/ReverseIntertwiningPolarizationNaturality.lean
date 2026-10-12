module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ReverseOperatorEvaluation

@[expose] public section

section

noncomputable section
namespace DedekindZetaZeroFree.ActualReverseMinorSvN
open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneShellRepair
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

private theorem finite_evaluation_coordinates
    {H D : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CommGroup D] [Fintype D] (T : LocalHeisenbergData H D)
    (P : Polarization T) (l : InducedModule P →ₗ[ℂ] ℂ) :
    ∃ (r : D → H) (c : D → ℂ), ∀ v : InducedModule P,
      l v = ∑ d : D, c d * v.val (r d) := by
  classical
  let r : D → H := Function.surjInv T.quotient_surjective
  have hr : ∀ d, T.π (r d) = d := Function.surjInv_eq T.quotient_surjective
  let ev : InducedModule P →ₗ[ℂ] (D → ℂ) :=
    { toFun := fun v d => v.val (r d)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hev : Function.Injective ev := by
    intro v w he
    apply Subtype.ext
    funext x
    let y := r (T.π x)
    have ha : x * y⁻¹ ∈ P.L.comap T.π := by
      change T.π (x * y⁻¹) ∈ P.L
      rw [map_mul, map_inv, hr]
      simp
    let a : P.L.comap T.π := ⟨x * y⁻¹, ha⟩
    have hxy : (a : H) * y = x := by dsimp [a]; simp
    rw [← hxy, v.property a y, w.property a y]
    congr 1
    exact congrFun he (T.π x)
  obtain ⟨b, hb⟩ := ev.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hev)
  let L := l.comp b
  refine ⟨r, fun d => L (Pi.single d 1), ?_⟩
  intro v
  have hv : ev v = ∑ d : D, (v.val (r d)) • Pi.single d (1 : ℂ) := by
    ext d
    simp [ev, Pi.single_apply]
  calc
    l v = L (ev v) := by
      change l v = l ((b.comp ev) v)
      rw [hb]; rfl
    _ = ∑ d : D, L ((v.val (r d)) • Pi.single d (1 : ℂ)) := by rw [hv, map_sum]
    _ = _ := by simp [map_smul, smul_eq_mul, mul_comm]

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q)
  (P Q : Polarization S.heisenberg) (e : (tau P).Equiv (tau Q))

theorem inducing_action_naturality (ε : Sign) (s : ℂ)
    (b : S.borel.B) (v : InducedModule P) :
    e (inducingAction S.borel P ε s b v) =
      inducingAction S.borel Q ε s b (e v) := by
  change e (inducingScalar S.borel s b • borelAction S.borel P ε b v) = _
  rw [map_smul]
  congr 1
  cases ε <;> exact Representation.IntertwiningMap.isIntertwining (tau P) (tau Q) e.toIntertwiningMap _ v

 def compact_svn_map (ε : Sign) :
    compactPicture S.borel P S.iwasawa ε →ₗ[ℂ]
      compactPicture S.borel Q S.iwasawa ε where
  toFun φ := ⟨fun k => e (φ.val k), by
    constructor
    · intro b k k' hk
      change e (φ.val k') = _
      rw [φ.property.1 b k k' hk]
      exact inducing_action_naturality F ζ hζ q S P Q e ε 0 b (φ.val k)
    · obtain ⟨U, hU⟩ := φ.property.2
      refine ⟨U, ?_⟩
      intro u hu
      funext k
      exact congrArg e (congrFun (hU u hu) k)⟩
  map_add' := by intros; ext k; simp
  map_smul' := by intros; ext k; simp

private theorem compact_extension_naturality (ε : Sign) (s : ℂ)
    (φ : compactPicture S.borel P S.iwasawa ε) (g : ActualCover F ζ hζ q) :
    e ((compactTrivialization S.borel P S.iwasawa ε s φ).val g) =
      (compactTrivialization S.borel Q S.iwasawa ε s
        (compact_svn_map F ζ hζ q S P Q e ε φ)).val g :=
  inducing_action_naturality F ζ hζ q S P Q e ε s
    (S.iwasawa.borelPart g) (φ.val (S.iwasawa.compactPart g))

open _root_.DedekindZetaZeroFree.KPRankOneTranslatedMeromorphy renaming actual_coordinate_regular → actual_coordinate_regular

variable (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)

private theorem canonical_compact_regular (ε : Sign)
    (φ : compactPicture S.borel P S.iwasawa (sourceSign ε))
    (k : S.iwasawa.compact.toOpenSubgroup) (h : actualTorus F ζ hζ q) :
    Meromorphic (fun s : ℂ => ((actualCanonicalContinued F q ζ hζ S P μ hμ ε s φ).val k).val h) ∧
    (∀ s, denominator (LocalField F q) ε s ≠ 0 →
      DifferentiableAt ℂ (fun t : ℂ =>
        ((actualCanonicalContinued F q ζ hζ S P μ hμ ε t φ).val k).val h) s) :=
  actual_coordinate_regular F ζ hζ q S P μ hμ (actualFamilyUniformizer F q)
    (actualFamilyUniformizer_spec F q) ε φ k h

private theorem canonical_compact_chamber (ε : Sign) (s : ℂ)
    (hs : convergenceHalfPlane ε s)
    (φ : compactPicture S.borel P S.iwasawa (sourceSign ε))
    (k : S.iwasawa.compact.toOpenSubgroup) (h : actualTorus F ζ hζ q) :
    ((actualCanonicalContinued F q ζ hζ S P μ hμ ε s φ).val k).val h =
      standardIntegralCoordinate (LocalField F q) S.borel P S.iwasawa μ ε s φ k h := by
  have he := actualCanonicalContinued_chamber F q ζ hζ S P μ hμ ε s hs φ k h
  change ((compactTrivialization S.borel P S.iwasawa (targetSign ε) (targetParameter ε s)
    (actualCanonicalContinued F q ζ hζ S P μ hμ ε s
      ((compactTrivialization S.borel P S.iwasawa (sourceSign ε) (sourceParameter ε s)).symm
        (compactTrivialization S.borel P S.iwasawa (sourceSign ε) (sourceParameter ε s) φ)))).val k).val h = _ at he
  rw [LinearEquiv.symm_apply_apply] at he
  change (inducingAction S.borel P (targetSign ε) (targetParameter ε s)
    (S.iwasawa.borelPart k)
      ((actualCanonicalContinued F q ζ hζ S P μ hμ ε s φ).val (S.iwasawa.compactPart k))).val h = _ at he
  simpa only [S.iwasawa.borelPart_compact, S.iwasawa.compactPart_compact,
    map_one, Module.End.one_apply] using he

private theorem actual_compact_svn_naturality (ε : Sign) (s₀ : ℂ)
    (hs₀ : denominator (LocalField F q) ε s₀ ≠ 0)
    (φ : compactPicture S.borel P S.iwasawa (sourceSign ε))
    (k : S.iwasawa.compact.toOpenSubgroup) :
    e ((actualCanonicalContinued F q ζ hζ S P μ hμ ε s₀ φ).val k) =
      (actualCanonicalContinued F q ζ hζ S Q μ hμ ε s₀
        (compact_svn_map F ζ hζ q S P Q e (sourceSign ε) φ)).val k := by
  classical
  let : Fintype S.D := Fintype.ofFinite S.D
  apply Subtype.ext
  funext h
  let l : InducedModule P →ₗ[ℂ] ℂ :=
    { toFun := fun v => (e v).val h
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  obtain ⟨r, c, hc⟩ := finite_evaluation_coordinates S.heisenberg P l
  let φQ := compact_svn_map F ζ hζ q S P Q e (sourceSign ε) φ
  let f := fun s : ℂ => ∑ d : S.D, c d *
    ((actualCanonicalContinued F q ζ hζ S P μ hμ ε s φ).val k).val (r d)
  let g := fun s : ℂ =>
    ((actualCanonicalContinued F q ζ hζ S Q μ hμ ε s φQ).val k).val h
  have hf : Meromorphic f := by
    intro s
    apply MeromorphicAt.fun_sum
    intro d hd
    exact (MeromorphicAt.const _ _).mul
      ((canonical_compact_regular F ζ hζ q S P μ hμ ε φ k (r d)).1 s)
  have hg : Meromorphic g := (canonical_compact_regular F ζ hζ q S Q μ hμ ε φQ k h).1
  have hfc : ContinuousAt f s₀ := by
    apply DifferentiableAt.continuousAt (𝕜 := ℂ)
    apply DifferentiableAt.fun_sum
    intro d hd
    exact (differentiableAt_const (𝕜 := ℂ) (c d)).mul
      ((canonical_compact_regular F ζ hζ q S P μ hμ ε φ k (r d)).2 s₀ hs₀)
  have hgc : ContinuousAt g s₀ :=
    ((canonical_compact_regular F ζ hζ q S Q μ hμ ε φQ k h).2 s₀ hs₀).continuousAt
  have he : ∀ s, convergenceHalfPlane ε s → f s = g s := by
    intro s hs
    dsimp only [f, g]
    simp_rw [canonical_compact_chamber F ζ hζ q S P μ hμ ε s hs φ k]
    rw [canonical_compact_chamber F ζ hζ q S Q μ hμ ε s hs φQ k h]
    let v := fun x : LocalField F q =>
      (compactTrivialization S.borel P S.iwasawa (sourceSign ε) (sourceParameter ε s) φ).val
        (kernelW (LocalField F q) S.borel ε *
          S.borel.upperRoot (Multiplicative.ofAdd x) * (k : ActualCover F ζ hζ q))
    have hi (d : S.D) : Integrable (fun x => (v x).val (r d)) μ :=
      actualCanonicalContinued_integrable F q ζ hζ S P μ hμ ε s hs
        (compactTrivialization S.borel P S.iwasawa (sourceSign ε) (sourceParameter ε s) φ) k (r d)
    have hv (x : LocalField F q) :
        ((compactTrivialization S.borel Q S.iwasawa (sourceSign ε) (sourceParameter ε s) φQ).val
          (kernelW (LocalField F q) S.borel ε *
            S.borel.upperRoot (Multiplicative.ofAdd x) * (k : ActualCover F ζ hζ q))).val h =
        ∑ d : S.D, c d * (v x).val (r d) := by
      rw [← compact_extension_naturality F ζ hζ q S P Q e]
      exact hc (v x)
    unfold standardIntegralCoordinate
    simp_rw [hv]
    rw [integral_finsetSum _ (fun d _ => (hi d).const_mul (c d))]
    simp_rw [integral_const_mul]
    rfl
  have H := KPRankOneChamberUniqueness.chamber_identity_value ε hf hg he s₀ hfc hgc
  change l ((actualCanonicalContinued F q ζ hζ S P μ hμ ε s₀ φ).val k) = g s₀
  rw [hc]
  exact H

theorem actual_reverse_svn_naturality
    (fP : sectionSpace S.borel P .minus 0)
    (fQ : sectionSpace S.borel Q .minus 0)
    (hf : ∀ g, e (fP.val g) = fQ.val g) :
    ∀ g, e ((actualCanonicalReverseMap F ζ hζ q S P μ hμ fP).val g) =
      (actualCanonicalReverseMap F ζ hζ q S Q μ hμ fQ).val g := by
  let φ := (compactTrivialization S.borel P S.iwasawa .minus 0).symm fP
  have hφ : compact_svn_map F ζ hζ q S P Q e .minus φ =
      (compactTrivialization S.borel Q S.iwasawa .minus 0).symm fQ := by
    apply Subtype.ext
    funext k
    exact hf k
  intro g
  change e (inducingAction S.borel P .plus 0 (S.iwasawa.borelPart g)
    ((actualCanonicalContinued F q ζ hζ S P μ hμ .minus 0 φ).val
      (S.iwasawa.compactPart g))) =
    inducingAction S.borel Q .plus 0 (S.iwasawa.borelPart g)
      ((actualCanonicalContinued F q ζ hζ S Q μ hμ .minus 0
        ((compactTrivialization S.borel Q S.iwasawa .minus 0).symm fQ)).val
        (S.iwasawa.compactPart g))
  rw [inducing_action_naturality F ζ hζ q S P Q e]
  congr 1
  have H := actual_compact_svn_naturality F ζ hζ q S P Q e μ hμ .minus 0
    (denominator_ne_zero_at_zero (LocalField F q) .minus) φ (S.iwasawa.compactPart g)
  change e ((actualCanonicalContinued F q ζ hζ S P μ hμ .minus 0 φ).val
    (S.iwasawa.compactPart g)) =
    (actualCanonicalContinued F q ζ hζ S Q μ hμ .minus 0
      (compact_svn_map F ζ hζ q S P Q e .minus φ)).val (S.iwasawa.compactPart g) at H
  rw [hφ] at H
  exact H

end DedekindZetaZeroFree.ActualReverseMinorSvN

end

end

section

noncomputable section
open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.ActualReverseMinorPolarization
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneShellRepair
open _root_.DedekindZetaZeroFree.ActualReverseMinorSvN renaming inducing_action_naturality → inducing_action_naturality
open _root_.DedekindZetaZeroFree.ActualReverseMinorSvN renaming actual_reverse_svn_naturality → actual_reverse_svn_naturality
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q)
  (P Q : Polarization S.heisenberg) (e : (tau P).Equiv (tau Q))

 def section_svn_map (ε : Sign) (s : ℂ) :
    sectionSpace S.borel P ε s →ₗ[ℂ] sectionSpace S.borel Q ε s where
  toFun f := ⟨fun g => e (f.val g), by
    constructor
    · intro b g
      change e (f.val (b.val * g)) = inducingAction S.borel Q ε s b (e (f.val g))
      rw [f.property.1 b g]
      exact inducing_action_naturality F ζ hζ q S P Q e ε s b (f.val g)
    · obtain ⟨J, hJ⟩ := f.property.2
      refine ⟨J, ?_⟩
      intro j hj
      funext g
      exact congrArg e (congrFun (hJ j hj) g)⟩
  map_add' := by intros; ext g; simp
  map_smul' := by intros; ext g; simp

def section_svn_equiv (ε : Sign) (s : ℂ) :
    sectionSpace S.borel P ε s ≃ₗ[ℂ] sectionSpace S.borel Q ε s where
  toLinearMap := section_svn_map F ζ hζ q S P Q e ε s
  invFun := section_svn_map F ζ hζ q S Q P e.symm ε s
  left_inv := by intro f; apply Subtype.ext; funext g; exact e.symm_apply_apply (f.val g)
  right_inv := by intro f; apply Subtype.ext; funext g; exact e.apply_symm_apply (f.val g)

 def principal_svn_equiv (ε : Sign) (s : ℂ) :
    (principalSeries S.borel P ε s).Equiv (principalSeries S.borel Q ε s) where
  toLinearEquiv := section_svn_equiv F ζ hζ q S P Q e ε s
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext x
    rfl

private theorem actual_reverse_square
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1) :
    (section_svn_equiv F ζ hζ q S P Q e .plus 0).toLinearMap.comp
        (actualCanonicalReverseMap F ζ hζ q S P μ hμ).toLinearMap =
      (actualCanonicalReverseMap F ζ hζ q S Q μ hμ).toLinearMap.comp
        (section_svn_equiv F ζ hζ q S P Q e .minus 0).toLinearMap := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext g
  exact actual_reverse_svn_naturality F ζ hζ q S P Q e μ hμ f
    (section_svn_equiv F ζ hζ q S P Q e .minus 0 f) (fun _ => rfl) g

 local instance sectionAddCommGroup
    (R : Polarization S.heisenberg) (ε : Sign) (s : ℂ) :
    AddCommGroup (sectionSpace S.borel R ε s) := inferInstance

 def twisted_root_equiv
    {G N V W : Type*} [Group G] [Group N]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (n : N →* G) (ψ : N →* ℂˣ) (u : ρ.Equiv σ) :
    RootCoinvariants ρ n ψ ≃ₗ[ℂ] RootCoinvariants σ n ψ where
  toLinearMap := rootCoinvariantsMap ρ σ n ψ u.toIntertwiningMap
  invFun := rootCoinvariantsMap σ ρ n ψ u.symm.toIntertwiningMap
  left_inv := by
    intro x
    obtain ⟨v, rfl⟩ := rootCoinvariantsMk_surjective ρ n ψ x
    change rootCoinvariantsMk ρ n ψ (u.symm (u v)) = _
    rw [u.symm_apply_apply]
  right_inv := by
    intro x
    obtain ⟨v, rfl⟩ := rootCoinvariantsMk_surjective σ n ψ x
    change rootCoinvariantsMk σ n ψ (u (u.symm v)) = _
    rw [u.apply_symm_apply]

 def section_root_equiv (ε : Sign) (s : ℂ)
    {N : Type*} [Group N] (n : N →* ActualCover F ζ hζ q) (ψ : N →* ℂˣ) :
    RootCoinvariants (principalSeries S.borel P ε s) n ψ ≃ₗ[ℂ]
      RootCoinvariants (principalSeries S.borel Q ε s) n ψ :=
  twisted_root_equiv _ _ n ψ (principal_svn_equiv F ζ hζ q S P Q e ε s)

theorem actual_reverse_pair_transport
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
    {N : Type*} [Group N] (n : N →* ActualCover F ζ hζ q) (ψ : N →* ℂˣ)
    (v₁ v₂ : sectionSpace S.borel P .minus 0)
    (h : LinearIndependent ℂ ![
      rootCoinvariantsMk (IPlus S.borel P) n ψ
        (actualCanonicalReverseMap F ζ hζ q S P μ hμ v₁),
      rootCoinvariantsMk (IPlus S.borel P) n ψ
        (actualCanonicalReverseMap F ζ hζ q S P μ hμ v₂)]) :
    LinearIndependent ℂ ![
      rootCoinvariantsMk (IPlus S.borel Q) n ψ
        (actualCanonicalReverseMap F ζ hζ q S Q μ hμ
          (section_svn_equiv F ζ hζ q S P Q e .minus 0 v₁)),
      rootCoinvariantsMk (IPlus S.borel Q) n ψ
        (actualCanonicalReverseMap F ζ hζ q S Q μ hμ
          (section_svn_equiv F ζ hζ q S P Q e .minus 0 v₂))] := by
  let E := section_root_equiv F ζ hζ q S P Q e .plus 0 n ψ
  have H := h.map' E.toLinearMap (LinearMap.ker_eq_bot.mpr E.injective)
  have he (v : sectionSpace S.borel P .minus 0) :
      E (rootCoinvariantsMk (IPlus S.borel P) n ψ
        (actualCanonicalReverseMap F ζ hζ q S P μ hμ v)) =
      rootCoinvariantsMk (IPlus S.borel Q) n ψ
        (actualCanonicalReverseMap F ζ hζ q S Q μ hμ
          (section_svn_equiv F ζ hζ q S P Q e .minus 0 v)) := by
    change rootCoinvariantsMk (IPlus S.borel Q) n ψ
      (section_svn_equiv F ζ hζ q S P Q e .plus 0
        (actualCanonicalReverseMap F ζ hζ q S P μ hμ v)) = _
    exact congrArg (rootCoinvariantsMk (IPlus S.borel Q) n ψ)
      (LinearMap.congr_fun (actual_reverse_square F ζ hζ q S P Q e μ hμ) v)
  have hv : E.toLinearMap ∘ ![
      rootCoinvariantsMk (IPlus S.borel P) n ψ
        (actualCanonicalReverseMap F ζ hζ q S P μ hμ v₁),
      rootCoinvariantsMk (IPlus S.borel P) n ψ
        (actualCanonicalReverseMap F ζ hζ q S P μ hμ v₂)] = ![
      rootCoinvariantsMk (IPlus S.borel Q) n ψ
        (actualCanonicalReverseMap F ζ hζ q S Q μ hμ
          (section_svn_equiv F ζ hζ q S P Q e .minus 0 v₁)),
      rootCoinvariantsMk (IPlus S.borel Q) n ψ
        (actualCanonicalReverseMap F ζ hζ q S Q μ hμ
          (section_svn_equiv F ζ hζ q S P Q e .minus 0 v₂))] := by
    funext i
    fin_cases i <;> exact he _
  exact hv ▸ H

end DedekindZetaZeroFree.ActualReverseMinorPolarization

end

end
