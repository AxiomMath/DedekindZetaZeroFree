module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Cubic.SixthRootParameterBaseChange
public import DedekindZetaZeroFree.Metaplectic.Intertwining.Cubic.TwistedMellinBetaFactorization
public import DedekindZetaZeroFree.Metaplectic.Intertwining.Cubic.ShiftedBetaContinuation
public import DedekindZetaZeroFree.Theta.Profiles.TwistedMellinGeometricTails
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.RegulatedDiagonalKernel
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RationalMatrixEntries
public import DedekindZetaZeroFree.Metaplectic.Intertwining.Cubic.DoubleCoefficientRestriction
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ReverseShellExpansion
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.UpperRootTranslationsAndSectionDetermination

@[expose] public section

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel

namespace DedekindZetaZeroFree.KPActualScalarBinding.ResidueSteps

open KPLocalStoneVonNeumann KPRankOneCubicResidueReduction
open KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneGenericComposition KPRankOneRootParameter

noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : HeightOneSpectrum (𝓞 F))

open KPRankOneCenterInducedDiagonalComparison KPRankOneReverseRegulatorShells
open KPRankOneOpenCellKernel

namespace ActualShellPort
open scoped Classical
open KPActualResidueSources KPRankOneLiftedRegulatedDiagonalAlgebra
set_option autoImplicit false
private theorem rational_ext {K : Type*} [Field K] (R S : RatFunc K) (u : Set K) (hu : u.Infinite)
    (he : ∀ a ∈ u, R.denom.eval a ≠ 0 ∧ S.denom.eval a ≠ 0 ∧
      RatFunc.eval (RingHom.id K) a R = RatFunc.eval (RingHom.id K) a S) : R = S := by
  have hp : R.num * S.denom = S.num * R.denom := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply hu.mono
    intro a ha
    obtain ⟨hR,hS,h⟩ := he a ha
    simp only [RatFunc.eval, Polynomial.eval₂_id] at h
    change Polynomial.eval a (R.num * S.denom) = Polynomial.eval a (S.num * R.denom)
    simpa only [Polynomial.eval_mul] using (div_eq_div_iff hR hS).mp h
  have hh := (RatFunc.num_mul_eq_mul_denom_iff (RatFunc.denom_ne_zero S)).mp hp
  rwa [RatFunc.num_div_denom] at hh

private theorem shell_two_variable_rational_unique (R S : RatFunc (RatFunc ℂ))
    (u v : Set ℂ) (hui : u.Infinite) (hvi : v.Infinite)
    (he : ∀ r ∈ u, ∀ Q ∈ v,
      RatFunc.eval (RingHom.id ℂ) r (RatFunc.eval (RingHom.id (RatFunc ℂ)) (RatFunc.C Q) R) =
      RatFunc.eval (RingHom.id ℂ) r (RatFunc.eval (RingHom.id (RatFunc ℂ)) (RatFunc.C Q) S)) :
    R = S := by
  let bad : Set (RatFunc ℂ) := {Q | R.denom.IsRoot Q} ∪ {Q | S.denom.IsRoot Q}
  have hbad : bad.Finite :=
    (Polynomial.finite_setOf_isRoot (RatFunc.denom_ne_zero R)).union
      (Polynomial.finite_setOf_isRoot (RatFunc.denom_ne_zero S))
  have hgood : (v \ (RatFunc.C ⁻¹' bad)).Infinite := hvi.diff (hbad.preimage RatFunc.C_injective.injOn)
  apply rational_ext R S (RatFunc.C '' (v \ (RatFunc.C ⁻¹' bad)))
    (hgood.image RatFunc.C_injective.injOn)
  rintro _ ⟨Q,hQ,rfl⟩
  have hdR : R.denom.eval (RatFunc.C Q) ≠ 0 := fun h => hQ.2 (Or.inl h)
  have hdS : S.denom.eval (RatFunc.C Q) ≠ 0 := fun h => hQ.2 (Or.inr h)
  refine ⟨hdR,hdS,?_⟩
  let RQ := RatFunc.eval (RingHom.id (RatFunc ℂ)) (RatFunc.C Q) R
  let SQ := RatFunc.eval (RingHom.id (RatFunc ℂ)) (RatFunc.C Q) S
  let badr : Set ℂ := {r | RQ.denom.IsRoot r} ∪ {r | SQ.denom.IsRoot r}
  have hbadr : badr.Finite :=
    (Polynomial.finite_setOf_isRoot (RatFunc.denom_ne_zero RQ)).union
      (Polynomial.finite_setOf_isRoot (RatFunc.denom_ne_zero SQ))
  apply rational_ext RQ SQ (u \ badr) (hui.diff hbadr)
  intro r hr
  exact ⟨fun h => hr.2 (Or.inl h), fun h => hr.2 (Or.inr h), he r hr.1 Q hQ.1⟩

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
variable (S : ActualKPBinding F ζ hζ q) (P : Polarization S.heisenberg)
variable [DecidableEq S.D]

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in
 def actualHilbertCharacter (c : (LocalField F q)ˣ) : (LocalField F q)ˣ →ₜ* ℂˣ := by
  let _ : TopologicalSpace (rootsOfUnity 3 F) := ⊥
  let _ : DiscreteTopology (rootsOfUnity 3 F) := ⟨rfl⟩
  refine { toFun := fun x => KPExceptionalRaw.ordinaryIota F ζ hζ (KPHilbert.B3 F ζ hζ (Sum.inr q) c x), map_one' := ?_, map_mul' := ?_, continuous_toFun := ?_ }
  · have hb : KPHilbert.B3 F ζ hζ (Sum.inr q) c 1 = 1 := by
      have h := (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.1 c 1 1
      simp only [one_mul] at h
      exact (mul_eq_left.mp h.symm)
    rw [hb,map_one]
  · intro x y
    rw [(KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.1,map_mul]
  · have hB := (KPHilbert.B3_continuous F ζ hζ (Sum.inr q)).comp
      ((continuous_const : Continuous (fun _ : (LocalField F q)ˣ => c)).prodMk continuous_id)
    have hI : Continuous (fun e : rootsOfUnity 3 F => KPExceptionalRaw.ordinaryIota F ζ hζ e) :=
      continuous_of_discreteTopology
    exact hI.comp hB
private lemma actualHilbertCharacter_cubic (c x : (LocalField F q)ˣ) :
    actualHilbertCharacter F ζ hζ q c x ^ 3 = 1 := by
  change (KPExceptionalRaw.ordinaryIota F ζ hζ _ ) ^ 3 = 1
  rw [← map_pow]
  have h : (KPHilbert.B3 F ζ hζ (Sum.inr q) c x)^3 = 1 := by
    apply Subtype.ext
    exact (mem_rootsOfUnity 3 _).mp (KPHilbert.B3 F ζ hζ (Sum.inr q) c x).property
  rw [h,map_one]
private lemma actualHilbertCharacter_eq_one_iff (c : (LocalField F q)ˣ) :
    actualHilbertCharacter F ζ hζ q c = 1 ↔ c ∈ CubicCharacters.cubes (LocalField F q)ˣ := by
  constructor
  · intro hc
    rw [← QuotientGroup.eq_one_iff]
    change ClassFieldTheory.powerClass (q.adicCompletion F) 3 c = 1
    apply NormalizedSymbolTransport.inverseTransport_left_nondegenerate
      (KPHilbert.finiteRootsThree F ζ hζ q)
      (ClassFieldTheory.finitePlaceAdicHilbertPairingFamily F 3 (KPHilbert.rootsThree F ζ hζ) q)
      (ClassFieldTheory.finitePlaceAdicHilbertPairingFamily_isLocallyHilbert F 3
        (KPHilbert.rootsThree F ζ hζ) q).2.2.1.1
    intro b
    induction b using QuotientGroup.induction_on with
    | H b =>
      have hh := congrArg (fun χ : (LocalField F q)ˣ →ₜ* ℂˣ => χ b) hc
      change KPExceptionalRaw.ordinaryIota F ζ hζ (KPHilbert.B3 F ζ hζ (Sum.inr q) c b) = 1 at hh
      apply (KPHilbert.B3_canonical F ζ hζ q c b).symm.trans
      apply KPExceptionalRaw.ordinaryIota_injective F ζ hζ
      simpa only [map_one] using hh
  · intro hc
    obtain ⟨y,hy⟩ := hc
    ext x
    change (KPExceptionalRaw.ordinaryIota F ζ hζ (KPHilbert.B3 F ζ hζ (Sum.inr q) c x) : ℂ) = 1
    have hy' : y^3 = c := hy
    change (KPExceptionalRaw.ordinaryIota F ζ hζ (KPHilbert.B3 F ζ hζ (Sum.inr q) c x) : ℂ) = 1
    rw [← hy']
    have h : KPHilbert.B3 F ζ hζ (Sum.inr q) (y^3) x = 1 := by
      let f : (LocalField F q)ˣ →* rootsOfUnity 3 F :=
        { toFun := fun z => KPHilbert.B3 F ζ hζ (Sum.inr q) z x
          map_one' := by
            have h := (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).1 1 1 x
            simp only [one_mul] at h
            exact mul_eq_left.mp h.symm
          map_mul' := fun u v => (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).1 u v x }
      change f (y^3) = 1
      rw [map_pow]
      apply Subtype.ext
      exact (mem_rootsOfUnity 3 _).mp (f y).property
    change (KPExceptionalRaw.ordinaryIota F ζ hζ (KPHilbert.B3 F ζ hζ (Sum.inr q) (y^3) x) : ℂ) = 1
    have hi := congrArg (fun e : rootsOfUnity 3 F => (KPExceptionalRaw.ordinaryIota F ζ hζ e : ℂ)) h
    simpa only [map_one, Units.val_one] using hi
private lemma actualUc_neg_one
    (S : ActualKPBinding F ζ hζ q) (P : Polarization S.heisenberg) [DecidableEq S.D]
    (rep : S.D → KPExceptionalRaw.actualTorus F ζ hζ q)
    (hrep : ∀ d, S.heisenberg.π (rep d) = d) (d e : S.D) (r : ℂˣ) :
    UcProposal.actualUc F ζ hζ q S P rep hrep d (-1)
      (KPRankOneReverseRegulatorShells.additiveParameter F q r) (rep e) =
      if e=d then 1 else 0 := by
  have he (u : rootsOfUnity 3 F) : (S.openCell P).centralTorus u = (S.central u : _) := by
    apply Subtype.val_injective
    rw [← S.torus_full, (S.openCell P).central_eq, S.central_actual]
  have hm (u : rootsOfUnity 3 F) : (S.openCell P).centralTorus u ∈ S.heisenberg.C := by
    rw [he]; exact (S.central u).property
  have hc (u : rootsOfUnity 3 F) : S.heisenberg.ω ⟨(S.openCell P).centralTorus u,hm u⟩ =
      (S.openCell P).eta u := by
    rw [S.openCell_ordinary]
    convert S.central_character u using 1
    congr 1
    apply Subtype.val_injective
    exact he u
  let t₀ : ℂˣ := Units.mk0 (KPRankOneReverseRegulatorShells.t F q r) (by
    unfold KPRankOneReverseRegulatorShells.t
    exact mul_ne_zero (inv_ne_zero (by exact_mod_cast (Nat.card_pos (α :=
      IsLocalRing.ResidueField (Valuation.integer (valuation (LocalField F q))))).ne'))
      (pow_ne_zero _ r.ne_zero))
  have h := KPRankOneLiftedDiagonal.diagonal_center_action F ζ hζ q
    S.heisenberg S.borel P (S.openCell P) hm hc r t₀ rfl 1 1 1
    ((centerCoordinates S.heisenberg rep hrep).symm (Pi.single d (1:ℂ))) (rep e)
  have hv := congrFun ((centerCoordinates S.heisenberg rep hrep).apply_symm_apply
    (Pi.single d (1:ℂ))) e
  change (((centerCoordinates S.heisenberg rep hrep).symm (Pi.single d (1:ℂ))).val (rep e)) = _ at hv
  unfold UcProposal.actualUc doubleKernel
  simp only [reverseIncrement, one_pow, mul_one, one_mul, one_smul]
  simp only [normPower, zero_mul, Complex.exp_zero, mul_one] at h ⊢
  simp only [one_pow, mul_one, KPCubicExpansion.omega, KPCubicExpansion.valuationExponent,
    map_one, WithZero.log_one, neg_zero, zero_mul, Complex.exp_zero, inv_one, one_mul] at h
  rw [h, hv]
  simp [Pi.single_apply]

private theorem shell_domain_parameter (r w : ℂ) (hw : (r,w) ∈ KPRankOneRegulatedDiagonalKernel.jointRationalDomain F q) :
    ∃ (ru tu : ℂˣ) (lam : ℂ), (ru : ℂ) = r ∧ (tu : ℂ) = KPRankOneReverseRegulatorShells.t F q (ru : ℂ) ∧ Q F q lam = w ∧ KPJointRegulator.cone (LocalField F q) tu lam := by
  have hc : (1 : ℝ) < residueCardinality (LocalField F q) := by
    exact_mod_cast (Finite.one_lt_card (α := IsLocalRing.ResidueField (Valuation.integer (ValuativeRel.valuation (LocalField F q)))))
  have hl : Real.log (residueCardinality (LocalField F q) : ℝ) ≠ 0 := (Real.log_pos hc).ne'
  have hlC : (Real.log (residueCardinality (LocalField F q) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hl
  have hw0 : w ≠ 0 := norm_pos_iff.mp (lt_trans (inv_pos.mpr (lt_trans zero_lt_one hc)) hw.1)
  have ht : KPRankOneReverseRegulatorShells.t F q r ≠ 0 := norm_pos_iff.mp (lt_trans (pow_pos (norm_pos_iff.mpr hw0) 3) hw.2.2.1)
  have hr : r ≠ 0 := by intro h; simp [h,KPRankOneReverseRegulatorShells.t] at ht
  let ru := Units.mk0 r hr
  let tu := Units.mk0 (KPRankOneReverseRegulatorShells.t F q r) ht
  let lam := -Complex.log w / (Real.log (residueCardinality (LocalField F q) : ℝ) : ℂ)
  have hQ : Q F q lam = w := by
    unfold Q lam
    rw [show -(-Complex.log w / (Real.log (residueCardinality (LocalField F q) : ℝ) : ℂ)) * (Real.log (residueCardinality (LocalField F q) : ℝ) : ℂ) = Complex.log w by field_simp]
    exact Complex.exp_log hw0
  refine ⟨ru,tu,lam,rfl,rfl,hQ,?_⟩
  apply (KPRankOneRegulatedDiagonalKernel.cone_iff_jointRationalDomain F q ru tu rfl lam).mpr
  simpa only [hQ, ru, Units.val_mk0] using hw

private theorem shell_joint_cone_continuation_unique (R S : RatFunc (RatFunc ℂ))
    (he : ∀ (r t₀ : ℂˣ), (t₀ : ℂ) = KPRankOneReverseRegulatorShells.t F q (r : ℂ) → ∀ ρ : ℂ,
      KPJointRegulator.cone (LocalField F q) t₀ ρ →
      evaluateRational R r (Q F q ρ) = evaluateRational S r (Q F q ρ)) : R = S := by
  obtain ⟨ho,_,⟨p,hp⟩⟩ :=
    KPRankOneRegulatedDiagonalKernel.jointRationalDomain_open_connected_nonempty F q
  obtain ⟨u,v,hu,hv,hpu,hpv,huv⟩ := isOpen_prod_iff.mp ho p.1 p.2 hp
  have hui : u.Infinite := infinite_of_mem_nhds p.1 (hu.mem_nhds hpu)
  have hvi : v.Infinite := infinite_of_mem_nhds p.2 (hv.mem_nhds hpv)
  apply shell_two_variable_rational_unique R S u v hui hvi
  intro r hr w hw
  obtain ⟨ru,tu,ρ,hru,htu,hQ,hcone⟩ := shell_domain_parameter F q r w (huv ⟨hr,hw⟩)
  have h := he ru tu htu ρ hcone
  simpa only [hru,hQ,evaluateRational] using h

private theorem actual_shell_rational_model_unique
    (dx : Measure (LocalField F q))
    (Jreg : CenterStandardFamily F ζ hζ q S.heisenberg S.borel S.iwasawa dx)
    (rep : S.D → KPExceptionalRaw.actualTorus F ζ hζ q)
    (hrep : ∀ d, S.heisenberg.π (rep d) = d) (d : S.D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)
    (p : KPExceptionalRaw.actualTorus F ζ hζ q → ShellNumerator)
    (hp : ∀ (r t₀ : ℂˣ), (t₀ : ℂ) = KPRankOneReverseRegulatorShells.t F q (r : ℂ) → ∀ ρ : ℂ,
      KPJointRegulator.cone (LocalField F q) t₀ ρ → ∀ h,
      H F ζ hζ q S.heisenberg S.borel P S.iwasawa dx Jreg (S.openCell P)
        rep hrep d φ hφ hcφ r ρ h =
        evaluateNumerator (p h) r (Q F q ρ) / shellDenominator F q r (Q F q ρ))
    (R : KPExceptionalRaw.actualTorus F ζ hζ q → RatFunc (RatFunc ℂ))
    (hR : ∀ (r t₀ : ℂˣ), (t₀ : ℂ) = KPRankOneReverseRegulatorShells.t F q (r : ℂ) → ∀ ρ : ℂ,
      KPJointRegulator.cone (LocalField F q) t₀ ρ → ∀ h,
      H F ζ hζ q S.heisenberg S.borel P S.iwasawa dx Jreg (S.openCell P)
        rep hrep d φ hφ hcφ r ρ h = evaluateRational (R h) r (Q F q ρ)) :
    ∀ h, rationalH F q (p h) = R h := by
  intro h
  apply shell_joint_cone_continuation_unique F q
  intro r t₀ ht₀ ρ hcone
  have hd : shellDenominator F q r (Q F q ρ) ≠ 0 :=
    shellDenominator_ne_zero F q r
      (by
        change 1-KPRankOneReverseRegulatorShells.t F q (r:ℂ) ≠ 0
        rw [← ht₀]
        intro he
        have hn := hcone.2.2.2
        rw [← sub_eq_zero.mp he, norm_one] at hn
        exact lt_irrefl _ hn)
      ρ ⟨hcone.2.1,by
        change (KPCubicUnitIndices.residueCard (LocalField F q) : ℝ).rpow (-3*ρ.re) < _
        rw [← ht₀]
        exact hcone.2.2.1⟩
  rw [evaluateRational_rationalH F q (p h) r (Q F q ρ) r.ne_zero
    (Complex.exp_ne_zero _) hd, ← hp r t₀ ht₀ ρ hcone h]
  exact hR r t₀ ht₀ ρ hcone h

 def Regular {F : Type*} [Field F] (u : F) (r : RatFunc F) : Prop :=
  r.denom.eval u ≠ 0

private lemma regular_C {F : Type*} [Field F] (u c : F) : Regular u (RatFunc.C c) := by
  simp [Regular]
private lemma regular_X {F : Type*} [Field F] (u : F) : Regular u (RatFunc.X : RatFunc F) := by
  simp [Regular]
private lemma regular_add {F : Type*} [Field F] {u : F} {r s : RatFunc F}
    (hr : Regular u r) (hs : Regular u s) : Regular u (r+s) := by
  exact fun h => (mul_ne_zero hr hs) (by
    simpa using Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (RatFunc.denom_add_dvd r s) h)
private lemma regular_mul_eval {F : Type*} [Field F] {u : F} {r s : RatFunc F}
    (hr : Regular u r) (hs : Regular u s) : Regular u (r*s) := by
  exact fun h => (mul_ne_zero hr hs) (by
    simpa using Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (RatFunc.denom_mul_dvd r s) h)
private lemma regular_inv {F : Type*} [Field F] {u : F} {r : RatFunc F}
    (_hr : Regular u r) (hv : RatFunc.eval (RingHom.id F) u r ≠ 0) : Regular u r⁻¹ := by
  have hr0 : r ≠ 0 := by intro h; simp [h] at hv
  intro h
  have hn := Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (RatFunc.denom_inv_dvd hr0) h
  apply hv
  simp [RatFunc.eval, hn]
private lemma eval_inv {F : Type*} [Field F] {u : F} {r : RatFunc F}
    (hr : Regular u r) (hv : RatFunc.eval (RingHom.id F) u r ≠ 0) :
    RatFunc.eval (RingHom.id F) u r⁻¹ = (RatFunc.eval (RingHom.id F) u r)⁻¹ := by
  have hr0 : r ≠ 0 := by intro h; simp [h] at hv
  have hm := RatFunc.eval_mul (f := RingHom.id F) (a := u) hr (regular_inv hr hv)
  rw [mul_inv_cancel₀ hr0, RatFunc.eval_one] at hm
  exact eq_inv_of_mul_eq_one_right hm.symm

 def Evaluates {F : Type*} [Field F] (u : F) (r : RatFunc F) (v : F) : Prop :=
  Regular u r ∧ RatFunc.eval (RingHom.id F) u r = v
private lemma Evaluates.const {F : Type*} [Field F] (u v : F) : Evaluates u (RatFunc.C v) v :=
  ⟨regular_C u v, by simp⟩
private lemma Evaluates.var {F : Type*} [Field F] (u : F) : Evaluates u RatFunc.X u :=
  ⟨regular_X u, by simp⟩
private lemma Evaluates.add {F : Type*} [Field F] {u a b : F} {r s : RatFunc F}
    (hr : Evaluates u r a) (hs : Evaluates u s b) : Evaluates u (r+s) (a+b) := by
  refine ⟨regular_add hr.1 hs.1, ?_⟩
  rw [RatFunc.eval_add (RingHom.id F) u hr.1 hs.1, hr.2, hs.2]
private lemma Evaluates.mul {F : Type*} [Field F] {u a b : F} {r s : RatFunc F}
    (hr : Evaluates u r a) (hs : Evaluates u s b) : Evaluates u (r*s) (a*b) := by
  refine ⟨regular_mul_eval hr.1 hs.1, ?_⟩
  rw [RatFunc.eval_mul (RingHom.id F) u hr.1 hs.1, hr.2, hs.2]
private lemma Evaluates.neg {F : Type*} [Field F] {u a : F} {r : RatFunc F}
    (hr : Evaluates u r a) : Evaluates u (-r) (-a) := by
  simpa only [map_neg, map_one, neg_one_mul] using (Evaluates.const u (-1)).mul hr
private lemma Evaluates.sub {F : Type*} [Field F] {u a b : F} {r s : RatFunc F}
    (hr : Evaluates u r a) (hs : Evaluates u s b) : Evaluates u (r-s) (a-b) := by
  simpa only [sub_eq_add_neg] using hr.add hs.neg
private lemma Evaluates.inv {F : Type*} [Field F] {u a : F} {r : RatFunc F}
    (hr : Evaluates u r a) (ha : a ≠ 0) : Evaluates u r⁻¹ a⁻¹ := by
  have hv : RatFunc.eval (RingHom.id F) u r ≠ 0 := hr.2 ▸ ha
  exact ⟨regular_inv hr.1 hv, by rw [eval_inv hr.1 hv, hr.2]⟩
private lemma Evaluates.div {F : Type*} [Field F] {u a b : F} {r s : RatFunc F}
    (hr : Evaluates u r a) (hs : Evaluates u s b) (hb : b ≠ 0) : Evaluates u (r/s) (a/b) := by
  simpa only [div_eq_mul_inv] using hr.mul (hs.inv hb)
private lemma Evaluates.pow {F : Type*} [Field F] {u a : F} {r : RatFunc F}
    (hr : Evaluates u r a) (n : ℕ) : Evaluates u (r^n) (a^n) := by
  induction n with
  | zero => simpa only [pow_zero, map_one] using Evaluates.const u 1
  | succ n ih => simpa only [pow_succ] using ih.mul hr
private lemma Evaluates.zpow {F : Type*} [Field F] {u a : F} {r : RatFunc F}
    (hr : Evaluates u r a) (ha : a ≠ 0) (n : ℤ) : Evaluates u (r^n) (a^n) := by
  cases n with
  | ofNat n => simpa using hr.pow n
  | negSucc n => simpa only [zpow_negSucc] using (hr.pow (n+1)).inv (pow_ne_zero _ ha)
private lemma Evaluates.sum {F I : Type*} [Field F] {u : F} (s : Finset I)
    {r : I → RatFunc F} {a : I → F} (h : ∀ i ∈ s, Evaluates u (r i) (a i)) :
    Evaluates u (∑ i ∈ s, r i) (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, map_zero] using Evaluates.const u 0
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

 def rationalR {E : Type*} [Field E] (a m b : E) (ram : Bool) (f : ℕ) : RatFunc E :=
  let A : RatFunc E := RatFunc.C a
  let B : RatFunc E := RatFunc.C b
  let Q : RatFunc E := RatFunc.X
  if ram then RatFunc.C m * A ^ f * Q ^ (1-(f : ℤ)) / (Q-A)
  else RatFunc.C m * (B-A) * (Q-A*B) / ((1-B)*(B-Q)*(Q-A))
private theorem rationalR_evaluates_one {E : Type*} [Field E] (a m b : E)
    (ha : a ≠ 1) (hb0 : b ≠ 0) (hb : b ≠ 1) (ram : Bool) (f : ℕ) :
    Evaluates (1 : E) (rationalR a m b ram f)
      (m / (1-a) * if ram then a^f else
        (1-a*b)*(1-a*b⁻¹)/((1-b)*(1-b⁻¹))) := by
  have hA := Evaluates.const (1 : E) a
  have hB := Evaluates.const (1 : E) b
  have hM := Evaluates.const (1 : E) m
  have hQ := Evaluates.var (1 : E)
  have h1 := Evaluates.const (1 : E) 1
  cases ram with
  | true =>
    have he := ((hM.mul (hA.pow f)).mul (hQ.zpow one_ne_zero (1-(f : ℤ)))).div
      (hQ.sub hA) (sub_ne_zero.mpr ha.symm)
    convert he using 1 <;> simp only [rationalR, ite_true, one_zpow, mul_one]
    ring
  | false =>
    have he := ((hM.mul (hB.sub hA)).mul (hQ.sub (hA.mul hB))).div
      (((h1.sub hB).mul (hB.sub hQ)).mul (hQ.sub hA))
      (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hb.symm) (sub_ne_zero.mpr hb)) (sub_ne_zero.mpr ha.symm))
    simp only [rationalR, Bool.false_eq_true, ite_false] at *
    convert he using 1 <;> try simp only [map_one]
    field_simp

private theorem rationalR_evaluates {E : Type*} [Field E]
    (a m b Q : E) (ram : Bool) (f : ℕ)
    (hQ : Q ≠ 0) (hQA : Q-a ≠ 0) (hb : 1-b ≠ 0) (hbQ : b-Q ≠ 0) :
    Evaluates Q (rationalR a m b ram f)
      (if ram then m*a^f*Q^(1-(f : ℤ))/(Q-a)
       else m*(b-a)*(Q-a*b)/((1-b)*(b-Q)*(Q-a))) := by
  have hA := Evaluates.const Q a
  have hB := Evaluates.const Q b
  have hM := Evaluates.const Q m
  have hX := Evaluates.var Q
  have h1 := Evaluates.const Q 1
  cases ram with
  | true =>
    have he := ((hM.mul (hA.pow f)).mul (hX.zpow hQ (1-(f : ℤ)))).div (hX.sub hA) hQA
    simpa only [rationalR,ite_true] using he
  | false =>
    have he := ((hM.mul (hB.sub hA)).mul (hX.sub (hA.mul hB))).div
      (((h1.sub hB).mul (hB.sub hX)).mul (hX.sub hA))
      (mul_ne_zero (mul_ne_zero hb hbQ) hQA)
    simpa only [rationalR,Bool.false_eq_true,ite_false,map_one] using he

 def numericBetaR
    (K : Type*) [Field K] [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (m : ℂ) (ξ : CubicUnitCharacters.Character K) (b : ℂ) : RatFunc ℂ :=
  rationalR (CubicUnitCharacters.residueCard K : ℂ)⁻¹ m b
    (if ξ=1 then false else true) (CubicUnitCharacters.conductor K ξ)

private lemma numericBetaR_one
    (K : Type*) [Field K] [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (m : ℂ) (ξ : CubicUnitCharacters.Character K)
    (b : ℂ) (hb0 : b ≠ 0) (hb1 : b ≠ 1) :
    Evaluates 1 (numericBetaR K m ξ b)
      (m/(1-(CubicUnitCharacters.residueCard K : ℂ)⁻¹) *
        KPRankoneCubicScalarSum.betaFactor K ξ b) := by
  have ha : (CubicUnitCharacters.residueCard K : ℂ)⁻¹ ≠ 1 := by
    intro h
    have he : (CubicUnitCharacters.residueCard K : ℂ) = 1 := inv_eq_one.mp h
    have he' : CubicUnitCharacters.residueCard K = 1 := by exact_mod_cast he
    have hq := KPCubicUnitIndices.two_le_residueCard K
    change 2 ≤ CubicUnitCharacters.residueCard K at hq
    omega
  have h := rationalR_evaluates_one (CubicUnitCharacters.residueCard K : ℂ)⁻¹ m b
    ha hb0 hb1 (if ξ=1 then false else true) (CubicUnitCharacters.conductor K ξ)
  by_cases hξ : ξ=1
  · simpa only [numericBetaR, KPRankoneCubicScalarSum.betaFactor, hξ, ite_true,
      Bool.false_eq_true, ite_false, KPRankoneCubicScalarSum.unramifiedFactor] using h
  · simpa only [numericBetaR, KPRankoneCubicScalarSum.betaFactor, hξ, ite_false, ite_true] using h

private lemma numericBetaR_evaluates
    (K : Type*) [Field K] [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (m : ℂ) (ξ : CubicUnitCharacters.Character K)
    (b Q : ℂ) (hQ : Q ≠ 0) (hQA : Q-(CubicUnitCharacters.residueCard K : ℂ)⁻¹ ≠ 0)
    (hb1 : 1-b ≠ 0) (hbQ : b-Q ≠ 0) :
    Evaluates Q (numericBetaR K m ξ b)
      (if ξ=1 then m*(b-(CubicUnitCharacters.residueCard K : ℂ)⁻¹)*
        (Q-(CubicUnitCharacters.residueCard K : ℂ)⁻¹*b)/
        ((1-b)*(b-Q)*(Q-(CubicUnitCharacters.residueCard K : ℂ)⁻¹))
      else m*(CubicUnitCharacters.residueCard K : ℂ)⁻¹ ^ CubicUnitCharacters.conductor K ξ *
        Q^(1-(CubicUnitCharacters.conductor K ξ : ℤ))/(Q-(CubicUnitCharacters.residueCard K : ℂ)⁻¹)) := by
  have h := rationalR_evaluates (CubicUnitCharacters.residueCard K : ℂ)⁻¹ m b Q
    (if ξ=1 then false else true) (CubicUnitCharacters.conductor K ξ) hQ hQA hb1 hbQ
  by_cases hξ : ξ=1
  · simpa only [numericBetaR,hξ,ite_true,Bool.false_eq_true,ite_false] using h
  · simpa only [numericBetaR,hξ,ite_false,ite_true] using h

private lemma finite_numeric_beta_mellin_pairing
    (K : Type*) [Field K] [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Fintype (CubicUnitCharacters.Character K)]
    [Fintype CubicCharacters.Mu3]
    (m : ℂ) (weight : CubicUnitCharacters.Character K → CubicCharacters.Mu3 → ℂ)
    (b : CubicCharacters.Mu3 → ℂ) (hb0 : ∀ ε, b ε ≠ 0) (hb1 : ∀ ε, b ε ≠ 1)
    (M : RatFunc ℂ) (C : ℂ) (hM : ((1-RatFunc.X)*M).denom.eval 1 ≠ 0)
    (eM : RatFunc.eval (RingHom.id ℂ) 1 ((1-RatFunc.X)*M) = C) :
    let R := ∑ ξ : CubicUnitCharacters.Character K, ∑ ε : CubicCharacters.Mu3,
      RatFunc.C (weight ξ ε) * numericBetaR K m ξ (b ε)
    (M*((1-RatFunc.X)*R/3)).denom.eval 1 ≠ 0 ∧
      RatFunc.eval (RingHom.id ℂ) 1 (M*((1-RatFunc.X)*R/3)) =
      C*(m/(1-(CubicUnitCharacters.residueCard K : ℂ)⁻¹) *
        ∑ ξ : CubicUnitCharacters.Character K, ∑ ε : CubicCharacters.Mu3,
          weight ξ ε * KPRankoneCubicScalarSum.betaFactor K ξ (b ε))/3 := by
  dsimp only
  have hR := Evaluates.sum Finset.univ (fun ξ _ =>
    Evaluates.sum Finset.univ (fun ε _ => (Evaluates.const (1:ℂ) (weight ξ ε)).mul
      (numericBetaR_one K m ξ (b ε) (hb0 ε) (hb1 ε))))
  have he : M*((1-RatFunc.X)*(∑ ξ : CubicUnitCharacters.Character K,
      ∑ ε : CubicCharacters.Mu3, RatFunc.C (weight ξ ε)*numericBetaR K m ξ (b ε))/3) =
      ((1-RatFunc.X)*M)*(∑ ξ : CubicUnitCharacters.Character K,
      ∑ ε : CubicCharacters.Mu3, RatFunc.C (weight ξ ε)*numericBetaR K m ξ (b ε))/3 := by ring
  rw [he]
  have h := (show Evaluates (1:ℂ) ((1-RatFunc.X)*M) C from ⟨hM,eM⟩).mul hR
  have h := h.div (Evaluates.const (1:ℂ) 3) (by norm_num)
  have hs : (∑ ξ : CubicUnitCharacters.Character K, ∑ ε : CubicCharacters.Mu3,
      weight ξ ε*(m/(1-(CubicUnitCharacters.residueCard K : ℂ)⁻¹)*
        KPRankoneCubicScalarSum.betaFactor K ξ (b ε))) =
      m/(1-(CubicUnitCharacters.residueCard K : ℂ)⁻¹)*
        ∑ ξ : CubicUnitCharacters.Character K, ∑ ε : CubicCharacters.Mu3,
          weight ξ ε*KPRankoneCubicScalarSum.betaFactor K ξ (b ε) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ξ _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ε _
    ring
  simpa only [Evaluates, Regular, map_ofNat, hs] using h

 def numericShellSlice (r : ℂ) (p : ShellNumerator) : RatFunc ℂ :=
  (p.sum (fun ij c => RatFunc.C (c*r^ij.1) * (RatFunc.X : RatFunc ℂ)^ij.2)) /
    ((1-RatFunc.C (KPRankOneReverseRegulatorShells.t F q r)) * (1-RatFunc.C (KPRankOneReverseRegulatorShells.t F q r)⁻¹ * RatFunc.X^3) *
      (1-RatFunc.C ((residueCardinality (LocalField F q) : ℂ)^(-3:ℤ)) *
        RatFunc.X^(-3:ℤ)))

private lemma numericShellSlice_evaluates (r Q : ℂ) (p : ShellNumerator)
    (hQ : Q ≠ 0) (hd : shellDenominator F q r Q ≠ 0) :
    Evaluates Q (numericShellSlice F q r p)
      (evaluateNumerator p r Q / shellDenominator F q r Q) := by
  have hnum := Evaluates.sum p.support (fun ij _ =>
    (Evaluates.const Q (p ij*r^ij.1)).mul ((Evaluates.var Q).zpow hQ ij.2))
  have hD := (((Evaluates.const Q 1).sub (Evaluates.const Q (KPRankOneReverseRegulatorShells.t F q r))).mul
    ((Evaluates.const Q 1).sub ((Evaluates.const Q (KPRankOneReverseRegulatorShells.t F q r)⁻¹).mul
      ((Evaluates.var Q).pow 3)))).mul
    ((Evaluates.const Q 1).sub ((Evaluates.const Q
      ((residueCardinality (LocalField F q) : ℂ)^(-3:ℤ))).mul
      ((Evaluates.var Q).zpow hQ (-3))))
  have hden : (1-KPRankOneReverseRegulatorShells.t F q r)*(1-(KPRankOneReverseRegulatorShells.t F q r)⁻¹*Q^3)*
      (1-(residueCardinality (LocalField F q) : ℂ)^(-3:ℤ)*Q^(-3:ℤ)) ≠ 0 := hd
  have h := hnum.div hD hden
  simpa only [numericShellSlice, evaluateNumerator, shellDenominator, Finsupp.sum,
    map_one, map_inv₀] using h

private lemma rational_unique_of_numeric_values (R S : RatFunc ℂ) (u : Set ℂ)
    (hu : u.Infinite)
    (he : ∀ Q ∈ u, RatFunc.eval (RingHom.id ℂ) Q R = RatFunc.eval (RingHom.id ℂ) Q S) :
    R = S := by
  let bad : Set ℂ := {Q | R.denom.IsRoot Q} ∪ {Q | S.denom.IsRoot Q}
  have hb : bad.Finite := (Polynomial.finite_setOf_isRoot (RatFunc.denom_ne_zero R)).union
    (Polynomial.finite_setOf_isRoot (RatFunc.denom_ne_zero S))
  apply rational_ext R S (u \ bad) (hu.diff hb)
  intro Q hQ
  exact ⟨fun h => hQ.2 (Or.inl h), fun h => hQ.2 (Or.inr h), he Q hQ.1⟩

private lemma numericShellSlice_one (r : ℂ) (p : ShellNumerator)
    (hr : r ≠ 0) (hd : shellDenominator F q r 1 ≠ 0) :
    (numericShellSlice F q r p).denom.eval 1 ≠ 0 ∧
    (restrictionAtOne F q p).denom.eval r ≠ 0 ∧
    RatFunc.eval (RingHom.id ℂ) 1 (numericShellSlice F q r p) =
      RatFunc.eval (RingHom.id ℂ) r (restrictionAtOne F q p) := by
  have hs := numericShellSlice_evaluates F q r 1 p one_ne_zero hd
  have hnum := Evaluates.sum p.support (fun ij _ =>
    (Evaluates.const r (p ij)).mul ((Evaluates.var r).zpow hr ij.1))
  have ht := (Evaluates.const r (residueCardinality (LocalField F q) : ℂ)⁻¹).mul
    ((Evaluates.var r).pow 6)
  have ht0 : KPRankOneReverseRegulatorShells.t F q r ≠ 0 := by
    unfold KPRankOneReverseRegulatorShells.t
    exact mul_ne_zero (inv_ne_zero (by exact_mod_cast (Nat.card_pos
      (α := IsLocalRing.ResidueField (Valuation.integer (valuation (LocalField F q))))).ne'))
      (pow_ne_zero _ hr)
  have hD := (((Evaluates.const r 1).sub ht).mul
    ((Evaluates.const r 1).sub (ht.inv ht0))).mul
    ((Evaluates.const r 1).sub (Evaluates.const r
      ((residueCardinality (LocalField F q) : ℂ)^(-3:ℤ))))
  have hd' : (1-KPRankOneReverseRegulatorShells.t F q r)*(1-(KPRankOneReverseRegulatorShells.t F q r)⁻¹)*
      (1-(residueCardinality (LocalField F q) : ℂ)^(-3:ℤ)) ≠ 0 := by
    simpa only [shellDenominator, one_pow, one_zpow, mul_one] using hd
  have hv := hnum.div hD hd'
  have hres : Evaluates r (restrictionAtOne F q p)
      (evaluateNumerator p r 1 / shellDenominator F q r 1) := by
    rw [restrictionAtOne_eq]
    simpa only [Evaluates, Regular, Finsupp.sum, map_one, map_inv₀, KPRankOneReverseRegulatorShells.t, evaluateNumerator,
      shellDenominator, one_pow, one_zpow, mul_one] using hv
  exact ⟨hs.1,hres.1,hs.2.trans hres.2.symm⟩

private lemma exists_preferred_cube_representatives
    (K : Type*) [Field K] :
    ∃ cRep : KPLocalTorus.CubeClasses Kˣ → Kˣ,
      (∀ k, QuotientGroup.mk' (CubicCharacters.cubes Kˣ) (cRep k) = k) ∧ cRep 1 = -1 := by
  classical
  have hneg : (-1 : Kˣ) ∈ CubicCharacters.cubes Kˣ := by
    refine ⟨-1, ?_⟩
    change (-1 : Kˣ)^3 = -1
    norm_num
  have hmk : QuotientGroup.mk' (CubicCharacters.cubes Kˣ) (-1) = 1 := by
    exact (QuotientGroup.eq_one_iff _).mpr hneg
  have hsur : Function.Surjective (QuotientGroup.mk' (CubicCharacters.cubes Kˣ)) :=
    QuotientGroup.mk'_surjective _
  choose c hc using hsur
  refine ⟨fun k => if k=1 then -1 else c k, ?_, ?_⟩
  · intro k
    by_cases hk : k=1
    · simpa [hk] using hmk
    · simpa [hk] using hc k
  · simp

private lemma preferred_character_eq_one_iff
    (cRep : KPLocalTorus.CubeClasses (LocalField F q)ˣ → (LocalField F q)ˣ)
    (hcRep : ∀ k, QuotientGroup.mk' (CubicCharacters.cubes (LocalField F q)ˣ) (cRep k) = k)
    (k : KPLocalTorus.CubeClasses (LocalField F q)ˣ) :
    actualHilbertCharacter F ζ hζ q (cRep k) = 1 ↔ k = 1 := by
  rw [actualHilbertCharacter_eq_one_iff]
  change (cRep k ∈ CubicCharacters.cubes (LocalField F q)ˣ) ↔ _
  rw [← QuotientGroup.eq_one_iff]
  change (QuotientGroup.mk' (CubicCharacters.cubes (LocalField F q)ˣ) (cRep k) = 1) ↔ _
  rw [hcRep]

private lemma abs_localAbs (x : (LocalField F q)ˣ) :
    KPCubicHaar.abs (LocalField F q) (x : LocalField F q) = localAbs (LocalField F q) x := by
  simp [KPCubicHaar.abs, localAbs, Units.ne_zero, Real.rpow_intCast]
  rfl

private lemma actual_mellin_model
    (dx : Measure (LocalField F q)) [dx.IsAddHaarMeasure]
    (π : (LocalField F q)ˣ) (hπ : valuation (LocalField F q) π = uniformizer (LocalField F q))
    (χ : (LocalField F q)ˣ →ₜ* ℂˣ) (hχ : ∀ x, χ x^3=1)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ) :
    ∃ M : RatFunc ℂ,
      (∀ ρ : ℂ, 0<ρ.re → Evaluates (Q F q ρ) M
        (∫ x : (LocalField F q)ˣ, φ (x : LocalField F q)*(χ x : ℂ)*
          normPower (LocalField F q) x ρ ∂KPCubicHaar.multiplicativeHaar (LocalField F q) dx)) ∧
      Evaluates 1 ((1-RatFunc.X)*M)
        (if χ=1 then (KPRankOneRamifiedBeta.m (LocalField F q) dx : ℂ)*
          (1-(CubicUnitCharacters.residueCard (LocalField F q) : ℂ)⁻¹)*φ 0 else 0) := by
  obtain ⟨n₀,a,hi,he,hr,hv,_⟩ := actual_twisted_profile_geometric_tail F q dx π hπ χ hχ φ hφ hcφ
  refine ⟨_,?_,⟨hr,hv⟩⟩
  intro ρ hρ
  have h := he ρ hρ
  refine ⟨h.1, ?_⟩
  simp_rw [abs_localAbs F q] at h
  exact h.2.symm

private lemma normPower_regulator (c : (LocalField F q)ˣ) (ρ : ℂ) :
    normPower (LocalField F q) c ρ = (Q F q ρ)^KPCubicExpansion.valuationExponent (LocalField F q) c := by
  rw [normPower, ← abs_localAbs F q, KPRankOneUnramifiedBetaShells.abs_eq_q_neg_valuation,
    Real.log_zpow, Complex.ofReal_mul, Complex.ofReal_intCast, Int.cast_neg, Q,
    ← Complex.exp_int_mul]
  change Complex.exp _ = Complex.exp ((KPCubicExpansion.valuationExponent (LocalField F q) c : ℂ)*
    (-ρ*(Real.log (KPCubicUnitIndices.residueCard (LocalField F q) : ℝ) : ℂ)))
  congr 1
  ring

 def finite_numeric_full_model {I : Type*} [Fintype I]
    (K : Type*) [Field K] [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Fintype (CubicUnitCharacters.Character K)] [Fintype CubicCharacters.Mu3]
    (δ m : ℂ) (U : I → ℂ) (M : I → RatFunc ℂ)
    (weight : I → CubicUnitCharacters.Character K → CubicCharacters.Mu3 → ℂ)
    (b : CubicCharacters.Mu3 → ℂ) : RatFunc ℂ :=
  RatFunc.C (δ/3) * ∑ k : I, RatFunc.C (U k) *
    (M k*((1-RatFunc.X)*(∑ ξ : CubicUnitCharacters.Character K, ∑ ε : CubicCharacters.Mu3,
      RatFunc.C (weight k ξ ε)*numericBetaR K m ξ (b ε))/3))

private lemma finite_numeric_full_model_evaluates {I : Type*} [Fintype I]
    (K : Type*) [Field K] [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Fintype (CubicUnitCharacters.Character K)] [Fintype CubicCharacters.Mu3]
    (δ m Q : ℂ) (U : I → ℂ) (M : I → RatFunc ℂ) (v : I → ℂ)
    (weight : I → CubicUnitCharacters.Character K → CubicCharacters.Mu3 → ℂ)
    (b : CubicCharacters.Mu3 → ℂ)
    (hM : ∀ k, Evaluates Q (M k) (v k)) (hQ : Q ≠ 0)
    (hQA : Q-(CubicUnitCharacters.residueCard K : ℂ)⁻¹ ≠ 0)
    (hb1 : ∀ ε, 1-b ε ≠ 0) (hbQ : ∀ ε, b ε-Q ≠ 0) :
    Evaluates Q (finite_numeric_full_model K δ m U M weight b)
      ((δ/3)*∑ k : I, U k * (v k*((1-Q)*(∑ ξ : CubicUnitCharacters.Character K,
        ∑ ε : CubicCharacters.Mu3, weight k ξ ε *
          (if ξ=1 then m*(b ε-(CubicUnitCharacters.residueCard K : ℂ)⁻¹)*
            (Q-(CubicUnitCharacters.residueCard K : ℂ)⁻¹*b ε)/
            ((1-b ε)*(b ε-Q)*(Q-(CubicUnitCharacters.residueCard K : ℂ)⁻¹))
          else m*(CubicUnitCharacters.residueCard K : ℂ)⁻¹ ^ CubicUnitCharacters.conductor K ξ *
            Q^(1-(CubicUnitCharacters.conductor K ξ : ℤ))/(Q-(CubicUnitCharacters.residueCard K : ℂ)⁻¹)))/3))) := by
  have hb (k : I) := Evaluates.sum Finset.univ (fun ξ _ =>
    Evaluates.sum Finset.univ (fun ε _ => (Evaluates.const Q (weight k ξ ε)).mul
      (numericBetaR_evaluates K m ξ (b ε) Q hQ hQA (hb1 ε) (hbQ ε))))
  have hs := Evaluates.sum Finset.univ (fun k _ => (Evaluates.const Q (U k)).mul
    ((hM k).mul ((((Evaluates.const Q 1).sub (Evaluates.var Q)).mul (hb k)).div
      (Evaluates.const Q 3) (by norm_num))))
  simpa only [finite_numeric_full_model,map_one,map_ofNat] using (Evaluates.const Q (δ/3)).mul hs

private lemma finite_numeric_full_model_one {I : Type*} [Fintype I]
    (K : Type*) [Field K] [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Fintype (CubicUnitCharacters.Character K)] [Fintype CubicCharacters.Mu3]
    (δ m : ℂ) (U : I → ℂ) (M : I → RatFunc ℂ) (C : I → ℂ)
    (weight : I → CubicUnitCharacters.Character K → CubicCharacters.Mu3 → ℂ)
    (b : CubicCharacters.Mu3 → ℂ) (hb0 : ∀ ε, b ε ≠ 0) (hb1 : ∀ ε, b ε ≠ 1)
    (hM : ∀ k, Evaluates 1 ((1-RatFunc.X)*M k) (C k)) :
    Evaluates 1 (finite_numeric_full_model K δ m U M weight b)
      ((δ/3)*∑ k : I, U k * (C k*(m/(1-(CubicUnitCharacters.residueCard K : ℂ)⁻¹)*
        ∑ ξ : CubicUnitCharacters.Character K, ∑ ε : CubicCharacters.Mu3,
          weight k ξ ε*KPRankoneCubicScalarSum.betaFactor K ξ (b ε))/3)) := by
  have hb (k : I) := finite_numeric_beta_mellin_pairing K m (weight k) b hb0 hb1
    (M k) (C k) (hM k).1 (hM k).2
  have hs := Evaluates.sum Finset.univ (fun k _ => (Evaluates.const (1:ℂ) (U k)).mul (hb k))
  simpa only [finite_numeric_full_model] using (Evaluates.const (1:ℂ) (δ/3)).mul hs

private lemma exists_actual_finite_mellin_models
    (dx : Measure (LocalField F q)) [dx.IsAddHaarMeasure]
    (π : (LocalField F q)ˣ) (hπ : valuation (LocalField F q) π = uniformizer (LocalField F q))
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)
    (cRep : KPLocalTorus.CubeClasses (LocalField F q)ˣ → (LocalField F q)ˣ)
    (hcRep : ∀ k, QuotientGroup.mk' (CubicCharacters.cubes (LocalField F q)ˣ) (cRep k) = k) :
    ∃ M : KPLocalTorus.CubeClasses (LocalField F q)ˣ → RatFunc ℂ,
      (∀ k ρ, 0<ρ.re → Evaluates (Q F q ρ) (M k)
        (∫ x : (LocalField F q)ˣ, φ (x : LocalField F q)*
          (KPExceptionalRaw.ordinaryIota F ζ hζ (KPHilbert.B3 F ζ hζ (Sum.inr q) (cRep k) x) : ℂ)*
          normPower (LocalField F q) x ρ ∂KPCubicHaar.multiplicativeHaar (LocalField F q) dx)) ∧
      (∀ k, Evaluates 1 ((1-RatFunc.X)*M k)
        (if k=1 then (KPRankOneRamifiedBeta.m (LocalField F q) dx : ℂ)*
          (1-(CubicUnitCharacters.residueCard (LocalField F q) : ℂ)⁻¹)*φ 0 else 0)) := by
  classical
  have hm (k) := actual_mellin_model F q dx π hπ (actualHilbertCharacter F ζ hζ q (cRep k))
    (actualHilbertCharacter_cubic F ζ hζ q (cRep k)) φ hφ hcφ
  choose M hi hr using hm
  refine ⟨M,?_,?_⟩
  · intro k ρ hρ
    exact hi k ρ hρ
  · intro k
    have h := hr k
    rw [preferred_character_eq_one_iff F ζ hζ q cRep hcRep k] at h
    by_cases hk : k = 1
    · simpa only [if_pos hk] using h
    · simpa only [if_neg hk] using h

private lemma finite_numeric_full_model_identity_class
    [Fintype (KPLocalTorus.CubeClasses (LocalField F q)ˣ)]
    [Fintype (CubicUnitCharacters.Character (LocalField F q))] [Fintype CubicCharacters.Mu3]
    (dx : Measure (LocalField F q))
    (M : KPLocalTorus.CubeClasses (LocalField F q)ˣ → RatFunc ℂ)
    (r : ℂˣ) (rep : S.D → KPExceptionalRaw.actualTorus F ζ hζ q)
    (hrep : ∀ d, S.heisenberg.π (rep d) = d) (d e : S.D)
    (cRep : KPLocalTorus.CubeClasses (LocalField F q)ˣ → (LocalField F q)ˣ)
    (hneg : cRep 1 = -1) (φ : LocalField F q → ℂ)
    (weight : KPLocalTorus.CubeClasses (LocalField F q)ˣ →
      CubicUnitCharacters.Character (LocalField F q) → CubicCharacters.Mu3 → ℂ)
    (hw : ∀ ξ ε, weight 1 ξ ε = 1)
    (b : CubicCharacters.Mu3 → ℂ) (hb0 : ∀ ε, b ε ≠ 0) (hb1 : ∀ ε, b ε ≠ 1)
    (hM : ∀ k, Evaluates 1 ((1-RatFunc.X)*M k)
      (if k=1 then (KPRankOneRamifiedBeta.m (LocalField F q) dx : ℂ)*
        (1-(CubicUnitCharacters.residueCard (LocalField F q) : ℂ)⁻¹)*φ 0 else 0)) :
    Evaluates 1 (finite_numeric_full_model (LocalField F q)
      (KPCubicHaar.abs (LocalField F q) (3 : LocalField F q) : ℂ)
      (KPRankOneRamifiedBeta.m (LocalField F q) dx : ℂ)
      (fun k => UcProposal.actualUc F ζ hζ q S P rep hrep d (cRep k)
        (additiveParameter F q r) (rep e)) M weight b)
      ((KPCubicHaar.abs (LocalField F q) (3 : LocalField F q) : ℂ)*
        (KPRankOneRamifiedBeta.m (LocalField F q) dx : ℂ)^2/9*φ 0*
        (if e=d then 1 else 0)*
        ∑ ξ : CubicUnitCharacters.Character (LocalField F q), ∑ ε : CubicCharacters.Mu3,
          KPRankoneCubicScalarSum.betaFactor (LocalField F q) ξ (b ε)) := by
  classical
  have ha : 1-(CubicUnitCharacters.residueCard (LocalField F q) : ℂ)⁻¹ ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    have hq : CubicUnitCharacters.residueCard (LocalField F q) = 1 := by
      exact_mod_cast (inv_eq_one.mp he.symm)
    have h2 := KPCubicUnitIndices.two_le_residueCard (LocalField F q)
    change 2 ≤ CubicUnitCharacters.residueCard (LocalField F q) at h2
    omega
  have h := finite_numeric_full_model_one (LocalField F q)
    (KPCubicHaar.abs (LocalField F q) (3 : LocalField F q) : ℂ)
    (KPRankOneRamifiedBeta.m (LocalField F q) dx : ℂ)
    (fun k => UcProposal.actualUc F ζ hζ q S P rep hrep d (cRep k)
      (additiveParameter F q r) (rep e)) M
    (fun k => if k=1 then (KPRankOneRamifiedBeta.m (LocalField F q) dx : ℂ)*
      (1-(CubicUnitCharacters.residueCard (LocalField F q) : ℂ)⁻¹)*φ 0 else 0)
    weight b hb0 hb1 hM
  have hs : (∑ k : KPLocalTorus.CubeClasses (LocalField F q)ˣ,
      UcProposal.actualUc F ζ hζ q S P rep hrep d (cRep k) (additiveParameter F q r) (rep e)*
      ((if k=1 then (KPRankOneRamifiedBeta.m (LocalField F q) dx : ℂ)*
        (1-(CubicUnitCharacters.residueCard (LocalField F q) : ℂ)⁻¹)*φ 0 else 0)*
        ((KPRankOneRamifiedBeta.m (LocalField F q) dx : ℂ)/
        (1-(CubicUnitCharacters.residueCard (LocalField F q) : ℂ)⁻¹)*
        ∑ ξ : CubicUnitCharacters.Character (LocalField F q), ∑ ε : CubicCharacters.Mu3,
          weight k ξ ε*KPRankoneCubicScalarSum.betaFactor (LocalField F q) ξ (b ε))/3)) =
      (if e=d then 1 else 0)*((KPRankOneRamifiedBeta.m (LocalField F q) dx : ℂ)^2*φ 0*
        (∑ ξ : CubicUnitCharacters.Character (LocalField F q), ∑ ε : CubicCharacters.Mu3,
          KPRankoneCubicScalarSum.betaFactor (LocalField F q) ξ (b ε))/3) := by
    rw [Finset.sum_eq_single 1]
    · rw [hneg,actualUc_neg_one F ζ hζ q S P rep hrep d e r]
      simp only [ite_true,hw,one_mul]
      field_simp [ha]
    · intro k hk hne
      simp only [hne,ite_false,zero_mul,zero_div,mul_zero]
    · simp
  rw [hs] at h
  convert h using 1
  ring

set_option maxHeartbeats 1000000 in

private lemma actual_fixed_root_full_model
    (dx : Measure (LocalField F q)) [dx.IsAddHaarMeasure]
    (J : CenterStandardFamily F ζ hζ q S.heisenberg S.borel S.iwasawa dx)
    (rep : S.D → KPExceptionalRaw.actualTorus F ζ hζ q)
    (hrep : ∀ d, S.heisenberg.π (rep d) = d) (d e : S.D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)
    (r t₀ z : ℂˣ) (ht : (t₀ : ℂ) = KPRankOneReverseRegulatorShells.t F q (r : ℂ)) (hz : z^3=t₀)
    (hz1 : ‖(z : ℂ)‖ < 1) :
    ∃ R : RatFunc ℂ,
      (∀ ρ, KPJointRegulator.cone (LocalField F q) t₀ ρ →
        Evaluates (Q F q ρ) R
          (H F ζ hζ q S.heisenberg S.borel P S.iwasawa dx J (S.openCell P)
            rep hrep d φ hφ hcφ r ρ (rep e))) ∧
      Evaluates 1 R
        ((KPCubicHaar.abs (LocalField F q) (3 : LocalField F q) : ℂ)*
          (KPRankOneRamifiedBeta.m (LocalField F q) dx : ℂ)^2/9*φ 0*
          (if e=d then 1 else 0)*
          ∑ᶠ ξ : CubicUnitCharacters.Character (LocalField F q), ∑ᶠ ε : CubicCharacters.Mu3,
            KPRankoneCubicScalarSum.betaFactor (LocalField F q) ξ (((ε : ℂˣ) : ℂ)*(z : ℂ))) := by
  classical
  letI : Fintype S.D := Fintype.ofFinite S.D
  letI : Fintype (KPLocalTorus.CubeClasses (LocalField F q)ˣ) :=
    Fintype.ofEquiv S.D S.cubeClassEquiv.toEquiv
  haveI := KPCubicHaar.cubeUnits_finiteIndex (K := LocalField F q)
  haveI : Finite (CubicUnitCharacters.Character (LocalField F q)) :=
    Nat.finite_of_card_ne_zero (by
      rw [KPCubicExpansion.card_unit_cubic_characters]
      exact Subgroup.index_ne_zero_of_finite)
  letI := Fintype.ofFinite (CubicUnitCharacters.Character (LocalField F q))
  letI := Fintype.ofFinite CubicCharacters.Mu3
  obtain ⟨p,hp⟩ := valuation_surjective (uniformizer (LocalField F q))
  have hp0 : p ≠ 0 := by
    intro h
    simp [h] at hp
    exact uniformizer_ne_zero hp.symm
  let π := Units.mk0 p hp0
  obtain ⟨cRep,hcRep,hneg⟩ := exists_preferred_cube_representatives (LocalField F q)
  obtain ⟨M,hMi,hMr⟩ := exists_actual_finite_mellin_models F ζ hζ q dx π hp φ hφ hcφ cRep hcRep
  obtain ⟨θ,hθ,hβ,hRrat,hβrat,hβeval⟩ := actual_shifted_beta_common_zero F q ζ hζ dx π hp
  let U := fun k => UcProposal.actualUc F ζ hζ q S P rep hrep d (cRep k)
    (additiveParameter F q r) (rep e)
  let weight := fun k ξ (ε : CubicCharacters.Mu3) => (θ ξ ((ε : ℂˣ)*z) (-cRep k) : ℂ)
  let b := fun ε : CubicCharacters.Mu3 => ((ε : ℂˣ) : ℂ)*(z : ℂ)
  have hbn (ε : CubicCharacters.Mu3) : ‖b ε‖ = ‖(z : ℂ)‖ := by
    dsimp [b]
    rw [norm_mul, Complex.norm_eq_one_of_mem_rootsOfUnity ε.property, one_mul]
  have hb0 (ε) : b ε ≠ 0 := by
    exact norm_pos_iff.mp (by rw [hbn]; exact norm_pos_iff.mpr z.ne_zero)
  have hb1 (ε) : b ε ≠ 1 := by
    intro he
    have h := hz1
    rw [← hbn ε,he,norm_one] at h
    exact lt_irrefl _ h
  let R := finite_numeric_full_model (LocalField F q)
    (KPCubicHaar.abs (LocalField F q) (3 : LocalField F q) : ℂ)
    (KPRankOneRamifiedBeta.m (LocalField F q) dx : ℂ) U M weight b
  refine ⟨R,?_,?_⟩
  · intro ρ hcone
    have hd := (KPRankOneRegulatedDiagonalKernel.cone_iff_jointRationalDomain F q r t₀ ht ρ).mp hcone
    have hQ0 : Q F q ρ ≠ 0 := Complex.exp_ne_zero _
    have hQA : Q F q ρ-(CubicUnitCharacters.residueCard (LocalField F q) : ℂ)⁻¹ ≠ 0 := by
      apply sub_ne_zero.mpr
      intro he
      have h := hd.1
      rw [he,norm_inv,Complex.norm_natCast] at h
      exact lt_irrefl _ h
    have hQz : ‖Q F q ρ‖ < ‖(z : ℂ)‖ := by
      have h := hd.2.2.1
      rw [← ht, ← hz, Units.val_pow_eq_pow_val, norm_pow] at h
      exact (pow_lt_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by decide : 3 ≠ 0)).mp h
    have hbQ (ε) : b ε-Q F q ρ ≠ 0 := by
      apply sub_ne_zero.mpr
      intro he
      have h := hQz
      rw [← hbn ε,he] at h
      exact lt_irrefl _ h
    have he := finite_numeric_full_model_evaluates (LocalField F q)
      (KPCubicHaar.abs (LocalField F q) (3 : LocalField F q) : ℂ)
      (KPRankOneRamifiedBeta.m (LocalField F q) dx : ℂ) (Q F q ρ) U M
      (fun k => ∫ x : (LocalField F q)ˣ, φ (x : LocalField F q)*
        (KPExceptionalRaw.ordinaryIota F ζ hζ (KPHilbert.B3 F ζ hζ (Sum.inr q) (cRep k) x) : ℂ)*
        normPower (LocalField F q) x ρ ∂KPCubicHaar.multiplicativeHaar (LocalField F q) dx)
      weight b (fun k => hMi k ρ hcone.1) hQ0 hQA
      (fun ε => sub_ne_zero.mpr (hb1 ε).symm) hbQ
    have hf := (KPActualFullKernelArithmetic.actual_full_H_joint_factorization F ζ hζ q S P
      dx J rep hrep d φ hφ hcφ r t₀ ht ρ hcone cRep hcRep).2 (rep e)
    refine ⟨he.1,he.2.trans ?_⟩
    rw [hf]
    simp only [Complex.ofReal_div,Complex.ofReal_ofNat]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    have hb := (hβ (cRep k) t₀ z hz ρ hcone).2
    dsimp only at hb
    have hQdef : Complex.exp (-ρ*(Real.log (CubicUnitCharacters.residueCard (LocalField F q) : ℝ) : ℂ)) = Q F q ρ := rfl
    rw [hQdef] at hb
    rw [normPower_regulator F q, hb]
    simp only [finsum_eq_sum_of_fintype]
    dsimp [U,weight,b,UcProposal.actualUc]
    rw [zpow_neg, div_eq_mul_inv]
    have hpow : (Q F q ρ)^KPCubicExpansion.valuationExponent (LocalField F q) (cRep k) ≠ 0 :=
      zpow_ne_zero _ hQ0
    field_simp
    congr 1
    apply Finset.sum_congr rfl
    intro ξ hξ
    apply Finset.sum_congr rfl
    intro ε hε
    congr 1
    split_ifs <;> ring
  · have hw : ∀ ξ ε, weight 1 ξ ε = 1 := by
      intro ξ ε
      dsimp [weight]
      rw [hneg,neg_neg,map_one,Units.val_one]
    simpa only [R,U,finsum_eq_sum_of_fintype] using
      finite_numeric_full_model_identity_class F ζ hζ q S P dx M r rep hrep d e cRep hneg
        φ weight hw b hb0 hb1 hMr

private lemma norm_annulus_infinite (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    {Q : ℂ | a < ‖Q‖ ∧ ‖Q‖ < b}.Infinite := by
  have ho : IsOpen {Q : ℂ | a < ‖Q‖ ∧ ‖Q‖ < b} :=
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  let c : ℝ := (a+b)/2
  have hc0 : 0 ≤ c := by dsimp [c]; linarith
  have hmem : (c : ℂ) ∈ {Q : ℂ | a < ‖Q‖ ∧ ‖Q‖ < b} := by
    simp only [Set.mem_setOf_eq,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc0]
    dsimp [c]
    constructor <;> linarith
  exact infinite_of_mem_nhds (c : ℂ) (ho.mem_nhds hmem)

private lemma shellDenominator_one_of_cube_root
    (r t₀ z : ℂˣ) (ht : (t₀ : ℂ) = KPRankOneReverseRegulatorShells.t F q (r : ℂ)) (hz : z^3=t₀)
    (hz1 : ‖(z : ℂ)‖ < 1) : shellDenominator F q r 1 ≠ 0 := by
  have ht1 : ‖(t₀ : ℂ)‖ < 1 := by
    rw [← hz,Units.val_pow_eq_pow_val,norm_pow]
    exact (pow_lt_one₀ (norm_nonneg _) hz1 (by decide : 3 ≠ 0))
  have htne : (t₀ : ℂ) ≠ 1 := by
    intro he
    rw [he,norm_one] at ht1
    exact lt_irrefl _ ht1
  have hq1 : 1 < ‖(residueCardinality (LocalField F q) : ℂ)‖ := by
    rw [Complex.norm_natCast]
    exact_mod_cast (Finite.one_lt_card (α := IsLocalRing.ResidueField
      (Valuation.integer (valuation (LocalField F q)))))
  have hq3 : 1 < ‖(residueCardinality (LocalField F q) : ℂ)‖^3 :=
    one_lt_pow₀ hq1 (by decide)
  have hqinv : ‖(residueCardinality (LocalField F q) : ℂ)^(-3:ℤ)‖ < 1 := by
    rw [zpow_neg,norm_inv,zpow_ofNat,norm_pow]
    exact (inv_lt_one₀ (zero_lt_one.trans hq3)).mpr hq3
  have hqne : (residueCardinality (LocalField F q) : ℂ)^(-3:ℤ) ≠ 1 := by
    intro he
    rw [he,norm_one] at hqinv
    exact lt_irrefl _ hqinv
  simp only [shellDenominator,one_pow,one_zpow,mul_one,← ht]
  exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr htne.symm)
    (sub_ne_zero.mpr (by intro h; exact htne (inv_eq_one.mp h.symm))))
    (sub_ne_zero.mpr hqne.symm)

private lemma actual_fixed_root_shell_residue
    (dx : Measure (LocalField F q)) [dx.IsAddHaarMeasure]
    (J : CenterStandardFamily F ζ hζ q S.heisenberg S.borel S.iwasawa dx)
    (rep : S.D → KPExceptionalRaw.actualTorus F ζ hζ q)
    (hrep : ∀ d, S.heisenberg.π (rep d) = d) (d e : S.D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)
    (p : ShellNumerator) (r t₀ z : ℂˣ)
    (ht : (t₀ : ℂ) = KPRankOneReverseRegulatorShells.t F q (r : ℂ)) (hz : z^3=t₀)
    (hzA : (residueCardinality (LocalField F q) : ℝ)⁻¹ < ‖(z : ℂ)‖)
    (hz1 : ‖(z : ℂ)‖ < 1)
    (hp : ∀ ρ, KPJointRegulator.cone (LocalField F q) t₀ ρ →
      H F ζ hζ q S.heisenberg S.borel P S.iwasawa dx J (S.openCell P)
        rep hrep d φ hφ hcφ r ρ (rep e) =
        evaluateNumerator p r (Q F q ρ)/shellDenominator F q r (Q F q ρ)) :
    Evaluates (r : ℂ) (restrictionAtOne F q p)
      ((KPCubicHaar.abs (LocalField F q) (3 : LocalField F q) : ℂ)*
        (KPRankOneRamifiedBeta.m (LocalField F q) dx : ℂ)^2/9*φ 0*
        (if e=d then 1 else 0)*
        ∑ᶠ ξ : CubicUnitCharacters.Character (LocalField F q), ∑ᶠ ε : CubicCharacters.Mu3,
          KPRankoneCubicScalarSum.betaFactor (LocalField F q) ξ (((ε : ℂˣ) : ℂ)*(z : ℂ))) := by
  obtain ⟨R,hi,hr⟩ := actual_fixed_root_full_model F ζ hζ q S P dx J rep hrep d e
    φ hφ hcφ r t₀ z ht hz hz1
  let a : ℝ := (residueCardinality (LocalField F q) : ℝ)⁻¹
  have ha : 0 < a := by
    dsimp [a]
    exact inv_pos.mpr (by exact_mod_cast (Nat.card_pos (α := IsLocalRing.ResidueField
      (Valuation.integer (valuation (LocalField F q))))))
  have heq : numericShellSlice F q r p = R := by
    apply rational_unique_of_numeric_values _ _ {Q : ℂ | a < ‖Q‖ ∧ ‖Q‖ < ‖(z : ℂ)‖}
      (norm_annulus_infinite a ‖(z : ℂ)‖ ha.le hzA)
    intro Q₀ hQ
    have hd : ((r : ℂ),Q₀) ∈ KPRankOneRegulatedDiagonalKernel.jointRationalDomain F q := by
      refine ⟨hQ.1,hQ.2.trans hz1,?_,?_⟩
      · rw [← ht,← hz,Units.val_pow_eq_pow_val,norm_pow]
        exact (pow_lt_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by decide : 3 ≠ 0)).mpr hQ.2
      · rw [← ht,← hz,Units.val_pow_eq_pow_val,norm_pow]
        exact pow_lt_one₀ (norm_nonneg _) hz1 (by decide)
    obtain ⟨ru,tu,ρ,hru,htu,hQr,hcone⟩ := shell_domain_parameter F q r Q₀ hd
    have hru' : ru=r := Units.ext hru
    have htu' : tu=t₀ := Units.ext (by rw [htu,hru,← ht])
    subst ru
    subst tu
    have hden : shellDenominator F q r (Q F q ρ) ≠ 0 :=
      shellDenominator_ne_zero F q r
        (by
          change 1-KPRankOneReverseRegulatorShells.t F q (r:ℂ) ≠ 0
          rw [← ht]
          apply sub_ne_zero.mpr
          intro he
          have hn := hcone.2.2.2
          rw [← he,norm_one] at hn
          exact lt_irrefl _ hn)
        ρ ⟨hcone.2.1,by rw [← ht]; exact hcone.2.2.1⟩
    have hs := numericShellSlice_evaluates F q r (Q F q ρ) p (Complex.exp_ne_zero _) hden
    have hv := (hi ρ hcone).2
    rw [hp ρ hcone] at hv
    rw [← hQr]
    exact hs.2.trans hv.symm
  have hb := numericShellSlice_one F q r p r.ne_zero
    (shellDenominator_one_of_cube_root F q r t₀ z ht hz hz1)
  rw [heq] at hb
  exact ⟨hb.2.1,hb.2.2.symm.trans hr.2⟩

private lemma polynomial_evaluates (p : Polynomial ℂ) (x : ℂ) :
    Evaluates x (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) (p.eval x) := by
  refine ⟨by simp [Regular],?_⟩
  simp [RatFunc.eval,RatFunc.num_algebraMap,Polynomial.eval₂_id]

private lemma scaled_root_evaluates (α w : ℂ) (R : RatFunc ℂ)
    (hR : R.denom.eval (α*w) ≠ 0) :
    Evaluates w (RatFunc.eval (RatFunc.C : ℂ →+* RatFunc ℂ) (RatFunc.C α*RatFunc.X) R)
      (RatFunc.eval (RingHom.id ℂ) (α*w) R) := by
  have he (p : Polynomial ℂ) :
      p.eval₂ (RatFunc.C : ℂ →+* RatFunc ℂ) (RatFunc.C α*RatFunc.X) =
      algebraMap (Polynomial ℂ) (RatFunc ℂ) (p.comp (Polynomial.C α*Polynomial.X)) := by
    rw [← RatFunc.aeval_X_left_eq_algebraMap]
    simp only [Polynomial.aeval_def,RatFunc.algebraMap_eq_C,Polynomial.eval₂_comp,
      Polynomial.eval₂_mul,Polynomial.eval₂_C,Polynomial.eval₂_X]
  rw [RatFunc.eval,he,he]
  have h := (polynomial_evaluates (R.num.comp (Polynomial.C α*Polynomial.X)) w).div
    (polynomial_evaluates (R.denom.comp (Polynomial.C α*Polynomial.X)) w)
    (by simpa only [Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X] using hR)
  simpa only [Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_X,RatFunc.eval,Polynomial.eval₂_id] using h

private lemma betaFactor_evaluates
    (K : Type*) [Field K] [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ξ : CubicUnitCharacters.Character K)
    (w : ℂ) (B : RatFunc ℂ) (b : ℂ) (hB : Evaluates w B b) (hb0 : b ≠ 0) (hb1 : b ≠ 1) :
    Evaluates w (KPRankoneCubicScalarSum.betaFactor K ξ B)
      (KPRankoneCubicScalarSum.betaFactor K ξ b) := by
  classical
  have hA := (Evaluates.const w (CubicUnitCharacters.residueCard K : ℂ)⁻¹)
  have h1 := Evaluates.const w 1
  by_cases hξ : ξ=1
  · have hBi := hB.inv hb0
    have hden : (1-b)*(1-b⁻¹) ≠ 0 :=
      mul_ne_zero (sub_ne_zero.mpr hb1.symm)
        (sub_ne_zero.mpr (by intro h; exact hb1 (inv_eq_one.mp h.symm)))
    have h := ((h1.sub (hA.mul hB)).mul (h1.sub (hA.mul hBi))).div
      ((h1.sub hB).mul (h1.sub hBi)) hden
    simpa only [KPRankoneCubicScalarSum.betaFactor,hξ,ite_true,
      KPRankoneCubicScalarSum.unramifiedFactor,map_one,map_inv₀,map_natCast] using h
  · simpa only [KPRankoneCubicScalarSum.betaFactor,hξ,ite_false,map_natCast,map_inv₀] using
      hA.pow (CubicUnitCharacters.conductor K ξ)

private lemma rationalResidueScalar_evaluates
    (dx : Measure (LocalField F q)) (w : ℂ) (hw0 : w ≠ 0) (hw1 : ‖w‖ < 1) :
    Evaluates w (rationalResidueScalar (LocalField F q) dx)
      ((KPCubicHaar.abs (LocalField F q) (3 : LocalField F q) : ℂ)*
        (KPRankOneRamifiedBeta.m (LocalField F q) dx : ℂ)^2/9*
        ∑ᶠ ξ : CubicUnitCharacters.Character (LocalField F q), ∑ᶠ ε : CubicCharacters.Mu3,
          KPRankoneCubicScalarSum.betaFactor (LocalField F q) ξ (((ε : ℂˣ) : ℂ)*w^2)) := by
  classical
  haveI := KPCubicHaar.cubeUnits_finiteIndex (K := LocalField F q)
  haveI : Finite (CubicUnitCharacters.Character (LocalField F q)) :=
    Nat.finite_of_card_ne_zero (by
      rw [KPCubicExpansion.card_unit_cubic_characters]
      exact Subgroup.index_ne_zero_of_finite)
  letI := Fintype.ofFinite (CubicUnitCharacters.Character (LocalField F q))
  letI := Fintype.ofFinite CubicCharacters.Mu3
  have hb (ε : CubicCharacters.Mu3) := (Evaluates.const w ((ε : ℂˣ) : ℂ)).mul ((Evaluates.var w).pow 2)
  have hb0 (ε : CubicCharacters.Mu3) : ((ε : ℂˣ) : ℂ)*w^2 ≠ 0 :=
    mul_ne_zero (ε : ℂˣ).ne_zero (pow_ne_zero _ hw0)
  have hb1 (ε : CubicCharacters.Mu3) : ((ε : ℂˣ) : ℂ)*w^2 ≠ 1 := by
    intro he
    have hn : ‖((ε : ℂˣ) : ℂ)*w^2‖ < 1 := by
      rw [norm_mul,Complex.norm_eq_one_of_mem_rootsOfUnity ε.property,one_mul,norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) hw1 (by decide)
    rw [he,norm_one] at hn
    exact lt_irrefl _ hn
  have hs := Evaluates.sum Finset.univ (fun ξ _ => Evaluates.sum Finset.univ (fun ε _ =>
    betaFactor_evaluates (LocalField F q) ξ w _ _ (hb ε) (hb0 ε) (hb1 ε)))
  have h := (Evaluates.const w (((integerMass (LocalField F q) dx^2*
    KPCubicHaar.abs (LocalField F q) (3 : LocalField F q) : ℝ) : ℂ)/9)).mul hs
  have hm : integerMass (LocalField F q) dx = KPRankOneRamifiedBeta.m (LocalField F q) dx := rfl
  simpa only [rationalResidueScalar,finsum_eq_sum_of_fintype,hm,Complex.ofReal_mul,
    Complex.ofReal_pow,mul_comm] using h

private theorem actual_shell_restriction_residue
    (dx : Measure (LocalField F q)) [dx.IsAddHaarMeasure]
    (Jreg : CenterStandardFamily F ζ hζ q S.heisenberg S.borel S.iwasawa dx)
    (rep : S.D → KPExceptionalRaw.actualTorus F ζ hζ q)
    (hrep : ∀ d, S.heisenberg.π (rep d) = d) (d : S.D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)
    (p : KPExceptionalRaw.actualTorus F ζ hζ q → ShellNumerator)
    (hp : ∀ (r t : ℂˣ), (t : ℂ) =
      (residueCardinality (LocalField F q) : ℂ)⁻¹ * (r : ℂ)^6 →
      ∀ ρ : ℂ, KPJointRegulator.cone (LocalField F q) t ρ →
      ∀ h : KPExceptionalRaw.actualTorus F ζ hζ q,
      H F ζ hζ q S.heisenberg S.borel P S.iwasawa dx Jreg (S.openCell P)
        rep hrep d φ hφ hcφ r ρ h =
        evaluateNumerator (p h) r (Q F q ρ) / shellDenominator F q r (Q F q ρ))
    (α : ℂ) (hα : α^6 = (residueCardinality (LocalField F q) : ℂ)) :
    ∀ e : S.D,
      Polynomial.eval₂ (RatFunc.C : ℂ →+* RatFunc ℂ) (RatFunc.C α * RatFunc.X)
        (restrictionAtOne F q (p (rep e))).denom ≠ 0 ∧
      RatFunc.eval (RatFunc.C : ℂ →+* RatFunc ℂ) (RatFunc.C α * RatFunc.X)
        (restrictionAtOne F q (p (rep e))) =
        RatFunc.C (φ 0 * if e=d then 1 else 0) * rationalResidueScalar (LocalField F q) dx := by
  intro e
  constructor
  · have hq : (residueCardinality (LocalField F q) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := IsLocalRing.ResidueField
        (Valuation.integer (valuation (LocalField F q))))).ne'
    have hα0 : α ≠ 0 := by intro h; rw [h, zero_pow (by decide)] at hα; exact hq hα.symm
    exact scaled_root_rational_denom_ne_zero α hα0 _
  · by_cases hzero : φ = 0
    · have hm := actual_shell_rational_model_unique F ζ hζ q S P dx Jreg rep hrep d
        φ hφ hcφ p hp (fun _ => 0) (by
          intro r t₀ ht₀ ρ hcone h
          rw [H]
          simp_rw [reverseIntegrand_eq_zero_of_profile_eq_zero F ζ hζ q
            S.heisenberg S.borel P S.iwasawa dx Jreg (S.openCell P)
            rep hrep d φ hφ hcφ hzero r ρ h]
          simp [evaluateRational])
      have hz : restrictionAtOne F q (p (rep e)) = 0 := by
        rw [restrictionAtOne, hm (rep e), RatFunc.eval_zero]
      rw [hz]
      simp [hzero]
    · have hq0 : (residueCardinality (LocalField F q) : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.card_pos (α := IsLocalRing.ResidueField
          (Valuation.integer (valuation (LocalField F q))))).ne'
      have hα0 : α ≠ 0 := by
        intro he
        rw [he,zero_pow (by decide)] at hα
        exact hq0 hα.symm
      let a : ℝ := (residueCardinality (LocalField F q) : ℝ)⁻¹
      have hq1 : 1 < (residueCardinality (LocalField F q) : ℝ) := by
        exact_mod_cast (Finite.one_lt_card (α := IsLocalRing.ResidueField
          (Valuation.integer (valuation (LocalField F q)))))
      have ha0 : 0 < a := inv_pos.mpr (zero_lt_one.trans hq1)
      have ha1 : a < 1 := (inv_lt_one₀ (zero_lt_one.trans hq1)).mpr hq1
      have hsqrt : Real.sqrt a < 1 := by
        simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt ha0.le ha1
      apply rational_unique_of_numeric_values _ _
        {w : ℂ | Real.sqrt a < ‖w‖ ∧ ‖w‖ < 1}
        (norm_annulus_infinite (Real.sqrt a) 1 (Real.sqrt_nonneg _) hsqrt)
      intro w hw
      have hw0 : w ≠ 0 := norm_pos_iff.mp ((Real.sqrt_nonneg a).trans_lt hw.1)
      have hwA : a < ‖w^2‖ := by
        rw [norm_pow]
        have hs := Real.sq_sqrt ha0.le
        have hn := Real.sqrt_nonneg a
        have hwpos := norm_nonneg w
        nlinarith [hw.1]
      have hw2 : ‖w^2‖ < 1 := by
        rw [norm_pow]
        exact pow_lt_one₀ (norm_nonneg _) hw.2 (by decide)
      let r : ℂˣ := Units.mk0 (α*w) (mul_ne_zero hα0 hw0)
      let z : ℂˣ := Units.mk0 (w^2) (pow_ne_zero _ hw0)
      let t₀ : ℂˣ := z^3
      have ht : (t₀ : ℂ) = KPRankOneReverseRegulatorShells.t F q (r : ℂ) := by
        change (w^2)^3 = (residueCardinality (LocalField F q) : ℂ)⁻¹*(α*w)^6
        rw [mul_pow,hα,← mul_assoc,inv_mul_cancel₀ hq0,one_mul,← pow_mul]
      have hres := actual_fixed_root_shell_residue F ζ hζ q S P dx Jreg rep hrep d e
        φ hφ hcφ (p (rep e)) r t₀ z ht rfl hwA hw2 (fun ρ hcone => hp r t₀ ht ρ hcone (rep e))
      have hl := scaled_root_evaluates α w (restrictionAtOne F q (p (rep e))) hres.1
      have hr := (Evaluates.const w (φ 0 * if e=d then 1 else 0)).mul
        (rationalResidueScalar_evaluates F q dx w hw0 hw.2)
      exact hl.2.trans (hres.2.trans (by rw [hr.2]; dsimp [z]; ring))

open KPRankOneReverseRegulatorSpecialization
private theorem actual_joint_shell_Q1_standard_coefficient
    (dx : Measure (LocalField F q)) [dx.IsAddHaarMeasure]
    (Jreg : CenterStandardFamily F ζ hζ q S.heisenberg S.borel S.iwasawa dx)
    (rep : S.D → KPExceptionalRaw.actualTorus F ζ hζ q)
    (hrep : ∀ d, S.heisenberg.π (rep d) = d) (d : S.D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)
    (p : KPExceptionalRaw.actualTorus F ζ hζ q → ShellNumerator)
    (hp : ∀ (r t₀ : ℂˣ), (t₀ : ℂ) = KPRankOneReverseRegulatorShells.t F q (r : ℂ) → ∀ ρ : ℂ,
      KPJointRegulator.cone (LocalField F q) t₀ ρ → ∀ h,
      H F ζ hζ q S.heisenberg S.borel P S.iwasawa dx Jreg (S.openCell P)
        rep hrep d φ hφ hcφ r ρ h =
        evaluateNumerator (p h) r (Q F q ρ) / shellDenominator F q r (Q F q ρ))
    (r : ℂˣ) (hr : IsRegular F q r) (h : KPExceptionalRaw.actualTorus F ζ hζ q) :
    Polynomial.eval (r : ℂ) (restrictionAtOne F q (p h)).denom ≠ 0 ∧
    RatFunc.eval (RingHom.id ℂ) (r : ℂ) (restrictionAtOne F q (p h)) =
      actualDoubleCoefficient F ζ hζ q S.heisenberg S.borel P S.iwasawa dx Jreg
        (S.openCell P) rep hrep d φ hφ hcφ r h := by
  obtain ⟨p', hpfull⟩ := actual_reverse_shell_expansion F ζ hζ q S P S.iwasawa
    dx Jreg rep hrep d φ hφ hcφ
  have hp' : IsShellExpansion F ζ hζ q S.heisenberg S.borel P S.iwasawa dx Jreg
      (S.openCell P) rep hrep d φ hφ hcφ p' := by
    intro r hr ρ hρ h
    exact (hpfull r hr ρ hρ h).2
  have heq := actual_shell_rational_model_unique F ζ hζ q S P dx Jreg rep hrep d
    φ hφ hcφ p hp (fun h => rationalH F q (p' h)) (by
      intro r t₀ ht ρ hcone h
      have hr₀ : IsRegular F q r := by
        change 1-KPRankOneReverseRegulatorShells.t F q (r : ℂ) ≠ 0
        rw [← ht]
        intro he
        have hn := hcone.2.2.2
        rw [← sub_eq_zero.mp he,norm_one] at hn
        exact lt_irrefl _ hn
      have hreg : ConvergenceRegion F q r ρ := by
        refine ⟨hcone.2.1,?_⟩
        rw [← ht]
        exact hcone.2.2.1
      rw [evaluateRational_rationalH F q (p' h) r (Q F q ρ) r.ne_zero
        (Complex.exp_ne_zero _) (shellDenominator_ne_zero F q r hr₀ ρ hreg)]
      exact hp' r hr₀ ρ hreg h)
  have hrestrict : restrictionAtOne F q (p h) = restrictionAtOne F q (p' h) := by
    unfold restrictionAtOne
    rw [heq h]
  rw [hrestrict]
  exact actual_restriction_eq_double_coefficient F ζ hζ q S P
    S.iwasawa dx Jreg rep hrep d φ hφ hcφ p' hp' r hr h

end ActualShellPort

set_option backward.isDefEq.respectTransparency false in

private theorem pure_whole_from_zero_coefficients
    (S : ActualKPBinding F ζ hζ q) (P : Polarization S.heisenberg) [DecidableEq S.D]
    (dx : Measure (LocalField F q))
    (Jreg : CenterStandardFamily F ζ hζ q S.heisenberg S.borel S.iwasawa dx)
    (rep : S.D → KPExceptionalRaw.actualTorus F ζ hζ q)
    (hrep : ∀ d, S.heisenberg.π (rep d) = d)
    (r : ℂˣ) (c : ℂ)
    (hplus : denominator (LocalField F q) .plus (additiveParameter F q r) ≠ 0)
    (hminus : denominator (LocalField F q) .minus (additiveParameter F q r) ≠ 0)
    (hzero : ∀ (d : S.D) (φ : LocalField F q → ℂ)
      (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ) (e : S.D),
      ((Jreg.op .minus (additiveParameter F q r)
        (Jreg.op .plus (additiveParameter F q r)
          (actualSection F ζ hζ q S.heisenberg S.borel P (S.openCell P)
            rep hrep d φ hφ hcφ r))).val (openCoordinate F ζ hζ q 0)).val (rep e) =
        c*(φ 0*if e=d then 1 else 0))
    (d : S.D) (φ : LocalField F q → ℂ)
    (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ) :
    ∀ g : Cover F ζ hζ q,
      ((Jreg.op .minus (additiveParameter F q r)
        (Jreg.op .plus (additiveParameter F q r)
          (actualSection F ζ hζ q S.heisenberg S.borel P (S.openCell P)
            rep hrep d φ hφ hcφ r))).val g) =
        c • (actualSection F ζ hζ q S.heisenberg S.borel P (S.openCell P)
          rep hrep d φ hφ hcφ r).val g := by
  classical
  let o := Jreg.op .minus (additiveParameter F q r)
        (Jreg.op .plus (additiveParameter F q r)
          (actualSection F ζ hζ q S.heisenberg S.borel P (S.openCell P)
            rep hrep d φ hφ hcφ r))
  let a : centerSectionSpace F ζ hζ q S.heisenberg S.borel .plus (additiveParameter F q r) :=
    ⟨o.val, by simpa [targetSign,targetParameter,sourceParameter] using o.property⟩
  have ha : ∀ g, a.val g = (Jreg.op .minus (additiveParameter F q r)
        (Jreg.op .plus (additiveParameter F q r)
          (actualSection F ζ hζ q S.heisenberg S.borel P (S.openCell P)
            rep hrep d φ hφ hcφ r))).val g := by intro g; rfl
  suffices he : a = c • actualSection F ζ hζ q S.heisenberg S.borel P (S.openCell P)
      rep hrep d φ hφ hcφ r by
    intro g
    rw [← ha g,he]
    rfl
  apply actual_open_coordinate_injective F ζ hζ q S (additiveParameter F q r)
  intro x
  apply (centerCoordinates S.heisenberg rep hrep).injective
  ext e
  have hs := hzero d (fun y => φ (y+x)) (shifted_profile_lc F q φ hφ x)
    (shifted_profile_compact F q φ hcφ x) e
  rw [← actual_pure_upper_shift F ζ hζ q S P rep hrep d φ hφ hcφ r x] at hs
  have hp := Jreg.intertwining .plus _ hplus (nLift F ζ hζ q x)
    (actualSection F ζ hζ q S.heisenberg S.borel P (S.openCell P) rep hrep d φ hφ hcφ r)
  have hm := Jreg.intertwining .minus _ hminus (nLift F ζ hζ q x)
    (Jreg.op .plus (additiveParameter F q r)
      (actualSection F ζ hζ q S.heisenberg S.borel P (S.openCell P) rep hrep d φ hφ hcφ r))
  have hpv := congrArg (fun f => ((Jreg.op .minus (additiveParameter F q r) f).val
    (openCoordinate F ζ hζ q 0)).val (rep e)) hp
  have hmv := congrArg (fun f => (f.val (openCoordinate F ζ hζ q 0)).val (rep e)) hm
  have he := hpv.trans hmv
  have hxval := he.symm.trans hs
  clear hs
  have hs := hxval
  have hcoord : openCoordinate F ζ hζ q 0*nLift F ζ hζ q x = openCoordinate F ζ hζ q x := by
    simp only [openCoordinate,mul_assoc,nLift,← KPPGLLocalCover.N_add,zero_add]
  change ((Jreg.op .minus (additiveParameter F q r)
      (Jreg.op .plus (additiveParameter F q r)
        (actualSection F ζ hζ q S.heisenberg S.borel P (S.openCell P)
          rep hrep d φ hφ hcφ r))).val (openCoordinate F ζ hζ q 0*nLift F ζ hζ q x)).val (rep e) = _ at hs
  rw [hcoord,zero_add] at hs

  change _ = c * ((centerCoordinates S.heisenberg rep hrep)
    ((actualSection F ζ hζ q S.heisenberg S.borel P (S.openCell P)
      rep hrep d φ hφ hcφ r).val (openCoordinate F ζ hζ q x))) e
  rw [(actualSection_spec F ζ hζ q S.heisenberg S.borel P (S.openCell P)
    rep hrep d φ hφ hcφ r).1 x]
  change (a.val (openCoordinate F ζ hζ q x)).val (rep e) = _
  rw [ha,hs]
  simp [Pi.single_apply]

set_option backward.isDefEq.respectTransparency false in

 def actualDoubleMap
    (S : ActualKPBinding F ζ hζ q) [DecidableEq S.D]
    (dx : Measure (LocalField F q))
    (Jreg : CenterStandardFamily F ζ hζ q S.heisenberg S.borel S.iwasawa dx) (z : ℂ) :
    centerSectionSpace F ζ hζ q S.heisenberg S.borel .plus z →ₗ[ℂ]
      centerSectionSpace F ζ hζ q S.heisenberg S.borel .plus z where
  toFun a := ⟨(Jreg.op .minus z (Jreg.op .plus z a)).val,
    by simpa [targetSign,targetParameter,sourceParameter] using
      (Jreg.op .minus z (Jreg.op .plus z a)).property⟩
  map_add' a b := by apply Subtype.ext; simp only [map_add,Submodule.coe_add]
  map_smul' c a := by apply Subtype.ext; simp only [map_smul,Submodule.coe_smul]; rfl

set_option maxHeartbeats 1500000 in
set_option synthInstance.maxHeartbeats 100000 in
set_option backward.isDefEq.respectTransparency false in

private theorem compact_whole_from_pure
    (S : ActualKPBinding F ζ hζ q) (P : Polarization S.heisenberg) [DecidableEq S.D]
    (dx : Measure (LocalField F q))
    (Jreg : CenterStandardFamily F ζ hζ q S.heisenberg S.borel S.iwasawa dx)
    (rep : S.D → KPExceptionalRaw.actualTorus F ζ hζ q)
    (hrep : ∀ d, S.heisenberg.π (rep d) = d)
    (r : ℂˣ) (c : ℂ)
    (hplus : denominator (LocalField F q) .plus (additiveParameter F q r) ≠ 0)
    (hminus : denominator (LocalField F q) .minus (additiveParameter F q r) ≠ 0)
    (hpure : ∀ (d : S.D) (φ : LocalField F q → ℂ)
      (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ),
      actualDoubleMap F ζ hζ q S dx Jreg (additiveParameter F q r)
        (actualSection F ζ hζ q S.heisenberg S.borel P (S.openCell P)
          rep hrep d φ hφ hcφ r) =
      c • actualSection F ζ hζ q S.heisenberg S.borel P (S.openCell P)
        rep hrep d φ hφ hcφ r)
    (J : CompactOpenLevel (Cover F ζ hζ q))
    (hJ : J.toOpenSubgroup ≤ S.iwasawa.compact.toOpenSubgroup)
    (f : centerCompactLevel F ζ hζ q S.heisenberg S.borel S.iwasawa .plus J) :
    actualDoubleMap F ζ hζ q S dx Jreg (additiveParameter F q r)
      (centerCompactTrivialization F ζ hζ q S.heisenberg S.borel S.iwasawa .plus
        (additiveParameter F q r) f.val) =
    c • centerCompactTrivialization F ζ hζ q S.heisenberg S.borel S.iwasawa .plus
      (additiveParameter F q r) f.val := by
  classical
  obtain ⟨N,g,d,φ,hφ,hcφ,J₀,L,hL,hJ₀,hconj,ha₀,ha₁,hf⟩ :=
    KPActualResidueSources.actual_center_compact_translated_pure_spanning F ζ hζ q S P J hJ rep hrep r f
  let C := centerCompactTrivialization F ζ hζ q S.heisenberg S.borel S.iwasawa .plus
    (additiveParameter F q r)
  have hs : C f.val = ∑ i : Fin N,
      centerPrincipalSeries F ζ hζ q S.heisenberg S.borel .plus (additiveParameter F q r)
        (g i) (actualSection F ζ hζ q S.heisenberg S.borel P (S.openCell P)
          rep hrep (d i) (φ i) (hφ i) (hcφ i) r) := by
    have h := congrArg C hf
    rw [map_sum] at h
    simpa only [C,LinearEquiv.apply_symm_apply] using h
  change actualDoubleMap F ζ hζ q S dx Jreg (additiveParameter F q r) (C f.val) = c • C f.val
  rw [hs,map_sum,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hp := Jreg.intertwining .plus _ hplus (g i)
    (actualSection F ζ hζ q S.heisenberg S.borel P (S.openCell P)
      rep hrep (d i) (φ i) (hφ i) (hcφ i) r)
  have hm := Jreg.intertwining .minus _ hminus (g i)
    (Jreg.op .plus (additiveParameter F q r)
      (actualSection F ζ hζ q S.heisenberg S.borel P (S.openCell P)
        rep hrep (d i) (φ i) (hφ i) (hcφ i) r))
  apply Subtype.ext
  funext x
  change (Jreg.op .minus (additiveParameter F q r)
    (Jreg.op .plus (additiveParameter F q r) _)).val x = _
  have hpv := congrArg (fun a => (Jreg.op .minus (additiveParameter F q r) a).val x) hp
  have hmv := congrArg (fun a => a.val x) hm
  have he := congrArg (fun a => a.val (x*g i)) (hpure (d i) (φ i) (hφ i) (hcφ i))
  exact (hpv.trans hmv).trans he

open scoped TensorProduct

private theorem scalar_of_tensor_identity
    {V W : Type*} [AddCommMonoid V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [Nontrivial W]
    (M : V →ₗ[ℂ] V) (c : ℂ)
    (hM : TensorProduct.map M (LinearMap.id : W →ₗ[ℂ] W) = c • LinearMap.id) :
    M = c • LinearMap.id := by
  obtain ⟨w,hw⟩ := exists_ne (0 : W)
  obtain ⟨ℓ,hℓ⟩ := Module.Projective.exists_dual_eq_one ℂ hw
  let E : V ⊗[ℂ] W →ₗ[ℂ] V := (TensorProduct.rid ℂ V).toLinearMap.comp
    (TensorProduct.map LinearMap.id ℓ)
  ext v
  have h := congrArg (fun N : V ⊗[ℂ] W →ₗ[ℂ] V ⊗[ℂ] W => E (N (v ⊗ₜ[ℂ] w))) hM
  simp only [E,LinearMap.comp_apply,TensorProduct.map_tmul,LinearMap.id_apply,
    LinearMap.smul_apply,map_smul,hℓ] at h
  simpa only [LinearEquiv.coe_coe,TensorProduct.rid_tmul,one_smul,
    LinearMap.smul_apply,LinearMap.id_apply] using h

private theorem residue_regular_locus_infinite
    (dx : Measure (LocalField F q)) :
    {w : ℂ | w ≠ 0 ∧ w^6 ≠ 1 ∧
      (rationalResidueScalar (LocalField F q) dx).denom.eval w ≠ 0}.Infinite := by
  let bad : Set ℂ := {0} ∪ {w | w^6=1} ∪
    {w | (rationalResidueScalar (LocalField F q) dx).denom.IsRoot w}
  have hp : (Polynomial.X^6-1 : Polynomial ℂ) ≠ 0 := by
    intro he
    have hv := congrArg (Polynomial.eval (0 : ℂ)) he
    norm_num at hv
  have hroots : {w : ℂ | w^6=1}.Finite := by
    convert Polynomial.finite_setOfPred_isRoot hp using 1
    ext w
    simp [Polynomial.IsRoot,sub_eq_zero]
  have hb : bad.Finite := ((Set.finite_singleton 0).union hroots).union
    (Polynomial.finite_setOfPred_isRoot (RatFunc.denom_ne_zero _))
  have hi := Set.infinite_univ.sdiff hb
  apply hi.mono
  intro w hw
  rcases hw with ⟨_,hw⟩
  exact ⟨fun h => hw (Or.inl (Or.inl h)),
    fun h => hw (Or.inl (Or.inr h)),fun h => hw (Or.inr h)⟩

private theorem both_standard_denominators_regular
    (α w : ℂ) (hα : α^6=(residueCardinality (LocalField F q) : ℂ))
    (hw0 : w ≠ 0) (hw6 : w^6 ≠ 1) :
    ∃ r₀ : ℂˣ, (r₀ : ℂ)=α*w ∧
      denominator (LocalField F q) .plus (additiveParameter F q r₀) ≠ 0 ∧
      denominator (LocalField F q) .minus (additiveParameter F q r₀) ≠ 0 := by
  have hq0 : (residueCardinality (LocalField F q) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := IsLocalRing.ResidueField
      (Valuation.integer (valuation (LocalField F q))))).ne'
  have hα0 : α ≠ 0 := by
    intro he
    rw [he,zero_pow (by decide)] at hα
    exact hq0 hα.symm
  let r₀ := Units.mk0 (α*w) (mul_ne_zero hα0 hw0)
  have hroot := root_parameter_additiveParameter F q r₀
  have h6 : (r₀ : ℂ)^6 = (residueCardinality (LocalField F q) : ℂ)*w^6 := by
    change (α*w)^6 = _
    rw [mul_pow,hα]
  have h6ne : (r₀ : ℂ)^6 ≠ (residueCardinality (LocalField F q) : ℂ) := by
    rw [h6]
    intro he
    exact hw6 ((mul_left_cancel₀ hq0) (by simpa using he))
  refine ⟨r₀,rfl,?_,?_⟩
  · simp only [denominator,ite_true, KPRankOneRootParameter.t,hroot]
    apply sub_ne_zero.mpr
    intro he
    apply h6ne
    exact ((inv_mul_eq_one₀ hq0).mp he.symm).symm
  · simp only [denominator,show Sign.minus ≠ Sign.plus from by decide,ite_false,hroot]
    apply sub_ne_zero.mpr
    intro he
    apply h6ne
    have he' : (residueCardinality (LocalField F q) : ℂ)*((r₀ : ℂ)^6)⁻¹ = 1 := by
      simpa only [inv_pow] using he.symm
    exact ((mul_inv_eq_one₀ (pow_ne_zero _ r₀.ne_zero)).mp he').symm

private theorem scalar_composition_of_center_transport
    {Vp Vm W Cp Cm : Type*}
    [AddCommMonoid Vp] [Module ℂ Vp] [AddCommMonoid Vm] [Module ℂ Vm]
    [AddCommGroup W] [Module ℂ W] [Nontrivial W]
    [AddCommMonoid Cp] [Module ℂ Cp] [AddCommMonoid Cm] [Module ℂ Cm]
    (ep : Vp ⊗[ℂ] W ≃ₗ[ℂ] Cp) (em : Vm ⊗[ℂ] W ≃ₗ[ℂ] Cm)
    (A : Vp →ₗ[ℂ] Vm) (B : Vm →ₗ[ℂ] Vp) (c : ℂ)
    (hc : (ep.toLinearMap.comp ((TensorProduct.map B LinearMap.id).comp em.symm.toLinearMap)).comp
      (em.toLinearMap.comp ((TensorProduct.map A LinearMap.id).comp ep.symm.toLinearMap)) =
        c • LinearMap.id) : B.comp A = c • LinearMap.id := by
  apply scalar_of_tensor_identity (W := W) (B.comp A) c
  apply LinearMap.ext
  intro t
  have h := congrArg (fun M => ep.symm (M (ep t))) hc
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply,
    LinearMap.smul_apply,LinearMap.id_apply,map_smul] at h
  change ((TensorProduct.map B LinearMap.id).comp (TensorProduct.map A LinearMap.id)) t = _ at h
  rw [← TensorProduct.map_comp] at h
  simpa only [LinearMap.id_comp,LinearMap.comp_apply,LinearMap.smul_apply,
    LinearMap.id_apply] using h

set_option maxHeartbeats 1500000 in
set_option backward.isDefEq.respectTransparency false in

private theorem continued_scalar_from_compact_whole
    (S : ActualKPBinding F ζ hζ q) (P : Polarization S.heisenberg) [DecidableEq S.D]
    (dx : Measure (LocalField F q))
    (Jτ : TauStandardFamily F ζ hζ q S.heisenberg S.borel P S.iwasawa dx)
    (Jreg : CenterStandardFamily F ζ hζ q S.heisenberg S.borel S.iwasawa dx)
    (J : CompactOpenLevel (Cover F ζ hζ q))
    (p : LevelLaurentOperator (LocalField F q) S.borel P S.iwasawa J .plus)
    (pRev : LevelLaurentOperator (LocalField F q) S.borel P S.iwasawa J .minus)
    (hp : IsLevelNumerator (LocalField F q) S.borel P S.iwasawa J dx .plus p)
    (hpRev : IsLevelNumerator (LocalField F q) S.borel P S.iwasawa J dx .minus pRev)
    (z c : ℂ)
    (hplus : denominator (LocalField F q) .plus z ≠ 0)
    (hminus : denominator (LocalField F q) .minus z ≠ 0)
    (hwhole : ∀ f : centerCompactLevel F ζ hζ q S.heisenberg S.borel S.iwasawa .plus J,
      actualDoubleMap F ζ hζ q S dx Jreg z
        (centerCompactTrivialization F ζ hζ q S.heisenberg S.borel S.iwasawa .plus z f.val) =
      c • centerCompactTrivialization F ζ hζ q S.heisenberg S.borel S.iwasawa .plus z f.val) :
    (continuedLevel (LocalField F q) S.borel P S.iwasawa J .minus pRev z).comp
      (continuedLevel (LocalField F q) S.borel P S.iwasawa J .plus p z) =
        c • LinearMap.id := by
  classical
  let cp : centerCompactLevel F ζ hζ q S.heisenberg S.borel S.iwasawa .plus J →ₗ[ℂ]
      centerCompactLevel F ζ hζ q S.heisenberg S.borel S.iwasawa .minus J := centerContinuedLevel F ζ hζ q S.heisenberg S.borel S.iwasawa J .plus
    (centerLevelLaurentTransport F ζ hζ q S.heisenberg S.borel P S.iwasawa J .plus p) z
  let cm : centerCompactLevel F ζ hζ q S.heisenberg S.borel S.iwasawa .minus J →ₗ[ℂ]
      centerCompactLevel F ζ hζ q S.heisenberg S.borel S.iwasawa .plus J := centerContinuedLevel F ζ hζ q S.heisenberg S.borel S.iwasawa J .minus
    (centerLevelLaurentTransport F ζ hζ q S.heisenberg S.borel P S.iwasawa J .minus pRev) z
  have hpC := centerLevelLaurentTransport_isNumerator F ζ hζ q S.heisenberg S.borel P
    S.iwasawa J dx Jτ .plus p hp
  have hmC := centerLevelLaurentTransport_isNumerator F ζ hζ q S.heisenberg S.borel P
    S.iwasawa J dx Jτ .minus pRev hpRev
  have hc : cm.comp cp = c • LinearMap.id := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply (centerCompactTrivialization F ζ hζ q S.heisenberg S.borel S.iwasawa .plus z).injective
    have hs := Jreg.shell_eq J .plus _ hpC z hplus f
    have ht := Jreg.shell_eq J .minus _ hmC z hminus (cp f)
    have h := congrArg (fun a => a.val) (hwhole f)
    apply Subtype.ext
    change (centerCompactTrivialization F ζ hζ q S.heisenberg S.borel S.iwasawa .plus z
      (cm (cp f)).val).val = _
    change (Jreg.op .minus z (Jreg.op .plus z _)).val = _ at h
    change Jreg.op .plus z
      (centerCompactTrivialization F ζ hζ q S.heisenberg S.borel S.iwasawa .plus z f.val) =
      centerCompactTrivialization F ζ hζ q S.heisenberg S.borel S.iwasawa .minus (-z)
        (cp f).val at hs
    rw [hs] at h
    change (Jreg.op .minus z
      (centerCompactTrivialization F ζ hζ q S.heisenberg S.borel S.iwasawa .minus (-z)
        (cp f).val)).val = _ at h
    have htv := congrArg (fun a => a.val) ht
    have h := htv.symm.trans h
    have hh : (centerCompactTrivialization F ζ hζ q S.heisenberg S.borel S.iwasawa .plus z
        (cm (cp f)).val).val =
      (c • centerCompactTrivialization F ζ hζ q S.heisenberg S.borel S.iwasawa .plus z f.val).val := by
      funext g
      have hg := congrFun h g
      simpa [centerCompactTrivialization,sourceSign,targetSign,sourceParameter,targetParameter,cm] using hg
    change _ = (centerCompactTrivialization F ζ hζ q S.heisenberg S.borel S.iwasawa .plus z
      (c • f.val)).val
    rw [map_smul]
    exact hh
  haveI : Nontrivial (InducedModule P) := by
    apply Module.nontrivial_of_finrank_pos (R := ℂ)
    rw [tau_finrank_eq_index S.heisenberg P]
    exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  letI : Nontrivial (Multiplicity S.heisenberg P) := inferInstance
  dsimp only [sourceSign,targetSign] at p pRev ⊢
  refine scalar_composition_of_center_transport
    (Vp := compactLevel S.borel P S.iwasawa .plus J)
    (Vm := compactLevel S.borel P S.iwasawa .minus J) (W := Multiplicity S.heisenberg P)
    (centerLevelTensorEquiv F ζ hζ q S.heisenberg S.borel P S.iwasawa .plus J)
    (centerLevelTensorEquiv F ζ hζ q S.heisenberg S.borel P S.iwasawa .minus J)
    (continuedLevel (LocalField F q) S.borel P S.iwasawa J .plus p z)
    (continuedLevel (LocalField F q) S.borel P S.iwasawa J .minus pRev z) c ?_
  change (centerLevelOperatorTransport F ζ hζ q S.heisenberg S.borel P S.iwasawa J .minus
    (continuedLevel (LocalField F q) S.borel P S.iwasawa J .minus pRev z)).comp
    (centerLevelOperatorTransport F ζ hζ q S.heisenberg S.borel P S.iwasawa J .plus
      (continuedLevel (LocalField F q) S.borel P S.iwasawa J .plus p z)) = _
  simpa only [cp,cm,centerLevelLaurentTransport_continued] using hc

private theorem rational_eq_of_regular_infinite
    (R T : RatFunc ℂ) (u : Set ℂ) (hu : u.Infinite)
    (he : ∀ w ∈ u, R.denom.eval w ≠ 0 ∧ T.denom.eval w ≠ 0 ∧
      RatFunc.eval (RingHom.id ℂ) w R = RatFunc.eval (RingHom.id ℂ) w T) : R=T := by
  have hp : R.num*T.denom=T.num*R.denom := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply hu.mono
    intro w hw
    obtain ⟨hR,hT,h⟩ := he w hw
    simp only [RatFunc.eval,Polynomial.eval₂_id] at h
    change Polynomial.eval w (R.num*T.denom) = Polynomial.eval w (T.num*R.denom)
    simpa only [Polynomial.eval_mul] using (div_eq_div_iff hR hT).mp h
  have hh := (RatFunc.num_mul_eq_mul_denom_iff (RatFunc.denom_ne_zero T)).mp hp
  rwa [RatFunc.num_div_denom] at hh

private lemma scalar_regular (c : ℂ) (R : RatFunc ℂ) (w : ℂ)
    (hR : R.denom.eval w ≠ 0) :
    (c • R).denom.eval w ≠ 0 ∧
      RatFunc.eval (RingHom.id ℂ) w (c • R) = c * RatFunc.eval (RingHom.id ℂ) w R := by
  rw [RatFunc.smul_eq_C_mul]
  refine ⟨?_, by rw [RatFunc.eval_mul _ _ (by simp) hR, RatFunc.eval_C]; rfl⟩
  intro h
  have hh := Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (RatFunc.denom_mul_dvd (RatFunc.C c) R) h
  exact hR (by simpa using hh)
private lemma sum_regular {ι : Type*} (s : Finset ι) (a : ι → RatFunc ℂ) (w : ℂ)
    (ha : ∀ i ∈ s, (a i).denom.eval w ≠ 0) :
    (∑ i ∈ s, a i).denom.eval w ≠ 0 ∧
      RatFunc.eval (RingHom.id ℂ) w (∑ i ∈ s, a i) =
        ∑ i ∈ s, RatFunc.eval (RingHom.id ℂ) w (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    obtain ⟨hs,es⟩ := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
    have hiR := ha i (Finset.mem_insert_self _ _)
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    refine ⟨?_, by rw [RatFunc.eval_add _ _ hiR hs,es]⟩
    intro h
    apply mul_ne_zero hiR hs
    simpa only [Polynomial.eval_mul] using
      Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (RatFunc.denom_add_dvd (a i) (∑ j ∈ s,a j)) h

set_option maxHeartbeats 800000 in

private theorem rational_sum_scalar {ι V : Type*} [AddCommMonoid V] [Module ℂ V]
    (s : Finset ι) (a : ι → RatFunc ℂ) (M : ι → Module.End ℂ V) (c : RatFunc ℂ)
    (U : Set ℂ) (hU : U.Infinite)
    (ha : ∀ w ∈ U, ∀ i ∈ s, (a i).denom.eval w ≠ 0)
    (hc : ∀ w ∈ U, c.denom.eval w ≠ 0)
    (hn : ∀ w ∈ U, (∑ i ∈ s, RatFunc.eval (RingHom.id ℂ) w (a i) • M i) =
      RatFunc.eval (RingHom.id ℂ) w c • LinearMap.id) :
    (∑ i ∈ s, a i • (M i).baseChange (RatFunc ℂ)) = c • LinearMap.id := by
  classical
  letI : AddCommGroup V := Module.addCommMonoidToAddCommGroup ℂ
  let b := Module.Free.chooseBasis ℂ V
  let e := TensorProduct.equivFinsuppOfBasisRight (M := RatFunc ℂ) b
  apply TensorProduct.AlgebraTensorModule.ext
  intro f v
  suffices h : (∑ i ∈ s, a i • (M i).baseChange (RatFunc ℂ)) (1 ⊗ₜ[ℂ] v) =
      (c • LinearMap.id) (1 ⊗ₜ[ℂ] v) by
    calc
      _ = f • (∑ i ∈ s, a i • (M i).baseChange (RatFunc ℂ)) (1 ⊗ₜ[ℂ] v) := by
        rw [← map_smul,TensorProduct.smul_tmul',smul_eq_mul,mul_one]
      _ = f • (c • LinearMap.id) (1 ⊗ₜ[ℂ] v) := congrArg (fun x => f • x) h
      _ = _ := by rw [← map_smul,TensorProduct.smul_tmul',smul_eq_mul,mul_one]
  apply e.injective
  ext j
  change (e ((∑ i ∈ s, a i • (M i).baseChange (RatFunc ℂ)) (1 ⊗ₜ[ℂ] v))) j =
    (e ((c • LinearMap.id) (1 ⊗ₜ[ℂ] v))) j
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.baseChange_tmul,
    TensorProduct.smul_tmul', smul_eq_mul,mul_one, map_sum, LinearMap.id_apply,
    Finsupp.finsetSum_apply,TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
  dsimp only [e]
  simp only [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
  apply rational_eq_of_regular_infinite _ _ U hU
  intro w hw
  have hs := sum_regular s (fun i => (b.repr (M i v)) j • a i) w
    (fun i hi => (scalar_regular _ _ _ (ha w hw i hi)).1)
  have ht := scalar_regular ((b.repr v) j) c w (hc w hw)
  refine ⟨hs.1,ht.1,?_⟩
  rw [hs.2,ht.2]
  have hev : (∑ i ∈ s, RatFunc.eval (RingHom.id ℂ) w ((b.repr (M i v)) j • a i)) =
      ∑ i ∈ s, (b.repr (M i v)) j * RatFunc.eval (RingHom.id ℂ) w (a i) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact (scalar_regular _ _ _ (ha w hw i hi)).2
  rw [hev]
  have hh := congrArg (fun L : Module.End ℂ V => (b.repr (L v)) j) (hn w hw)
  simpa only [LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.id_apply,map_sum,map_smul,
    Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul,mul_comm] using hh

private lemma product_regular (a b : RatFunc ℂ) (w : ℂ)
    (ha : a.denom.eval w ≠ 0) (hb : b.denom.eval w ≠ 0) :
    (a*b).denom.eval w ≠ 0 := by
  intro h
  apply mul_ne_zero ha hb
  simpa only [Polynomial.eval_mul] using
    Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (RatFunc.denom_mul_dvd a b) h

private theorem rational_rectangular_composition {ι κ V W : Type*}
    [AddCommMonoid V] [Module ℂ V] [AddCommMonoid W] [Module ℂ W]
    (s : Finset ι) (t : Finset κ) (a : ι → RatFunc ℂ) (b : κ → RatFunc ℂ)
    (A : ι → V →ₗ[ℂ] W) (B : κ → W →ₗ[ℂ] V) (c : RatFunc ℂ)
    (U : Set ℂ) (hU : U.Infinite)
    (ha : ∀ w ∈ U, ∀ i ∈ s, (a i).denom.eval w ≠ 0)
    (hb : ∀ w ∈ U, ∀ j ∈ t, (b j).denom.eval w ≠ 0)
    (hc : ∀ w ∈ U, c.denom.eval w ≠ 0)
    (hn : ∀ w ∈ U,
      (∑ j ∈ t, RatFunc.eval (RingHom.id ℂ) w (b j) • B j).comp
        (∑ i ∈ s, RatFunc.eval (RingHom.id ℂ) w (a i) • A i) =
      RatFunc.eval (RingHom.id ℂ) w c • LinearMap.id) :
    (∑ j ∈ t, b j • (B j).baseChange (RatFunc ℂ)).comp
      (∑ i ∈ s, a i • (A i).baseChange (RatFunc ℂ)) = c • LinearMap.id := by
  classical
  have hh := rational_sum_scalar (t ×ˢ s) (fun ji => b ji.1 * a ji.2)
    (fun ji => (B ji.1).comp (A ji.2)) c U hU
    (fun w hw ji hji => product_regular _ _ w
      (hb w hw ji.1 (Finset.mem_product.mp hji).1)
      (ha w hw ji.2 (Finset.mem_product.mp hji).2)) hc ?_
  · apply LinearMap.ext
    intro v
    have hhv := LinearMap.congr_fun hh v
    simp only [Finset.sum_product,LinearMap.comp_apply,LinearMap.sum_apply,
      LinearMap.smul_apply,LinearMap.id_apply,map_sum,map_smul,Finset.smul_sum,
      smul_smul,LinearMap.baseChange_comp] at hhv ⊢
    rw [Finset.sum_comm]
    simpa only [mul_comm] using hhv
  · intro w hw
    have he (ji : κ × ι) (hji : ji ∈ t ×ˢ s) :
        RatFunc.eval (RingHom.id ℂ) w (b ji.1 * a ji.2) =
          RatFunc.eval (RingHom.id ℂ) w (b ji.1) * RatFunc.eval (RingHom.id ℂ) w (a ji.2) :=
      RatFunc.eval_mul _ _ (hb w hw ji.1 (Finset.mem_product.mp hji).1)
        (ha w hw ji.2 (Finset.mem_product.mp hji).2)
    rw [Finset.sum_congr rfl (fun ji hji => congrArg (fun z => z • ((B ji.1).comp (A ji.2))) (he ji hji))]
    apply LinearMap.ext
    intro v
    have hhv := LinearMap.congr_fun (hn w hw) v
    simp only [Finset.sum_product,LinearMap.comp_apply,LinearMap.sum_apply,
      LinearMap.smul_apply,LinearMap.id_apply,map_sum,map_smul,Finset.smul_sum,
      smul_smul] at hhv ⊢
    rw [Finset.sum_comm]
    simpa only [mul_comm] using hhv

 def Numeric (w : ℂ) (R : RatFunc ℂ) (c : ℂ) : Prop :=
  R.denom.eval w ≠ 0 ∧ RatFunc.eval (RingHom.id ℂ) w R = c
private lemma numeric_const (w c : ℂ) : Numeric w (RatFunc.C c) c := by simp [Numeric]
private lemma numeric_X (w : ℂ) : Numeric w RatFunc.X w := by simp [Numeric]
private lemma numeric_mul {w a b : ℂ} {A B : RatFunc ℂ}
    (ha : Numeric w A a) (hb : Numeric w B b) : Numeric w (A*B) (a*b) := by
  refine ⟨?_, by rw [RatFunc.eval_mul _ _ ha.1 hb.1,ha.2,hb.2]⟩
  intro h
  apply mul_ne_zero ha.1 hb.1
  simpa using Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (RatFunc.denom_mul_dvd A B) h
private lemma numeric_add {w a b : ℂ} {A B : RatFunc ℂ}
    (ha : Numeric w A a) (hb : Numeric w B b) : Numeric w (A+B) (a+b) := by
  refine ⟨?_, by rw [RatFunc.eval_add _ _ ha.1 hb.1,ha.2,hb.2]⟩
  intro h
  apply mul_ne_zero ha.1 hb.1
  simpa using Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (RatFunc.denom_add_dvd A B) h
private lemma numeric_sub {w a b : ℂ} {A B : RatFunc ℂ}
    (ha : Numeric w A a) (hb : Numeric w B b) : Numeric w (A-B) (a-b) := by
  simpa [sub_eq_add_neg] using numeric_add ha (numeric_mul (numeric_const w (-1)) hb)
private lemma numeric_inv {w a : ℂ} {A : RatFunc ℂ}
    (ha : Numeric w A a) (ha0 : a ≠ 0) : Numeric w A⁻¹ a⁻¹ := by
  have hA0 : A ≠ 0 := by intro h; subst A; simp [Numeric] at ha; exact ha0 ha.symm
  have hi : A⁻¹.denom.eval w ≠ 0 := by
    intro h
    have hn := Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (RatFunc.denom_inv_dvd hA0) h
    apply ha0
    rw [← ha.2,RatFunc.eval,Polynomial.eval₂_id,hn,zero_div]
  refine ⟨hi,?_⟩
  have he := RatFunc.eval_mul (RingHom.id ℂ) w ha.1 hi
  rw [mul_inv_cancel₀ hA0,RatFunc.eval_one,ha.2] at he
  exact eq_inv_of_mul_eq_one_right he.symm
private lemma numeric_pow {w a : ℂ} {A : RatFunc ℂ}
    (ha : Numeric w A a) (n : ℕ) : Numeric w (A^n) (a^n) := by
  induction n with
  | zero => simpa using numeric_const w 1
  | succ n hn => simpa [pow_succ] using numeric_mul hn ha
private lemma numeric_zpow {w a : ℂ} {A : RatFunc ℂ}
    (ha : Numeric w A a) (ha0 : a ≠ 0) (n : ℤ) : Numeric w (A^n) (a^n) := by
  cases n with
  | ofNat n => simpa using numeric_pow ha n
  | negSucc n => simpa [zpow_negSucc,← inv_pow] using numeric_pow (numeric_inv ha ha0) (n+1)
private theorem actual_rational_coefficient_numeric
    (α w : ℂ) (r₀ : ℂˣ) (hr₀ : (r₀ : ℂ) = α*w)
    (ε : Sign) (hd : denominator (LocalField F q) ε (additiveParameter F q r₀) ≠ 0)
    (n : ℤ) :
    Numeric w
      ((rationalDenominator (LocalField F q) ε (RatFunc.C α*RatFunc.X))⁻¹ *
        (if ε = .plus then RatFunc.C α*RatFunc.X else (RatFunc.C α*RatFunc.X)⁻¹)^n)
      ((denominator (LocalField F q) ε (additiveParameter F q r₀))⁻¹ *
        (evaluationUnit (LocalField F q) ε (additiveParameter F q r₀) : ℂ)^n) := by
  have hv : Numeric w (RatFunc.C α*RatFunc.X) (r₀ : ℂ) := by
    rw [hr₀]; exact numeric_mul (numeric_const w α) (numeric_X w)
  have hi := numeric_inv hv r₀.ne_zero
  have hroot := root_parameter_additiveParameter F q r₀
  have hdv : Numeric w (rationalDenominator (LocalField F q) ε (RatFunc.C α*RatFunc.X))
      (denominator (LocalField F q) ε (additiveParameter F q r₀)) := by
    cases ε
    · simpa only [KPRankOneGenericComposition.rationalDenominator,map_one,denominator,ite_true,KPRankOneRootParameter.t,hroot] using
        numeric_sub (numeric_const w 1)
          (numeric_mul (numeric_const w (residueCardinality (LocalField F q) : ℂ)⁻¹) (numeric_pow hv 6))
    · simpa only [KPRankOneGenericComposition.rationalDenominator,map_one,denominator,show Sign.minus ≠ Sign.plus from by decide,ite_false,hroot] using
        numeric_sub (numeric_const w 1)
          (numeric_mul (numeric_const w (residueCardinality (LocalField F q) : ℂ)) (numeric_pow hi 6))
  apply numeric_mul (numeric_inv hdv hd)
  have hunit : (evaluationUnit (LocalField F q) ε (additiveParameter F q r₀) : ℂ) =
      if ε = .plus then (r₀ : ℂ) else (r₀ : ℂ)⁻¹ := by
    cases ε <;> simp [evaluationUnit,rUnit,hroot]
  rw [hunit]
  cases ε
  · simpa using numeric_zpow hv r₀.ne_zero n
  · simpa using numeric_zpow hi (inv_ne_zero r₀.ne_zero) n

set_option maxHeartbeats 1500000 in
set_option backward.isDefEq.respectTransparency false in

private theorem rational_from_continued
    (S : ActualKPBinding F ζ hζ q) (P : Polarization S.heisenberg)
    (dx : Measure (LocalField F q))
    (α : ℂ) (hα : α^6=(residueCardinality (LocalField F q) : ℂ))
    (J : CompactOpenLevel (Cover F ζ hζ q))
    (p : LevelLaurentOperator (LocalField F q) S.borel P S.iwasawa J .plus)
    (pRev : LevelLaurentOperator (LocalField F q) S.borel P S.iwasawa J .minus)
    (hn : ∀ w : ℂ, w ≠ 0 → w^6 ≠ 1 →
      (rationalResidueScalar (LocalField F q) dx).denom.eval w ≠ 0 →
      ∀ r₀ : ℂˣ, (r₀ : ℂ)=α*w →
      (continuedLevel (LocalField F q) S.borel P S.iwasawa J .minus pRev
        (additiveParameter F q r₀)).comp
      (continuedLevel (LocalField F q) S.borel P S.iwasawa J .plus p
        (additiveParameter F q r₀)) =
      RatFunc.eval (RingHom.id ℂ) w (rationalResidueScalar (LocalField F q) dx) • LinearMap.id) :
    (rationalStandard (LocalField F q) S.borel P S.iwasawa J .minus pRev
      (RatFunc.C α * RatFunc.X)).comp
    (rationalStandard (LocalField F q) S.borel P S.iwasawa J .plus p
      (RatFunc.C α * RatFunc.X)) =
    rationalResidueScalar (LocalField F q) dx • LinearMap.id := by
  classical
  let v : RatFunc ℂ := RatFunc.C α*RatFunc.X
  let a : ℤ → RatFunc ℂ := fun n =>
    (KPRankOneGenericComposition.rationalDenominator (LocalField F q) .plus v)⁻¹ * v^n
  let b : ℤ → RatFunc ℂ := fun n =>
    (KPRankOneGenericComposition.rationalDenominator (LocalField F q) .minus v)⁻¹ * v⁻¹^n
  let U : Set ℂ := {w | w ≠ 0 ∧ w^6 ≠ 1 ∧
    (rationalResidueScalar (LocalField F q) dx).denom.eval w ≠ 0}
  have hr (w : ℂ) (hw : w ∈ U) := both_standard_denominators_regular F q α w hα hw.1 hw.2.1
  have ha : ∀ w ∈ U, ∀ n ∈ p.support, (a n).denom.eval w ≠ 0 := by
    intro w hw n _
    obtain ⟨r₀,he,hp,hm⟩ := hr w hw
    exact (actual_rational_coefficient_numeric F q α w r₀ he .plus hp n).1
  have hb : ∀ w ∈ U, ∀ n ∈ pRev.support, (b n).denom.eval w ≠ 0 := by
    intro w hw n _
    obtain ⟨r₀,he,hp,hm⟩ := hr w hw
    exact (actual_rational_coefficient_numeric F q α w r₀ he .minus hm n).1
  have hh := rational_rectangular_composition p.support pRev.support a b p pRev
    (rationalResidueScalar (LocalField F q) dx) U (residue_regular_locus_infinite F q dx)
    ha hb (fun _ hw => hw.2.2) ?_
  · simpa only [rationalStandard,Finsupp.sum,Finset.smul_sum,smul_smul,
      ite_true,ite_eq_right (show Sign.minus ≠ Sign.plus from by decide)] using hh
  · intro w hw
    obtain ⟨r₀,he,hp,hm⟩ := hr w hw
    have ea (n : ℤ) : RatFunc.eval (RingHom.id ℂ) w (a n) =
        (denominator (LocalField F q) .plus (additiveParameter F q r₀))⁻¹ *
          (evaluationUnit (LocalField F q) .plus (additiveParameter F q r₀) : ℂ)^n :=
      (actual_rational_coefficient_numeric F q α w r₀ he .plus hp n).2
    have eb (n : ℤ) : RatFunc.eval (RingHom.id ℂ) w (b n) =
        (denominator (LocalField F q) .minus (additiveParameter F q r₀))⁻¹ *
          (evaluationUnit (LocalField F q) .minus (additiveParameter F q r₀) : ℂ)^n :=
      (actual_rational_coefficient_numeric F q α w r₀ he .minus hm n).2
    have ep : (∑ n ∈ p.support, RatFunc.eval (RingHom.id ℂ) w (a n) • p n) =
        continuedLevel (LocalField F q) S.borel P S.iwasawa J .plus p
          (additiveParameter F q r₀) := by
      simp only [ea,continuedLevel,evaluate,Finsupp.sum,Finset.smul_sum,smul_smul]
    have em : (∑ n ∈ pRev.support, RatFunc.eval (RingHom.id ℂ) w (b n) • pRev n) =
        continuedLevel (LocalField F q) S.borel P S.iwasawa J .minus pRev
          (additiveParameter F q r₀) := by
      simp only [eb,continuedLevel,evaluate,Finsupp.sum,Finset.smul_sum,smul_smul]
    rw [ep,em]
    exact hn w hw.1 hw.2.1 hw.2.2 r₀ he

private lemma numeric_polynomial (p : Polynomial ℂ) (w : ℂ) :
    Numeric w (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) (p.eval w) := by
  refine ⟨by simp, ?_⟩
  simp [RatFunc.eval, RatFunc.num_algebraMap, Polynomial.eval₂_id]

private lemma numeric_scaled_root (α w : ℂ) (R : RatFunc ℂ)
    (hR : R.denom.eval (α*w) ≠ 0) :
    Numeric w (RatFunc.eval (RatFunc.C : ℂ →+* RatFunc ℂ) (RatFunc.C α*RatFunc.X) R)
      (RatFunc.eval (RingHom.id ℂ) (α*w) R) := by
  have he (p : Polynomial ℂ) :
      p.eval₂ (RatFunc.C : ℂ →+* RatFunc ℂ) (RatFunc.C α*RatFunc.X) =
      algebraMap (Polynomial ℂ) (RatFunc ℂ) (p.comp (Polynomial.C α*Polynomial.X)) := by
    rw [← RatFunc.aeval_X_left_eq_algebraMap]
    simp only [Polynomial.aeval_def,RatFunc.algebraMap_eq_C,Polynomial.eval₂_comp,
      Polynomial.eval₂_mul,Polynomial.eval₂_C,Polynomial.eval₂_X]
  rw [RatFunc.eval,he,he,div_eq_mul_inv]
  have hn := numeric_polynomial (R.num.comp (Polynomial.C α*Polynomial.X)) w
  have hd := numeric_polynomial (R.denom.comp (Polynomial.C α*Polynomial.X)) w
  have hdn : (R.denom.comp (Polynomial.C α*Polynomial.X)).eval w ≠ 0 := by
    simpa only [Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X] using hR
  simpa only [Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_X,RatFunc.eval,Polynomial.eval₂_id,div_eq_mul_inv] using
      numeric_mul hn (numeric_inv hd hdn)

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 100000 in
set_option backward.isDefEq.respectTransparency false in

theorem forward_two_cell_residue
    (S : ActualKPBinding F ζ hζ q) (P : Polarization S.heisenberg)
    (dx : Measure (KPExceptionalRaw.LocalField F q)) [dx.IsAddHaarMeasure]
    (hμ : 0 < integerMass (KPExceptionalRaw.LocalField F q) dx)
    (ω : (valuation (KPExceptionalRaw.LocalField F q)).integer)
    (hω : IsPrimitiveRoot ω 3)
    (α : ℂ) (hα : α ^ 6 = (residueCardinality (KPExceptionalRaw.LocalField F q) : ℂ)) :
    ∀ (J : CompactOpenLevel (KPExceptionalRaw.ActualCover F ζ hζ q)),
      (J.toOpenSubgroup : Subgroup (KPExceptionalRaw.ActualCover F ζ hζ q)) ≤
        S.iwasawa.compact.toOpenSubgroup →
      ∀ (p : LevelLaurentOperator (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .plus)
        (pRev : LevelLaurentOperator (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .minus),
      IsLevelNumerator (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J dx .plus p →
      IsLevelNumerator (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J dx .minus pRev →
      (rationalStandard (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .minus pRev
          (RatFunc.C α * RatFunc.X)).comp
        (rationalStandard (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa J .plus p
          (RatFunc.C α * RatFunc.X)) =
        rationalResidueScalar (KPExceptionalRaw.LocalField F q) dx • LinearMap.id := by
  classical
  obtain ⟨Jτ⟩ := KPRankOneShellContinuation.actual_exists_tauStandardFamily F ζ hζ q
    (KPLocalExceptionalConstruction.actualCanonicalInducing F ζ hζ q S) P dx
  let Jreg := centerStandardFamilyFromTau F ζ hζ q S.heisenberg S.borel P S.iwasawa dx Jτ
  let rep : S.D → KPExceptionalRaw.actualTorus F ζ hζ q :=
    Function.surjInv S.heisenberg.quotient_surjective
  have hrep : ∀ d, S.heisenberg.π (rep d) = d :=
    Function.surjInv_eq S.heisenberg.quotient_surjective
  intro J hJ p pRev hp hpRev
  apply rational_from_continued F ζ hζ q S P dx α hα J p pRev
  intro w hw0 hw6 hwR r hr
  obtain ⟨r',hr',hp',hm'⟩ := both_standard_denominators_regular F q α w hα hw0 hw6
  have hrr : r' = r := Units.ext (hr'.trans hr.symm)
  subst r'
  have hregular : IsRegular F q r := by
    simpa only [KPRankOneReverseRegulatorShells.IsRegular,KPRankOneReverseRegulatorShells.t,
      denominator,ite_true,KPRankOneRootParameter.t,
      root_parameter_additiveParameter F q r] using hp'
  let c := RatFunc.eval (RingHom.id ℂ) w (rationalResidueScalar (LocalField F q) dx)
  apply continued_scalar_from_compact_whole F ζ hζ q S P dx Jτ Jreg J p pRev
    hp hpRev (additiveParameter F q r) c hp' hm'
  apply compact_whole_from_pure F ζ hζ q S P dx Jreg rep hrep r c hp' hm' ?_ J hJ
  intro d φ hφ hcφ
  apply Subtype.ext
  funext g
  exact pure_whole_from_zero_coefficients F ζ hζ q S P dx Jreg rep hrep r c hp' hm'
    (by
      intro d₀ φ₀ hφ₀ hcφ₀ e
      obtain ⟨ps,hps⟩ := KPActualResidueSources.actual_reverse_shell_expansion
        F ζ hζ q S P S.iwasawa dx Jreg rep hrep d₀ φ₀ hφ₀ hcφ₀
      have hjoint : ∀ (r₀ t₀ : ℂˣ), (t₀ : ℂ) = KPRankOneReverseRegulatorShells.t F q (r₀ : ℂ) →
          ∀ ρ : ℂ, KPJointRegulator.cone (LocalField F q) t₀ ρ → ∀ h,
          H F ζ hζ q S.heisenberg S.borel P S.iwasawa dx Jreg (S.openCell P)
            rep hrep d₀ φ₀ hφ₀ hcφ₀ r₀ ρ h =
            evaluateNumerator (ps h) r₀ (Q F q ρ) / shellDenominator F q r₀ (Q F q ρ) := by
        intro r₀ t₀ ht₀ ρ hcone h
        have hr₀ : IsRegular F q r₀ := by
          change 1-KPRankOneReverseRegulatorShells.t F q (r₀:ℂ) ≠ 0
          rw [← ht₀]
          intro he
          have hn := hcone.2.2.2
          rw [← sub_eq_zero.mp he,norm_one] at hn
          exact lt_irrefl _ hn
        have hregion : ConvergenceRegion F q r₀ ρ := by
          refine ⟨hcone.2.1,?_⟩
          rw [← ht₀]
          exact hcone.2.2.1
        exact (hps r₀ hr₀ ρ hregion h).2
      have hres := ActualShellPort.actual_shell_restriction_residue F ζ hζ q S P dx Jreg
        rep hrep d₀ φ₀ hφ₀ hcφ₀ ps hjoint α hα e
      have hcoef := ActualShellPort.actual_joint_shell_Q1_standard_coefficient F ζ hζ q S P dx
        Jreg rep hrep d₀ φ₀ hφ₀ hcφ₀ ps hjoint r hregular (rep e)
      have hpull := numeric_scaled_root α w (restrictionAtOne F q (ps (rep e)))
        (by rw [← hr]; exact hcoef.1)
      have hval := numeric_mul (numeric_const w (φ₀ 0 * if e=d₀ then 1 else 0))
        (show Numeric w (rationalResidueScalar (LocalField F q) dx) c from ⟨hwR,rfl⟩)
      have heval := congrArg (RatFunc.eval (RingHom.id ℂ) w) hres.2
      have hnum : KPRankOneReverseRegulatorSpecialization.actualDoubleCoefficient F ζ hζ q
          S.heisenberg S.borel P S.iwasawa dx Jreg (S.openCell P) rep hrep d₀ φ₀ hφ₀ hcφ₀ r (rep e) =
          c*(φ₀ 0*if e=d₀ then 1 else 0) := by
        calc
          _ = RatFunc.eval (RingHom.id ℂ) (r:ℂ) (restrictionAtOne F q (ps (rep e))) := hcoef.2.symm
          _ = RatFunc.eval (RingHom.id ℂ) w
            (RatFunc.eval RatFunc.C (RatFunc.C α*RatFunc.X) (restrictionAtOne F q (ps (rep e)))) := by
              rw [hr]; exact hpull.2.symm
          _ = (φ₀ 0*if e=d₀ then 1 else 0)*c := heval.trans hval.2
          _ = _ := mul_comm _ _
      exact hnum) d φ hφ hcφ g

end
end DedekindZetaZeroFree.KPActualScalarBinding.ResidueSteps
