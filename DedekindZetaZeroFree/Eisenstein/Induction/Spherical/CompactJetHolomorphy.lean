module

public import DedekindZetaZeroFree.Eisenstein.Sections.SmoothIwasawaLogNorm
public import DedekindZetaZeroFree.Adeles.Quotients.CompactOpenFiniteLevels

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section
open scoped Classical NumberField NNReal

namespace DedekindZetaZeroFree.KPContFlatStageJetHolomorphy

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev JetSpace (n : ℕ) :=
  ContinuousMultilinearMap ℝ
    (fun _ : Fin n => KPGlobalTorusBorelTwistCompatibility.GroupArch F) ℂ

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S]
  [hfd : FiniteDimensional ℂ S]
  (ι : S →ₗ[ℂ] KPMsRationalCompactCrossPairing.Vplus F ζ hζ
    (KPContFlatSourceRecipe.D F ζ hζ))

def L (s : ℂ) (v : S) (g : KPGlobalTorusFunctionData.G F ζ hζ) : ℂ :=
  (KPContFlatSourceRecipe.flatR F ζ hζ s (ι v)).val g

def spatialJet (g : KPGlobalTorusFunctionData.G F ζ hζ) (n : ℕ)
    (s : ℂ) (v : S) : KPGlobalTorusBorelTwistCompatibility.GroupArch F → JetSpace F n :=
  iteratedFDerivWithin ℝ n
    (fun z => L F ζ hζ ι s v
      (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g))
    (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F)

def parameterSection (m : ℕ) (s : ℂ) (v : S)
    (g : KPGlobalTorusFunctionData.G F ζ hζ) : ℂ :=
  (KPContFlatSourceRecipe.alpha F ζ hζ g : ℂ) ^ m * L F ζ hζ ι s v g

def parameterJet (g : KPGlobalTorusFunctionData.G F ζ hζ) (m n : ℕ)
    (s : ℂ) (v : S) : KPGlobalTorusBorelTwistCompatibility.GroupArch F → JetSpace F n :=
  iteratedFDerivWithin ℝ n
    (fun z => parameterSection F ζ hζ ι m s v
      (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g))
    (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F)

section JointJets
open scoped Topology
variable {A E Y : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
 [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
set_option backward.isDefEq.respectTransparency.types false in
private lemma joint_jet {h : A → E → Y} {U : Set E} (hU : IsOpen U)
 (hh : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry h) (Set.univ ×ˢ U)) (n : ℕ) :
 ContDiffOn ℝ (⊤ : ℕ∞) (fun p : A × E => iteratedFDeriv ℝ n (h p.1) p.2) (Set.univ ×ˢ U) := by
 induction n with
 | zero =>
   simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def, Function.uncurry] using
     (continuousMultilinearCurryFin0 ℝ E Y).symm.contDiff.comp_contDiffOn hh
 | succ n ih =>
   intro p hp
   have hio : IsOpen (Set.univ ×ˢ U : Set (A × E)) := isOpen_univ.prod hU
   have hlocal := ih.contDiffAt (hio.mem_nhds hp)
   have hcomp : ContDiffAt ℝ (⊤ : ℕ∞)
       (fun q : (A × E) × E => iteratedFDeriv ℝ n (h q.1.1) q.2) (p, p.2) :=
     hlocal.comp (p, p.2) (contDiff_fst.fst.prodMk contDiff_snd).contDiffAt
   have hd := ContDiffAt.fderiv (f := fun q : A × E => iteratedFDeriv ℝ n (h q.1))
     (g := fun q : A × E => q.2) (m := (⊤ : ℕ∞)) hcomp contDiff_snd.contDiffAt (by simp)
   have hc := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) Y).symm.contDiff.contDiffAt.comp p hd
   simpa only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, Function.comp_def] using hc.contDiffWithinAt
set_option backward.isDefEq.respectTransparency.types false in
private lemma partial_eq (h : A → E → Y) (s : A) (z : E)
 (hh : DifferentiableAt ℝ (Function.uncurry h) (s,z)) :
 fderiv ℝ (h s) z = (fderiv ℝ (Function.uncurry h) (s,z)).comp (ContinuousLinearMap.inr ℝ A E) := by
 exact (hh.hasFDerivAt.comp z (hasFDerivAt_prodMk_right s z)).fderiv
set_option backward.isDefEq.respectTransparency.types false in
private lemma mixed_partial (h : A → E → Y) (s : A) (z : E)
 (hh : ContDiffAt ℝ (⊤ : ℕ∞) (Function.uncurry h) (s,z)) (v : A) (w : E) :
 (fderiv ℝ (fun t => fderiv ℝ (h t) z) s) v w =
 (fderiv ℝ (fun x => fderiv ℝ (fun t => h t x) s) z) w v := by
 let H := Function.uncurry h
 let D := fderiv ℝ H
 let L := ContinuousLinearMap.inl ℝ A E
 let R := ContinuousLinearMap.inr ℝ A E
 let CR := (ContinuousLinearMap.compL ℝ E (A × E) Y).flip R
 let CL := (ContinuousLinearMap.compL ℝ A (A × E) Y).flip L
 have hD : HasFDerivAt D (fderiv ℝ D (s,z)) (s,z) :=
   (hh.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiableAt (by simp) |>.hasFDerivAt
 have hs : (fun t => fderiv ℝ (h t) z) =ᶠ[𝓝 s]
     (fun t => CR (D (t,z))) := by
   have hn := (hh.of_le (show (2 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)).eventually (by simp)
   filter_upwards [(continuous_id.prodMk continuous_const).continuousAt.eventually hn] with t ht
   exact partial_eq h t z (ht.differentiableAt (by simp))
 have hz : (fun x => fderiv ℝ (fun t => h t x) s) =ᶠ[𝓝 z]
     (fun x => CL (D (s,x))) := by
   have hn := (hh.of_le (show (2 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)).eventually (by simp)
   filter_upwards [(continuous_const.prodMk continuous_id).continuousAt.eventually hn] with x hx
   have hd : HasFDerivAt H (D (s,x)) (s,x) := (hx.differentiableAt (by simp)).hasFDerivAt
   have hleft : HasFDerivAt (fun t : A => H (t,x)) (CL (D (s,x))) s :=
     by convert hd.comp s (hasFDerivAt_prodMk_left (𝕜 := ℝ) s x) using 1 <;> rfl
   exact hleft.fderiv
 have hsd := CR.hasFDerivAt.comp s (hD.comp s (hasFDerivAt_prodMk_left s z))
 have hzd := CL.hasFDerivAt.comp z (hD.comp z (hasFDerivAt_prodMk_right s z))
 have hsde := hsd.fderiv
 have hzde := hzd.fderiv
 dsimp only [Function.comp_def] at hsde hzde
 rw [hs.fderiv_eq, hz.fderiv_eq, hsde, hzde]
 exact (hh.isSymmSndFDerivAt (by simp)).eq (v,0) (0,w)

section Complex
variable [NormedSpace ℂ Y] [IsScalarTower ℝ ℂ Y]
set_option backward.isDefEq.respectTransparency.types false in
private lemma partial_snd_hasDeriv (h k : ℂ → E → Y) (U : Set E) (hU : IsOpen U)
 (hh : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry h) (Set.univ ×ˢ U))
 (hk : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry k) (Set.univ ×ˢ U))
 (hd : ∀ s z, z ∈ U → HasDerivAt (fun t => h t z) (k s z) s)
 (s : ℂ) (z : E) (hz : z ∈ U) :
 HasDerivAt (fun t => fderiv ℝ (h t) z) (fderiv ℝ (k s) z) s := by
 have hlocal := hh.contDiffAt ((isOpen_univ.prod hU).mem_nhds (show (s,z) ∈ Set.univ ×ˢ U from ⟨Set.mem_univ s,hz⟩))
 have hcomp : ContDiffAt ℝ (⊤ : ℕ∞)
     (fun q : ℂ × E => h q.1 q.2) (s,z) := hlocal
 have hder : DifferentiableAt ℝ (fun t => fderiv ℝ (h t) z) s := by
   have h2 : ContDiffAt ℝ (⊤ : ℕ∞)
       (Function.uncurry (fun t x => h t x)) (s,z) := hlocal
   exact (h2.fderiv (g := fun _ : ℂ => z) (m := (⊤ : ℕ∞)) contDiffAt_const (by simp)).differentiableAt (by simp)
 have heq : (ContinuousLinearMap.toSpanSingleton ℂ (fderiv ℝ (k s) z)).restrictScalars ℝ =
     fderiv ℝ (fun t => fderiv ℝ (h t) z) s := by
   ext d w
   rw [mixed_partial h s z hlocal d w]
   have ht : (fun x => (fderiv ℝ (fun t => h t x) s) d) =ᶠ[𝓝 z]
       (fun x => d • k s x) := by
     filter_upwards [hU.mem_nhds hz] with x hx
     rw [((hd s x hx).hasFDerivAt.restrictScalars ℝ).fderiv]
     rfl
   have hp := (hk.contDiffAt ((isOpen_univ.prod hU).mem_nhds (show (s,z) ∈ Set.univ ×ˢ U from ⟨Set.mem_univ s,hz⟩))).comp
     z (contDiffAt_const.prodMk contDiffAt_id)
   have hf := hp.differentiableAt (by simp)
   have hswap : ContDiffAt ℝ (⊤ : ℕ∞) (Function.uncurry (fun x t => h t x)) (z,s) :=
     hlocal.comp (z,s) (contDiff_snd.prodMk contDiff_fst).contDiffAt
   have happ := (ContinuousLinearMap.apply ℝ Y d).hasFDerivAt.comp z
     ((hswap.fderiv (g := fun _ : E => s) (m := (⊤ : ℕ∞)) contDiffAt_const (by simp)).differentiableAt (by simp)).hasFDerivAt
   have he : (fderiv ℝ (fun x => (fderiv ℝ (fun t => h t x) s) d) z) w =
       ((fderiv ℝ (fun x => fderiv ℝ (fun t => h t x) s) z) w) d := by
     have he := happ.fderiv
     dsimp only [Function.comp_def] at he
     convert congrArg (fun T : E →L[ℝ] Y => T w) he using 1 <;> rfl
   rw [← he, ht.fderiv_eq]
   have hf' : DifferentiableAt ℝ (k s) z := hf
   change (d • fderiv ℝ (k s) z) w = (fderiv ℝ (d • k s) z) w
   rw [fderiv_const_smul hf' d]
 exact hasFDerivAt_of_restrictScalars ℝ hder.hasFDerivAt heq
end Complex

section ComplexJets
variable [NormedSpace ℂ Y] [IsScalarTower ℝ ℂ Y]
 def complexCurry (n : ℕ) :
 (E →L[ℝ] E [×n]→L[ℝ] Y) →L[ℂ] E [×(n+1)]→L[ℝ] Y where
 toFun := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) Y).symm
 map_add' := map_add _
 map_smul' c v := by
   ext w
   simp only [continuousMultilinearCurryLeftEquiv_symm_apply,
     ContinuousLinearMap.smul_apply, ContinuousMultilinearMap.smul_apply, RingHom.id_apply]
 cont := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) Y).symm.continuous
set_option backward.isDefEq.respectTransparency.types false in
private lemma jets_hasDeriv (h k : ℂ → E → Y) (U : Set E) (hU : IsOpen U)
 (hh : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry h) (Set.univ ×ˢ U))
 (hk : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry k) (Set.univ ×ˢ U))
 (hd : ∀ s z, z ∈ U → HasDerivAt (fun t => h t z) (k s z) s)
 (n : ℕ) (s : ℂ) (z : E) (hz : z ∈ U) :
 HasDerivAt (fun t => iteratedFDeriv ℝ n (h t) z) (iteratedFDeriv ℝ n (k s) z) s := by
 induction n generalizing s z with
 | zero =>
   let T : Y →L[ℂ] E [×0]→L[ℝ] Y :=
     { toFun := (continuousMultilinearCurryFin0 ℝ E Y).symm
       map_add' := map_add _
       map_smul' := by intro c v; ext w; simp
       cont := (continuousMultilinearCurryFin0 ℝ E Y).symm.continuous }
   have H := T.hasFDerivAt.comp s (hd s z hz).hasFDerivAt
   change HasFDerivAt _ (ContinuousLinearMap.toSpanSingleton ℂ _) s
   convert H using 1 <;> simp only [iteratedFDeriv_zero_eq_comp, Function.comp_def, ContinuousLinearMap.comp_toSpanSingleton] <;> rfl
 | succ n ih =>
   have hp := partial_snd_hasDeriv (fun t x => iteratedFDeriv ℝ n (h t) x)
     (fun t x => iteratedFDeriv ℝ n (k t) x) U hU
     (joint_jet hU hh n) (joint_jet hU hk n) (fun t x hx => ih t x hx) s z hz
   have H := (complexCurry (E := E) (Y := Y) n).hasFDerivAt.comp s hp.hasFDerivAt
   change HasFDerivAt _ (ContinuousLinearMap.toSpanSingleton ℂ _) s
   convert H using 1 <;> simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_def, ContinuousLinearMap.comp_toSpanSingleton] <;> rfl
end ComplexJets
end JointJets

section CompactDifferentiation
open scoped Topology
open Filter
variable {X Y : Type*} [UniformSpace X] [CompactSpace X]
 [NormedAddCommGroup Y] [NormedSpace ℂ Y]
set_option backward.isDefEq.respectTransparency.types false in
private lemma compact_hasDeriv (h k : ℂ → C(X,Y))
 (hk : Continuous (Function.uncurry (fun t x => k t x)))
 (hd : ∀ t x, HasDerivAt (fun r => h r x) (k t x) t) (s : ℂ) :
 HasDerivAt h (k s) s := by
 apply HasDerivAt.of_isLittleO
 rw [Asymptotics.isLittleO_iff]
 intro c hc
 have hu := Metric.tendstoUniformly_iff.mp (hk.tendstoUniformly (fun t x => k t x) s) c hc
 have hseg : ∀ᶠ t in 𝓝 s, ∀ r ∈ segment ℝ s t, ∀ x : X, ‖k r x - k s x‖ ≤ c := by
   have hs : ∀ᶠ t in 𝓝[Set.univ] s, ∀ x : X, ‖k t x - k s x‖ ≤ c := by
     simpa only [nhdsWithin_univ, dist_eq_norm_sub, norm_sub_rev] using hu.mono (fun t ht x => (ht x).le)
   simpa only [nhdsWithin_univ] using (convex_univ : Convex ℝ (Set.univ : Set ℂ)).eventually_nhdsWithin_segment (Set.mem_univ s) hs
 filter_upwards [hseg] with t ht
 apply (ContinuousMap.norm_le (h t - h s - (t-s) • k s) (mul_nonneg hc.le (norm_nonneg _))).mpr
 intro x
 have H := (convex_segment s t).norm_image_sub_le_of_norm_hasFDerivWithin_le'
   (f := fun r => h r x) (f' := fun r => ContinuousLinearMap.toSpanSingleton ℂ (k r x))
   (φ := ContinuousLinearMap.toSpanSingleton ℂ (k s x)) (C := c)
   (fun r _ => (hd r x).hasFDerivAt.hasFDerivWithinAt)
   (fun r hr => by
     have he : ContinuousLinearMap.toSpanSingleton ℂ (k r x) - ContinuousLinearMap.toSpanSingleton ℂ (k s x) =
       ContinuousLinearMap.toSpanSingleton ℂ (k r x - k s x) := by ext a; simp [smul_sub]
     rw [he, ContinuousLinearMap.norm_toSpanSingleton]
     exact ht r hr x)
   (left_mem_segment ℝ s t) (right_mem_segment ℝ s t)
 simpa using H

end CompactDifferentiation
 lemma L_formula (s : ℂ) (v : S) (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    L F ζ hζ ι s v g =
      Complex.exp (s * (KPContFlatSourceRecipe.alpha F ζ hζ g : ℂ)) * (ι v).val.val g := by
  unfold L
  rw [KPContFlatSourceRecipe.flatR_formula]

private lemma induced_chart_contDiffOn (P : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (f : KPGlobalTorusBorelTwistCompatibility.Induced F ζ hζ P)
    (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => (f.val.val
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g)).val.val 1)
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) := by
  have hf := f.property
  change f.val ∈ ⨆ J, KPGlobalTorusBorelTwistCompatibility.InducedLevel F ζ hζ P J at hf
  exact Submodule.iSup_induction
    (motive := fun x : KPGlobalTorusBorelTwistCompatibility.InducedFunctions F ζ hζ P =>
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun z => (x.val
          (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g)).val.val 1)
        (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F))
    (fun J => KPGlobalTorusBorelTwistCompatibility.InducedLevel F ζ hζ P J) hf
    (fun J x hx => hx.1 g) contDiffOn_const (fun x y hx hy => hx.add hy)

private lemma scalarSection_chart_contDiffOn
    (hSmooth : ∀ v : S, (ι v).val ∈
      KPMsRationalCompactCrossPairing.scalarSmooth F ζ hζ
        (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0))
    (v : S) (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => (ι v).val.val
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g))
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) := by
  obtain ⟨f, hf⟩ := hSmooth v
  have hfun : (fun z => (ι v).val.val
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g)) =
      (fun z => (f.val.val
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g)).val.val 1) := by
    funext z
    rw [← hf, KPGlobalTorusBorelTwistCompatibility.scalarSection_formula]
  rw [hfun]
  exact induced_chart_contDiffOn F ζ hζ
    (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0) f g

private lemma alpha_chart_contDiffOn (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => (KPContFlatSourceRecipe.alpha F ζ hζ
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g) : ℂ))
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) :=
  (Complex.ofRealCLM.contDiff.comp_contDiffOn
    (KPContFlatLogNormSmooth.alpha_groupArchChart_mul_contDiffOn F ζ hζ g)).of_le le_top

private lemma exp_alpha_chart_contDiffOn (s : ℂ) (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => Complex.exp (s * (KPContFlatSourceRecipe.alpha F ζ hζ
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g) : ℂ)))
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) :=
  ((contDiffOn_const (c := s)).mul (alpha_chart_contDiffOn F ζ hζ g)).cexp

private lemma L_chart_contDiffOn
    (hSmooth : ∀ v : S, (ι v).val ∈
      KPMsRationalCompactCrossPairing.scalarSmooth F ζ hζ
        (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0))
    (v : S) (s : ℂ) (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => L F ζ hζ ι s v
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g))
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) := by
  have hfun : (fun z => L F ζ hζ ι s v
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g)) =
      (fun z => Complex.exp (s * (KPContFlatSourceRecipe.alpha F ζ hζ
          (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g) : ℂ)) *
        ((ι v).val.val
          (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g))) := by
    funext z
    rw [L_formula]
  rw [hfun]
  exact (exp_alpha_chart_contDiffOn F ζ hζ s g).mul
    (scalarSection_chart_contDiffOn F ζ hζ ι hSmooth v g)

private lemma L_chart_varying_contDiffOn
    (hSmooth : ∀ v : S, (ι v).val ∈
      KPMsRationalCompactCrossPairing.scalarSmooth F ζ hζ
        (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0))
    (f : ℂ → S) (s : ℂ) (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => L F ζ hζ ι s (f s)
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g))
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) := by
  have hfun : (fun z => L F ζ hζ ι s (f s)
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g)) =
      (fun z => Complex.exp (s * (KPContFlatSourceRecipe.alpha F ζ hζ
          (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g) : ℂ)) *
        ((ι (f s)).val.val
          (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g))) := by
    funext z
    rw [L_formula]
  rw [hfun]
  exact (exp_alpha_chart_contDiffOn F ζ hζ s g).mul
    (scalarSection_chart_contDiffOn F ζ hζ ι hSmooth (f s) g)

 lemma parameterSection_chart_contDiffOn
    (hSmooth : ∀ v : S, (ι v).val ∈
      KPMsRationalCompactCrossPairing.scalarSmooth F ζ hζ
        (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0))
    (g : KPGlobalTorusFunctionData.G F ζ hζ) (m : ℕ) (s : ℂ) (v : S) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => parameterSection F ζ hζ ι m s v
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g))
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) := by
  have hfun : (fun z => parameterSection F ζ hζ ι m s v
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g)) =
      (fun z => ((KPContFlatSourceRecipe.alpha F ζ hζ
          (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g) : ℂ) ^ m) *
        (Complex.exp (s * (KPContFlatSourceRecipe.alpha F ζ hζ
          (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g) : ℂ)) *
        ((ι v).val.val
          (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g)))) := by
    funext z
    unfold parameterSection
    rw [L_formula]
  rw [hfun]
  exact ((alpha_chart_contDiffOn F ζ hζ g).pow m).mul
    ((exp_alpha_chart_contDiffOn F ζ hζ s g).mul
      (scalarSection_chart_contDiffOn F ζ hζ ι hSmooth v g))

variable (hSmooth : ∀ v : S, (ι v).val ∈
  KPMsRationalCompactCrossPairing.scalarSmooth F ζ hζ
    (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0))

include hSmooth hfd

set_option backward.isDefEq.respectTransparency.types false in
private lemma parameterJet_joint_continuousOn
    (g : KPGlobalTorusFunctionData.G F ζ hζ) (m n : ℕ) (v : S) :
    ContinuousOn (fun p : ℂ × KPGlobalTorusBorelTwistCompatibility.GroupArch F =>
      parameterJet F ζ hζ ι g m n p.1 v p.2)
      (Set.univ ×ˢ KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) := by
  let U := KPGlobalTorusBorelTwistCompatibility.groupArchDomain F
  let a := fun z => (KPContFlatSourceRecipe.alpha F ζ hζ
    (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g) : ℂ)
  let b := fun z => (ι v).val.val
    (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g)
  have ha : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℂ ×
      KPGlobalTorusBorelTwistCompatibility.GroupArch F => a p.2) (Set.univ ×ˢ U) :=
    (alpha_chart_contDiffOn F ζ hζ g).comp contDiffOn_snd (fun p hp => hp.2)
  have hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℂ ×
      KPGlobalTorusBorelTwistCompatibility.GroupArch F => b p.2) (Set.univ ×ˢ U) :=
    (scalarSection_chart_contDiffOn F ζ hζ ι hSmooth v g).comp
      contDiffOn_snd (fun p hp => hp.2)
  have hh := (ha.pow m).mul ((contDiffOn_fst.mul ha).cexp.mul hb)
  have hj := (joint_jet (KPGlobalTorusBorelTwistCompatibility.groupArchDomain_open F)
    (h := fun s z => a z ^ m * (Complex.exp (s * a z) * b z)) hh n).continuousOn
  apply hj.congr
  intro p hp
  dsimp only [parameterJet]
  rw [iteratedFDerivWithin_of_isOpen n
    (KPGlobalTorusBorelTwistCompatibility.groupArchDomain_open F) hp.2]
  congr 1

set_option backward.isDefEq.respectTransparency.types false in
 def parameterJet_linearMap
    (g : KPGlobalTorusFunctionData.G F ζ hζ) (m n : ℕ) (s : ℂ)
    (z : KPGlobalTorusBorelTwistCompatibility.GroupArch F)
    (hz : z ∈ KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) :
    S →ₗ[ℂ] JetSpace F n where
  toFun v := parameterJet F ζ hζ ι g m n s v z
  map_add' v w := by
    have hv := (parameterSection_chart_contDiffOn F ζ hζ ι hSmooth g m s v).of_le
      (show (n : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)
    have hw := (parameterSection_chart_contDiffOn F ζ hζ ι hSmooth g m s w).of_le
      (show (n : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)
    unfold parameterJet
    have he : (fun x => parameterSection F ζ hζ ι m s (v+w)
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ x * g)) =
        (fun x => parameterSection F ζ hζ ι m s v
          (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ x * g)) +
        (fun x => parameterSection F ζ hζ ι m s w
          (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ x * g)) := by
      funext x
      simp [parameterSection, L_formula, map_add, mul_add]
    rw [he]
    exact iteratedFDerivWithin_add_apply (hv z hz) (hw z hz)
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain_open F).uniqueDiffOn hz
  map_smul' c v := by
    have hv := (parameterSection_chart_contDiffOn F ζ hζ ι hSmooth g m s v).of_le
      (show (n : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)
    unfold parameterJet
    have he : (fun x => parameterSection F ζ hζ ι m s (c • v)
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ x * g)) =
        c • (fun x => parameterSection F ζ hζ ι m s v
          (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ x * g)) := by
      funext x
      simp [parameterSection, L_formula, map_smul, mul_left_comm]
    rw [he]
    exact iteratedFDerivWithin_const_smul_apply (hv z hz)
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain_open F).uniqueDiffOn hz

 def levelInter (U V : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    KPGlobalTorusFunctionData.FiniteLevel F ζ hζ :=
  ⟨U.toOpenSubgroup ⊓ V.toOpenSubgroup, U.isCompact.inter_right V.toOpenSubgroup.isClosed⟩

omit hSmooth hfd in
private lemma induced_uniform_level
    (P : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (f : KPGlobalTorusBorelTwistCompatibility.Induced F ζ hζ P) :
    ∃ J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
      ∀ g (j : KPGlobalTorusFunctionData.globalLevel F ζ hζ J),
        f.val.val (g * j.val) = f.val.val g := by
  obtain ⟨U, _⟩ := KPCompactFiniteLevel.exists_level F ζ hζ
  have hf := f.property
  change f.val ∈ ⨆ J, KPGlobalTorusBorelTwistCompatibility.InducedLevel F ζ hζ P J at hf
  exact Submodule.iSup_induction
    (motive := fun x : KPGlobalTorusBorelTwistCompatibility.InducedFunctions F ζ hζ P =>
      ∃ J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
        ∀ g (j : KPGlobalTorusFunctionData.globalLevel F ζ hζ J),
          x.val (g * j.val) = x.val g)
    (fun J => KPGlobalTorusBorelTwistCompatibility.InducedLevel F ζ hζ P J) hf
    (fun J x hx => ⟨J, hx.2⟩) ⟨U, fun _ _ => rfl⟩ (by
      intro x y hx hy
      obtain ⟨J, hJ⟩ := hx
      obtain ⟨K, hK⟩ := hy
      refine ⟨levelInter F ζ hζ J K, ?_⟩
      intro g j
      have hleft : KPGlobalTorusFunctionData.globalLevel F ζ hζ (levelInter F ζ hζ J K) ≤
          KPGlobalTorusFunctionData.globalLevel F ζ hζ J := Subgroup.map_mono inf_le_left
      have hright : KPGlobalTorusFunctionData.globalLevel F ζ hζ (levelInter F ζ hζ J K) ≤
          KPGlobalTorusFunctionData.globalLevel F ζ hζ K := Subgroup.map_mono inf_le_right
      change x.val (g * j.val) + y.val (g * j.val) = _
      rw [hJ g ⟨j.val, hleft j.property⟩, hK g ⟨j.val, hright j.property⟩]
      rfl)

private lemma scalar_uniform_level (v : S) :
    ∃ J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
      ∀ g (j : KPGlobalTorusFunctionData.globalLevel F ζ hζ J),
        (ι v).val.val (g * j.val) = (ι v).val.val g := by
  obtain ⟨f, hf⟩ := hSmooth v
  obtain ⟨J, hJ⟩ := induced_uniform_level F ζ hζ
    (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0) f
  refine ⟨J, ?_⟩
  intro g j
  rw [← hf, KPGlobalTorusBorelTwistCompatibility.scalarSection_formula,
    KPGlobalTorusBorelTwistCompatibility.scalarSection_formula, hJ g j]

theorem stage_uniform_right_level :
    ∃ J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
      ∀ (s : ℂ) (v : S) (g : KPGlobalTorusFunctionData.G F ζ hζ)
        (j : KPGlobalTorusFunctionData.globalLevel F ζ hζ J),
        L F ζ hζ ι s v (g * j.val) = L F ζ hζ ι s v g := by
  let e := Module.finBasis ℂ S
  obtain ⟨U, hU⟩ := KPCompactFiniteLevel.exists_level F ζ hζ
  have hfinite (A : Finset (Fin (Module.finrank ℂ S))) :
      ∃ J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
        KPGlobalTorusFunctionData.globalLevel F ζ hζ J ≤ (KPContFlatSourceRecipe.D F ζ hζ).K ∧
        ∀ i ∈ A, ∀ g (j : KPGlobalTorusFunctionData.globalLevel F ζ hζ J),
          (ι (e i)).val.val (g * j.val) = (ι (e i)).val.val g := by
    induction A using Finset.induction_on with
    | empty => exact ⟨U, hU, by simp⟩
    | @insert i A hi ih =>
      obtain ⟨J, hJK, hJ⟩ := ih
      obtain ⟨K, hK⟩ := scalar_uniform_level F ζ hζ ι hSmooth (e i)
      let W := levelInter F ζ hζ J K
      have hWJ : KPGlobalTorusFunctionData.globalLevel F ζ hζ W ≤
          KPGlobalTorusFunctionData.globalLevel F ζ hζ J := Subgroup.map_mono inf_le_left
      have hWK : KPGlobalTorusFunctionData.globalLevel F ζ hζ W ≤
          KPGlobalTorusFunctionData.globalLevel F ζ hζ K := Subgroup.map_mono inf_le_right
      refine ⟨W, hWJ.trans hJK, ?_⟩
      intro k hk g j
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact hK g ⟨j.val, hWK j.property⟩
      · exact hJ k hk g ⟨j.val, hWJ j.property⟩
  obtain ⟨J, hJK, hJ⟩ := hfinite Finset.univ
  refine ⟨J, ?_⟩
  intro s v g j
  have hscalar : (ι v).val.val (g * j.val) = (ι v).val.val g := by
    conv_lhs => rw [← e.sum_repr v]
    conv_rhs => rw [← e.sum_repr v]
    simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul,
      Finset.sum_apply, Finset.sum_fn, Pi.smul_apply, smul_eq_mul]
    change (∑ i, e.repr v i * (ι (e i)).val.val (g * j.val)) =
      ∑ i, e.repr v i * (ι (e i)).val.val g
    apply Finset.sum_congr rfl
    intro i hi
    rw [hJ i hi g j]
  have ha := KPContFlatFullProductIwasawa.alpha_mul_compact F ζ hζ g ⟨j.val, hJK j.property⟩
  rw [L_formula, L_formula, hscalar]
  exact congrArg (fun a : ℝ => Complex.exp (s * (a : ℂ)) * (ι v).val.val g) ha

theorem parameterSection_contDiffOn
    (g : KPGlobalTorusFunctionData.G F ζ hζ) (m : ℕ) (s : ℂ) (v : S) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => parameterSection F ζ hζ ι m s v
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g))
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) :=
  parameterSection_chart_contDiffOn F ζ hζ ι hSmooth g m s v

theorem L_contDiffOn (f : ℂ → S) (s : ℂ)
    (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => L F ζ hζ ι s (f s)
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g))
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) :=
  L_chart_varying_contDiffOn F ζ hζ ι hSmooth f s g

theorem parameterJet_continuousOn
    (g : KPGlobalTorusFunctionData.G F ζ hζ) (m n : ℕ)
    (C : KPGlobalTorusFunctionData.JetCompact
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F)) (s : ℂ) (v : S) :
    ContinuousOn (parameterJet F ζ hζ ι g m n s v) C.set :=
  ((parameterSection_chart_contDiffOn F ζ hζ ι hSmooth g m s v).continuousOn_iteratedFDerivWithin
    (m := n) (by simp)
    (KPGlobalTorusBorelTwistCompatibility.groupArchDomain_open F).uniqueDiffOn).mono C.inside

theorem spatialJet_continuousOn
    (g : KPGlobalTorusFunctionData.G F ζ hζ) (n : ℕ)
    (C : KPGlobalTorusFunctionData.JetCompact
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F)) (s : ℂ) (v : S) :
    ContinuousOn (spatialJet F ζ hζ ι g n s v) C.set :=
  ((L_chart_contDiffOn F ζ hζ ι hSmooth v s g).continuousOn_iteratedFDerivWithin
    (m := n) (by simp)
    (KPGlobalTorusBorelTwistCompatibility.groupArchDomain_open F).uniqueDiffOn).mono C.inside

def compactJet (g : KPGlobalTorusFunctionData.G F ζ hζ) (n : ℕ)
    (C : KPGlobalTorusFunctionData.JetCompact
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F)) (s : ℂ) (v : S) :
    C(C.set, JetSpace F n) :=
  ⟨fun z => spatialJet F ζ hζ ι g n s v z.val,
    (spatialJet_continuousOn F ζ hζ ι hSmooth g n C s v).restrict⟩

def compactParameterJet (g : KPGlobalTorusFunctionData.G F ζ hζ) (m n : ℕ)
    (C : KPGlobalTorusFunctionData.JetCompact
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F)) (s : ℂ) (v : S) :
    C(C.set, JetSpace F n) :=
  ⟨fun z => parameterJet F ζ hζ ι g m n s v z.val,
    (parameterJet_continuousOn F ζ hζ ι hSmooth g m n C s v).restrict⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 3000000 in

theorem compactParameterJet_hasDerivWithinAt
    (g : KPGlobalTorusFunctionData.G F ζ hζ) (m n : ℕ)
    (C : KPGlobalTorusFunctionData.JetCompact
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F))
    (v : S) (s : ℂ) (hs : s ∈ KPContinuation.spectralDomain) :
    letI : CompactSpace C.set := isCompact_iff_compactSpace.mp C.compact
    HasDerivWithinAt
      (fun t => compactParameterJet F ζ hζ ι hSmooth g m n C t v)
      (compactParameterJet F ζ hζ ι hSmooth g (m + 1) n C s v)
      KPContinuation.spectralDomain s := by
  letI : CompactSpace C.set := isCompact_iff_compactSpace.mp C.compact
  let H := fun l t z => parameterSection F ζ hζ ι l t v
    (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g)
  have hH (l : ℕ) : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry (H l))
      (Set.univ ×ˢ KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) := by
    have ha : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun p : ℂ × KPGlobalTorusBorelTwistCompatibility.GroupArch F =>
          (KPContFlatSourceRecipe.alpha F ζ hζ
            (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ p.2 * g) : ℂ))
        (Set.univ ×ˢ KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) :=
      (alpha_chart_contDiffOn F ζ hζ g).comp
      (contDiffOn_snd (s := Set.univ ×ˢ KPGlobalTorusBorelTwistCompatibility.groupArchDomain F))
      (fun p hp => hp.2)
    have hb : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun p : ℂ × KPGlobalTorusBorelTwistCompatibility.GroupArch F =>
          (ι v).val.val (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ p.2 * g))
        (Set.univ ×ˢ KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) :=
      (scalarSection_chart_contDiffOn F ζ hζ ι hSmooth v g).comp
      (contDiffOn_snd (s := Set.univ ×ˢ KPGlobalTorusBorelTwistCompatibility.groupArchDomain F))
      (fun p hp => hp.2)
    exact (ha.pow l).mul ((contDiffOn_fst.mul ha).cexp.mul hb)
  have hd (t : ℂ) (z : KPGlobalTorusBorelTwistCompatibility.GroupArch F)
      (_hz : z ∈ KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) :
      HasDerivAt (fun r => H m r z) (H (m+1) t z) t := by
    let a : ℂ := (KPContFlatSourceRecipe.alpha F ζ hζ
      (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g) : ℂ)
    let b : ℂ := (ι v).val.val
      (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g)
    have he := (((hasDerivAt_id t).mul_const a).cexp.mul_const b).const_mul (a^m)
    convert he using 1 <;> simp only [H, parameterSection, L_formula, pow_succ, a, b, id_eq] <;>
      first | (funext r; ring) | ring
  let h := fun t => compactParameterJet F ζ hζ ι hSmooth g m n C t v
  let k := fun t => compactParameterJet F ζ hζ ι hSmooth g (m+1) n C t v
  have hk : Continuous (Function.uncurry (fun t z => k t z)) := by
    have hc := parameterJet_joint_continuousOn F ζ hζ ι hSmooth g (m+1) n v
    exact hc.comp_continuous (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
      (fun p => ⟨Set.mem_univ _, C.inside p.2.property⟩)
  have hp (t : ℂ) (z : C.set) : HasDerivAt (fun r => h r z) (k t z) t := by
    have hj := jets_hasDeriv (H m) (H (m+1))
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F)
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain_open F)
      (hH m) (hH (m+1)) hd n t z.val (C.inside z.property)
    have he (r : ℂ) (l : ℕ) : parameterJet F ζ hζ ι g l n r v z.val =
        iteratedFDeriv ℝ n (H l r) z.val :=
      iteratedFDerivWithin_of_isOpen n
        (KPGlobalTorusBorelTwistCompatibility.groupArchDomain_open F) (C.inside z.property)
    change HasDerivAt (fun r => parameterJet F ζ hζ ι g m n r v z.val)
      (parameterJet F ζ hζ ι g (m+1) n t v z.val) t
    simp_rw [he]
    exact hj
  exact (compact_hasDeriv h k hk hp s).hasDerivWithinAt

 lemma compactParameterJet_zero
    (g : KPGlobalTorusFunctionData.G F ζ hζ) (n : ℕ)
    (C : KPGlobalTorusFunctionData.JetCompact
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F)) (s : ℂ) (v : S) :
    compactParameterJet F ζ hζ ι hSmooth g 0 n C s v =
      compactJet F ζ hζ ι hSmooth g n C s v := by
  ext z
  simp [compactParameterJet, compactJet, parameterJet, spatialJet, parameterSection]

set_option backward.isDefEq.respectTransparency.types false in
 def compactJet_linearMap
    (g : KPGlobalTorusFunctionData.G F ζ hζ) (n : ℕ)
    (C : KPGlobalTorusFunctionData.JetCompact
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F)) (s : ℂ) :
    S →ₗ[ℂ] C(C.set, JetSpace F n) where
  toFun v := compactJet F ζ hζ ι hSmooth g n C s v
  map_add' v w := by
    simp only [← compactParameterJet_zero F ζ hζ ι hSmooth g n C]
    apply ContinuousMap.ext
    intro z
    exact (parameterJet_linearMap F ζ hζ ι hSmooth g 0 n s z.val
      (C.inside z.property)).map_add v w
  map_smul' c v := by
    simp only [← compactParameterJet_zero F ζ hζ ι hSmooth g n C]
    apply ContinuousMap.ext
    intro z
    exact (parameterJet_linearMap F ζ hζ ι hSmooth g 0 n s z.val
      (C.inside z.property)).map_smul c v

theorem compactJet_holomorphic
    (_hι : Function.Injective ι) (f : ℂ → S)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (g : KPGlobalTorusFunctionData.G F ζ hζ) (n : ℕ)
    (C : KPGlobalTorusFunctionData.JetCompact
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F)) :
    letI : CompactSpace C.set := isCompact_iff_compactSpace.mp C.compact
    DifferentiableOn ℂ
      (fun s => compactJet F ζ hζ ι hSmooth g n C s (f s))
      KPContinuation.spectralDomain := by
  letI : CompactSpace C.set := isCompact_iff_compactSpace.mp C.compact
  letI : AddCommGroup C(C.set, JetSpace F n) :=
    (inferInstance : NormedAddCommGroup C(C.set, JetSpace F n)).toAddCommGroup
  letI : Module ℂ C(C.set, JetSpace F n) :=
    (inferInstance : NormedSpace ℂ C(C.set, JetSpace F n)).toModule
  letI : TopologicalSpace C(C.set, JetSpace F n) :=
    (inferInstance : MetricSpace C(C.set, JetSpace F n)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let e := Module.finBasis ℂ S
  have hfix (v : S) : DifferentiableOn ℂ
      (fun s => compactJet F ζ hζ ι hSmooth g n C s v) KPContinuation.spectralDomain := by
    intro s hs
    have hd := compactParameterJet_hasDerivWithinAt F ζ hζ ι hSmooth g 0 n C v s hs
    simp only [compactParameterJet_zero F ζ hζ ι hSmooth g n C] at hd
    exact ⟨_, hd.hasFDerivWithinAt⟩
  have hcoeff (i : Fin (Module.finrank ℂ S)) :
      DifferentiableOn ℂ (fun s => e.equivFunL (f s) i) KPContinuation.spectralDomain :=
    ((ContinuousLinearMap.proj i).comp e.equivFunL.toContinuousLinearMap).differentiable.comp_differentiableOn hf
  have heq (s : ℂ) : compactJet F ζ hζ ι hSmooth g n C s (f s) =
      ∑ i, e.equivFunL (f s) i • compactJet F ζ hζ ι hSmooth g n C s (e i) := by
    change compactJet_linearMap F ζ hζ ι hSmooth g n C s (f s) =
      ∑ i, e.equivFunL (f s) i • compactJet_linearMap F ζ hζ ι hSmooth g n C s (e i)
    simp_rw [← (compactJet_linearMap F ζ hζ ι hSmooth g n C s).map_smul]
    rw [← map_sum]
    congr 1
    exact (e.sum_equivFun (f s)).symm
  apply DifferentiableOn.congr (f := fun s =>
    ∑ i, e.equivFunL (f s) i • compactJet F ζ hζ ι hSmooth g n C s (e i))
  · convert (DifferentiableOn.sum (u := Finset.univ)
      (fun i _ => (hcoeff i).smul (hfix (e i)))) using 1 <;>
      simp only [Finset.sum_apply, Finset.sum_fn, Pi.smul_apply]
    funext s
    rfl
  · intro s hs
    exact heq s

end DedekindZetaZeroFree.KPContFlatStageJetHolomorphy

end
