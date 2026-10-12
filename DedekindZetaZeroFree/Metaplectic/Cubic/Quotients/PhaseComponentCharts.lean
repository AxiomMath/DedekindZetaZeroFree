module

public import DedekindZetaZeroFree.Metaplectic.Cubic.LineBundles.GenuineScalarDescent

@[expose] public section

noncomputable section
open scoped Classical NumberField

namespace DedekindZetaZeroFree.KPContSectorPhaseComponentCharts

open KPContSectorCoveredQuotientVocabulary

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)

def centralLevel : Subgroup (rootsOfUnity 3 F) :=
  U.toOpenSubgroup.toSubgroup.comap (KPCuspGenuineMonodromy.central F ζ hζ)

abbrev PhaseSheets := (rootsOfUnity 3 F) ⧸ centralLevel F ζ hζ U

instance instTopologicalSpacePhaseSheets : TopologicalSpace (PhaseSheets F ζ hζ U) := ⊥
instance instDiscreteTopologyPhaseSheets : DiscreteTopology (PhaseSheets F ζ hζ U) := ⟨rfl⟩
instance instFinitePhaseSheets : Finite (PhaseSheets F ζ hζ U) := by
  letI : NeZero (3 : ℕ) := ⟨by norm_num⟩
  infer_instance

def phaseClass : rootsOfUnity 3 F →* PhaseSheets F ζ hζ U :=
  QuotientGroup.mk' (centralLevel F ζ hζ U)

variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

abbrev Component (i : Fin (H.atlas U).componentCount) :=
  KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i)

instance instMulActionPhaseProduct (i : Fin (H.atlas U).componentCount) :
    MulAction (Component F ζ hζ U R P H i)
      (PhaseSheets F ζ hζ U × SymmetricSpace F) where
  smul γ p := (p.1 * phaseClass F ζ hζ U (((H.atlas U).line i).rho γ)⁻¹,
    (γ : KPCuspArithmetic.PGL2 F) • p.2)
  one_smul := by
    intro p
    apply Prod.ext
    · change p.1 * phaseClass F ζ hζ U (((H.atlas U).line i).rho 1)⁻¹ = p.1
      simp
    · exact one_smul _ _
  mul_smul := by
    intro γ δ p
    apply Prod.ext
    · change p.1 * phaseClass F ζ hζ U (((H.atlas U).line i).rho (γ * δ))⁻¹ =
        (p.1 * phaseClass F ζ hζ U (((H.atlas U).line i).rho δ)⁻¹) *
          phaseClass F ζ hζ U (((H.atlas U).line i).rho γ)⁻¹
      simp only [map_mul, mul_inv_rev, mul_assoc]
    · exact mul_smul (γ : KPCuspArithmetic.PGL2 F) (δ : KPCuspArithmetic.PGL2 F) p.2

abbrev PhaseComponent (i : Fin (H.atlas U).componentCount) :=
  Quotient (MulAction.orbitRel (Component F ζ hζ U R P H i)
    (PhaseSheets F ζ hζ U × SymmetricSpace F))

abbrev PhaseModel := Σ i : Fin (H.atlas U).componentCount,
  PhaseComponent F ζ hζ U R P H i

def forgetPhase (i : Fin (H.atlas U).componentCount) :
    PhaseComponent F ζ hζ U R P H i →
      KPCuspSiegel.OrbitQuotient F (Component F ζ hζ U R P H i) :=
  Quotient.map Prod.snd (by
    intro p q h
    change p ∈ MulAction.orbit (Component F ζ hζ U R P H i) q at h
    change p.2 ∈ MulAction.orbit (Component F ζ hζ U R P H i) q.2
    rw [MulAction.mem_orbit_iff] at h ⊢
    obtain ⟨γ, hγ⟩ := h
    refine ⟨γ, ?_⟩
    rw [← hγ]
    rfl)

 theorem phaseShift_rel (i : Fin (H.atlas U).componentCount)
    (ε : rootsOfUnity 3 F) (p q : PhaseSheets F ζ hζ U × SymmetricSpace F)
    (h : MulAction.orbitRel (Component F ζ hζ U R P H i)
      (PhaseSheets F ζ hζ U × SymmetricSpace F) p q) :
    MulAction.orbitRel (Component F ζ hζ U R P H i)
      (PhaseSheets F ζ hζ U × SymmetricSpace F)
      (phaseClass F ζ hζ U ε * p.1, p.2)
      (phaseClass F ζ hζ U ε * q.1, q.2) := by
  change p ∈ MulAction.orbit (Component F ζ hζ U R P H i) q at h
  change (phaseClass F ζ hζ U ε * p.1, p.2) ∈
    MulAction.orbit (Component F ζ hζ U R P H i)
      (phaseClass F ζ hζ U ε * q.1, q.2)
  rw [MulAction.mem_orbit_iff] at h ⊢
  obtain ⟨γ, hγ⟩ := h
  refine ⟨γ, ?_⟩
  rw [← hγ]
  apply Prod.ext
  · show phaseClass F ζ hζ U ε * q.1 *
        phaseClass F ζ hζ U (((H.atlas U).line i).rho γ)⁻¹ =
      phaseClass F ζ hζ U ε *
        (q.1 * phaseClass F ζ hζ U (((H.atlas U).line i).rho γ)⁻¹)
    rw [mul_assoc]
  · rfl

def residualPhase (ε : rootsOfUnity 3 F) (i : Fin (H.atlas U).componentCount) :
    PhaseComponent F ζ hζ U R P H i ≃ₜ PhaseComponent F ζ hζ U R P H i where
  toFun := Quotient.map (fun p => (phaseClass F ζ hζ U ε * p.1, p.2))
    (fun a b h => phaseShift_rel F ζ hζ U R P H i ε a b h)
  invFun := Quotient.map (fun p => (phaseClass F ζ hζ U ε⁻¹ * p.1, p.2))
    (fun a b h => phaseShift_rel F ζ hζ U R P H i ε⁻¹ a b h)
  left_inv := by
    intro x
    induction x using Quotient.inductionOn with
    | h p =>
      apply Quotient.sound
      change (phaseClass F ζ hζ U ε⁻¹ * (phaseClass F ζ hζ U ε * p.1), p.2) ∈
        MulAction.orbit (Component F ζ hζ U R P H i) p
      rw [MulAction.mem_orbit_iff]
      refine ⟨1, ?_⟩
      rw [one_smul]
      apply Prod.ext
      · show p.1 = phaseClass F ζ hζ U ε⁻¹ * (phaseClass F ζ hζ U ε * p.1)
        rw [← mul_assoc, map_inv, inv_mul_cancel, one_mul]
      · rfl
  right_inv := by
    intro x
    induction x using Quotient.inductionOn with
    | h p =>
      apply Quotient.sound
      change (phaseClass F ζ hζ U ε * (phaseClass F ζ hζ U ε⁻¹ * p.1), p.2) ∈
        MulAction.orbit (Component F ζ hζ U R P H i) p
      rw [MulAction.mem_orbit_iff]
      refine ⟨1, ?_⟩
      rw [one_smul]
      apply Prod.ext
      · show p.1 = phaseClass F ζ hζ U ε * (phaseClass F ζ hζ U ε⁻¹ * p.1)
        rw [← mul_assoc, map_inv, mul_inv_cancel, one_mul]
      · rfl
  continuous_toFun := continuous_quot_map
    (fun a b h => phaseShift_rel F ζ hζ U R P H i ε a b h) (by fun_prop)
  continuous_invFun := continuous_quot_map
    (fun a b h => phaseShift_rel F ζ hζ U R P H i ε⁻¹ a b h) (by fun_prop)

private theorem central_comm (ε : rootsOfUnity 3 F) (c : FiniteCover F ζ hζ) :
    KPCuspGenuineMonodromy.central F ζ hζ ε * c =
      c * KPCuspGenuineMonodromy.central F ζ hζ ε := by
  apply Subtype.ext
  exact (Subgroup.mem_center_iff.mp
    (KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ
      ⟨ε, rfl⟩) c).symm

 theorem phase_rel_forward (i : Fin (H.atlas U).componentCount)
    (ε δ : rootsOfUnity 3 F) (x y : SymmetricSpace F)
    (h : MulAction.orbitRel (Component F ζ hζ U R P H i)
      (PhaseSheets F ζ hζ U × SymmetricSpace F)
      (phaseClass F ζ hζ U ε, x) (phaseClass F ζ hζ U δ, y)) :
    (coveredRelation F ζ hζ U).r
      (x, KPCuspGenuineMonodromy.central F ζ hζ ε * (H.atlas U).representative i)
      (y, KPCuspGenuineMonodromy.central F ζ hζ δ * (H.atlas U).representative i) := by
  obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp
    (MulAction.orbitRel_apply.mp ((MulAction.orbitRel _ _).symm h))
  have hm := congrArg Prod.fst hγ
  have hx := congrArg Prod.snd hγ
  change phaseClass F ζ hζ U ε * phaseClass F ζ hζ U (((H.atlas U).line i).rho γ)⁻¹ =
    phaseClass F ζ hζ U δ at hm
  rw [← map_mul] at hm
  change QuotientGroup.mk' (centralLevel F ζ hζ U) _ =
    QuotientGroup.mk' (centralLevel F ζ hζ U) δ at hm
  rw [QuotientGroup.mk'_eq_mk'] at hm
  obtain ⟨η, hη, he⟩ := hm
  obtain ⟨u, hu⟩ := ((H.atlas U).line i).finite_comparison γ
  let c : U.toOpenSubgroup := ⟨KPCuspGenuineMonodromy.central F ζ hζ η, hη⟩
  refine ⟨γ.val, u⁻¹ * c, hx.symm, ?_⟩
  change KPCuspGenuineMonodromy.central F ζ hζ δ * (H.atlas U).representative i =
    KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ *
      (KPCuspGenuineMonodromy.central F ζ hζ ε * (H.atlas U).representative i) * ↑(u⁻¹ * c)
  rw [← mul_assoc (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ)]
  rw [← central_comm F ζ hζ ε (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ)]
  rw [mul_assoc (KPCuspGenuineMonodromy.central F ζ hζ ε)
    (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ), hu]
  change _ = KPCuspGenuineMonodromy.central F ζ hζ ε *
    (KPCuspGenuineMonodromy.central F ζ hζ (((H.atlas U).line i).rho γ)⁻¹ *
      (H.atlas U).representative i * u) *
        ((↑u : FiniteCover F ζ hζ)⁻¹ * KPCuspGenuineMonodromy.central F ζ hζ η)
  simp only [mul_assoc, mul_inv_cancel_left]
  rw [← central_comm F ζ hζ η ((H.atlas U).representative i)]
  rw [← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, he]

private theorem phase_rel_backward (i : Fin (H.atlas U).componentCount)
    (ε δ : rootsOfUnity 3 F) (x y : SymmetricSpace F)
    (h : (coveredRelation F ζ hζ U).r
      (x, KPCuspGenuineMonodromy.central F ζ hζ ε * (H.atlas U).representative i)
      (y, KPCuspGenuineMonodromy.central F ζ hζ δ * (H.atlas U).representative i)) :
    MulAction.orbitRel (Component F ζ hζ U R P H i)
      (PhaseSheets F ζ hζ U × SymmetricSpace F)
      (phaseClass F ζ hζ U ε, x) (phaseClass F ζ hζ U δ, y) := by
  obtain ⟨γ, u, hx, hc⟩ := h
  change y = γ • x at hx
  change KPCuspGenuineMonodromy.central F ζ hζ δ * (H.atlas U).representative i =
    KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ *
      (KPCuspGenuineMonodromy.central F ζ hζ ε * (H.atlas U).representative i) * u at hc
  have hz (η : rootsOfUnity 3 F) :
      KPCuspGenuineMonodromy.finiteBase F ζ hζ (KPCuspGenuineMonodromy.central F ζ hζ η) = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [← (KPCuspGenuineMonodromy.finite_cover_exact F ζ hζ).2.1]
    exact ⟨η, rfl⟩
  have hp := congrArg (KPCuspGenuineMonodromy.finiteBase F ζ hζ) hc
  simp only [map_mul, hz, one_mul] at hp
  rw [← MonoidHom.comp_apply,
    (KPCuspGenuineMonodromy.finite_cover_exact F ζ hζ).2.2.2.1] at hp
  have hγ : γ ∈ Component F ζ hζ U R P H i := by
    change KPFiniteComponents.diagonal F γ ∈
      (U.toOpenSubgroup.toSubgroup.map (KPCuspGenuineMonodromy.finiteBase F ζ hζ)).map
        (MulAut.conj (KPCuspGenuineMonodromy.finiteBase F ζ hζ ((H.atlas U).representative i))).toMonoidHom
    refine ⟨KPCuspGenuineMonodromy.finiteBase F ζ hζ u⁻¹, ⟨u⁻¹, u⁻¹.property, rfl⟩, ?_⟩
    change KPCuspGenuineMonodromy.finiteBase F ζ hζ ((H.atlas U).representative i) *
      KPCuspGenuineMonodromy.finiteBase F ζ hζ u⁻¹ *
        (KPCuspGenuineMonodromy.finiteBase F ζ hζ ((H.atlas U).representative i))⁻¹ = _
    rw [map_inv]
    have he := congrArg (fun z => z *
      (KPCuspGenuineMonodromy.finiteBase F ζ hζ u)⁻¹ *
        (KPCuspGenuineMonodromy.finiteBase F ζ hζ ((H.atlas U).representative i))⁻¹) hp
    simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using he
  let g : Component F ζ hζ U R P H i := ⟨γ, hγ⟩
  obtain ⟨v, hv⟩ := ((H.atlas U).line i).finite_comparison g
  have he : KPCuspGenuineMonodromy.central F ζ hζ δ =
      KPCuspGenuineMonodromy.central F ζ hζ (ε * (((H.atlas U).line i).rho g)⁻¹) *
        ((v : FiniteCover F ζ hζ) * u) := by
    rw [← mul_assoc (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ),
      ← central_comm F ζ hζ ε] at hc
    rw [mul_assoc (KPCuspGenuineMonodromy.central F ζ hζ ε)
      (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ), hv] at hc
    rw [← mul_assoc, ← mul_assoc, ← map_mul] at hc
    rw [central_comm F ζ hζ (ε * (((H.atlas U).line i).rho g)⁻¹),
      central_comm F ζ hζ δ ((H.atlas U).representative i), mul_assoc] at hc
    exact mul_left_cancel (by simpa only [mul_assoc] using hc)
  have hm : phaseClass F ζ hζ U ε *
      phaseClass F ζ hζ U (((H.atlas U).line i).rho g)⁻¹ = phaseClass F ζ hζ U δ := by
    rw [← map_mul]
    apply (QuotientGroup.mk'_eq_mk' (centralLevel F ζ hζ U)).mpr
    refine ⟨(ε * (((H.atlas U).line i).rho g)⁻¹)⁻¹ * δ, ?_, mul_inv_cancel_left _ _⟩
    change KPCuspGenuineMonodromy.central F ζ hζ _ ∈ U.toOpenSubgroup
    rw [map_mul, map_inv, he, inv_mul_cancel_left]
    exact U.toOpenSubgroup.mul_mem v.property u.property
  apply (MulAction.orbitRel _ _).symm
  apply MulAction.orbitRel_apply.mpr
  apply MulAction.mem_orbit_iff.mpr
  refine ⟨g, ?_⟩
  apply Prod.ext
  · exact hm
  · exact hx.symm

 theorem out_class (m : PhaseSheets F ζ hζ U) :
    phaseClass F ζ hζ U m.out = m := Quotient.out_eq m

 def forward (i : Fin (H.atlas U).componentCount) :
    PhaseComponent F ζ hζ U R P H i → CoveredSpherical F ζ hζ U :=
  Quotient.lift (fun p => Quotient.mk (coveredRelation F ζ hζ U)
    (p.2, KPCuspGenuineMonodromy.central F ζ hζ p.1.out * (H.atlas U).representative i)) (by
      intro p r h
      apply Quotient.sound
      apply phase_rel_forward F ζ hζ U R P H i
      simpa only [out_class] using h)

private theorem forward_mk (i : Fin (H.atlas U).componentCount) (ε : rootsOfUnity 3 F)
    (x : SymmetricSpace F) :
    forward F ζ hζ U R P H i (Quotient.mk _ (phaseClass F ζ hζ U ε,x)) =
      Quotient.mk (coveredRelation F ζ hζ U)
        (x, KPCuspGenuineMonodromy.central F ζ hζ ε * (H.atlas U).representative i) := by
  apply Quotient.sound
  apply phase_rel_forward F ζ hζ U R P H i
  rw [out_class]

 theorem forward_continuous (i : Fin (H.atlas U).componentCount) :
    Continuous (forward F ζ hζ U R P H i) := by
  apply Continuous.quotient_lift
  apply continuous_quot_mk.comp
  apply Continuous.prodMk continuous_snd
  have ho : Continuous (fun m : PhaseSheets F ζ hζ U =>
      KPCuspGenuineMonodromy.central F ζ hζ m.out * (H.atlas U).representative i) :=
    continuous_of_discreteTopology
  exact ho.comp continuous_fst

 theorem forward_forget (i : Fin (H.atlas U).componentCount)
    (v : PhaseComponent F ζ hζ U R P H i) :
    q F ζ hζ U (forward F ζ hζ U R P H i v) =
      (H.atlas U).components ⟨i, forgetPhase F ζ hζ U R P H i v⟩ := by
  induction v using Quotient.inductionOn with
  | h p =>
    change q F ζ hζ U (Quotient.mk _ (p.2,
      KPCuspGenuineMonodromy.central F ζ hζ p.1.out * (H.atlas U).representative i)) = _
    rw [← z_mk, q_z, q_mk, (H.atlas U).components_formula]
    rfl

 def globalForward : PhaseModel F ζ hζ U R P H → CoveredSpherical F ζ hζ U :=
  fun v => forward F ζ hζ U R P H v.1 v.2

 theorem global_injective : Function.Injective (globalForward F ζ hζ U R P H) := by
  rintro ⟨i,v⟩ ⟨j,w⟩ he
  have hf := congrArg (q F ζ hζ U) he
  rw [globalForward, globalForward, forward_forget, forward_forget] at hf
  have hij := congrArg Sigma.fst ((H.atlas U).components.injective hf)
  dsimp at hij
  subst j
  congr 1
  induction v using Quotient.inductionOn with
  | h p =>
    induction w using Quotient.inductionOn with
    | h r =>
      apply Quotient.sound
      have hr := Quotient.exact he
      have hp := phase_rel_backward F ζ hζ U R P H i p.1.out r.1.out p.2 r.2 hr
      simpa only [out_class] using hp

 theorem global_surjective : Function.Surjective (globalForward F ζ hζ U R P H) := by
  intro w
  obtain ⟨⟨i,v⟩, hv⟩ := (H.atlas U).components.surjective (q F ζ hζ U w)
  induction v using Quotient.inductionOn with
  | h x =>
    let v : PhaseComponent F ζ hζ U R P H i := Quotient.mk _ (phaseClass F ζ hζ U 1,x)
    have hq : q F ζ hζ U (forward F ζ hζ U R P H i v) = q F ζ hζ U w := by
      rw [forward_forget]
      exact hv
    obtain ⟨ε, hε⟩ := (KPContSectorQuotientRelationsComparison.q_eq_iff F ζ hζ U _ _).mp hq
    refine ⟨⟨i, Quotient.mk _ (phaseClass F ζ hζ U ε,x)⟩, ?_⟩
    rw [globalForward, forward_mk, hε]
    rw [show forward F ζ hζ U R P H i v =
      Quotient.mk (coveredRelation F ζ hζ U) (x,(H.atlas U).representative i) by
        rw [forward_mk]; simp, z_mk]
private theorem forget_continuous (i : Fin (H.atlas U).componentCount) :
    Continuous (forgetPhase F ζ hζ U R P H i) :=
  by
    apply Continuous.quotient_lift
    exact continuous_quot_mk.comp continuous_snd

private theorem forget_closed (i : Fin (H.atlas U).componentCount) :
    IsClosedMap (forgetPhase F ζ hζ U R P H i) := by
  intro s hs
  letI := MulAction.orbitRel (Component F ζ hζ U R P H i) (SymmetricSpace F)
  letI := MulAction.orbitRel (Component F ζ hζ U R P H i)
    (PhaseSheets F ζ hζ U × SymmetricSpace F)
  apply (isQuotientMap_quotient_mk'.isCoinducing.isClosed_preimage).mp
  have he : (Quotient.mk' : SymmetricSpace F → KPCuspSiegel.OrbitQuotient F
      (Component F ζ hζ U R P H i)) ⁻¹' (forgetPhase F ζ hζ U R P H i '' s) =
      Prod.snd '' ((Quotient.mk' : PhaseSheets F ζ hζ U × SymmetricSpace F →
        PhaseComponent F ζ hζ U R P H i) ⁻¹' s) := by
    ext x
    constructor
    · rintro ⟨v, hv, he⟩
      induction v using Quotient.inductionOn with
      | h p =>
        obtain ⟨γ, hγ⟩ := Quotient.exact he.symm
        refine ⟨γ • p, ?_, ?_⟩
        · have hq : Quotient.mk' (γ • p) = Quotient.mk' p :=
            Quotient.sound ⟨γ, rfl⟩
          change Quotient.mk' (γ • p) ∈ s
          rw [hq]
          exact hv
        · exact hγ
    · rintro ⟨p, hp, rfl⟩
      exact ⟨Quotient.mk' p, hp, rfl⟩
  rw [he]
  exact isClosedMap_snd_of_compactSpace _ (hs.preimage continuous_quot_mk)

private theorem forget_fiber_finite (i : Fin (H.atlas U).componentCount)
    (v : KPCuspSiegel.OrbitQuotient F (Component F ζ hζ U R P H i)) :
    (forgetPhase F ζ hζ U R P H i ⁻¹' {v}).Finite := by
  induction v using Quotient.inductionOn with
  | h x =>
    letI := MulAction.orbitRel (Component F ζ hζ U R P H i)
      (PhaseSheets F ζ hζ U × SymmetricSpace F)
    apply (Set.finite_range (fun m : PhaseSheets F ζ hζ U =>
      (Quotient.mk' (m,x) : PhaseComponent F ζ hζ U R P H i))).subset
    intro w hw
    induction w using Quotient.inductionOn with
    | h p =>
      obtain ⟨γ, hγ⟩ := Quotient.exact (Set.mem_singleton_iff.mp hw).symm
      refine ⟨(γ • p).1, ?_⟩
      have hpair : ((γ • p).1,x) = γ • p := Prod.ext rfl hγ.symm
      change Quotient.mk' ((γ • p).1,x) = Quotient.mk' p
      rw [hpair]
      exact Quotient.sound ⟨γ,rfl⟩

 def globalForget : PhaseModel F ζ hζ U R P H → KPFiniteCuspAtlas.rawXU F ζ hζ U :=
  fun v => (H.atlas U).components ⟨v.1, forgetPhase F ζ hζ U R P H v.1 v.2⟩

 theorem globalForget_proper : IsProperMap (globalForget F ζ hζ U R P H) := by
  let f : PhaseModel F ζ hζ U R P H →
      (Σ i : Fin (H.atlas U).componentCount,
        KPCuspSiegel.OrbitQuotient F (Component F ζ hζ U R P H i)) :=
    fun v => ⟨v.1, forgetPhase F ζ hζ U R P H v.1 v.2⟩
  have hfc : Continuous f := by
    apply continuous_sigma
    intro i
    exact continuous_sigmaMk.comp (forget_continuous F ζ hζ U R P H i)
  have hfcl : IsClosedMap f := by
    intro s hs
    rw [isClosed_sigma_iff]
    intro i
    have he : Sigma.mk i ⁻¹' (f '' s) =
        forgetPhase F ζ hζ U R P H i '' (Sigma.mk i ⁻¹' s) := by
      ext v
      constructor
      · rintro ⟨⟨j,w⟩, hw, he⟩
        have hij := congrArg Sigma.fst he
        dsimp [f] at hij
        subst j
        exact ⟨w, hw, eq_of_heq (Sigma.mk.inj he).2⟩
      · rintro ⟨w, hw, rfl⟩
        exact ⟨⟨i,w⟩, hw, rfl⟩
    rw [he]
    exact forget_closed F ζ hζ U R P H i _ (hs.preimage continuous_sigmaMk)
  have hff (v : Σ i : Fin (H.atlas U).componentCount,
      KPCuspSiegel.OrbitQuotient F (Component F ζ hζ U R P H i)) :
      (f ⁻¹' {v}).Finite := by
    obtain ⟨i,v⟩ := v
    apply ((forget_fiber_finite F ζ hζ U R P H i v).image (Sigma.mk i)).subset
    rintro ⟨j,w⟩ hw
    have he := Set.mem_singleton_iff.mp hw
    have hij := congrArg Sigma.fst he
    dsimp [f] at hij
    subst j
    exact ⟨w, eq_of_heq (Sigma.mk.inj he).2, rfl⟩
  have hfp : IsProperMap f := isProperMap_iff_isClosedMap_and_compact_fibers.mpr
    ⟨hfc, hfcl, fun v => (hff v).isCompact⟩
  exact (H.atlas U).components.isProperMap.comp hfp

 def actualHomeomorph : PhaseModel F ζ hζ U R P H ≃ₜ CoveredSpherical F ζ hζ U := by
  have hf : Continuous (globalForward F ζ hζ U R P H) := by
    apply continuous_sigma
    intro i
    exact forward_continuous F ζ hζ U R P H i
  have hp : IsProperMap (globalForward F ζ hζ U R P H) := by
    apply isProperMap_of_comp_of_t2 hf (KPContSectorQuotientRelationsComparison.q_continuous F ζ hζ U)
    convert globalForget_proper F ζ hζ U R P H using 1
    funext v
    exact forward_forget F ζ hζ U R P H v.1 v.2
  exact (Equiv.ofBijective (globalForward F ζ hζ U R P H)
    ⟨global_injective F ζ hζ U R P H, global_surjective F ζ hζ U R P H⟩).toHomeomorphOfContinuousClosed hf hp.isClosedMap

def componentHomeomorph : PhaseModel F ζ hζ U R P H ≃ₜ CoveredSpherical F ζ hζ U :=
  actualHomeomorph F ζ hζ U R P H

theorem componentHomeomorph_mk (i : Fin (H.atlas U).componentCount)
    (ε : rootsOfUnity 3 F) (x : SymmetricSpace F) :
    componentHomeomorph F ζ hζ U R P H
      ⟨i, Quotient.mk _ (phaseClass F ζ hζ U ε, x)⟩ =
        Quotient.mk (coveredRelation F ζ hζ U)
          (x, KPCuspGenuineMonodromy.central F ζ hζ ε * (H.atlas U).representative i) := by
  exact forward_mk F ζ hζ U R P H i ε x

theorem componentHomeomorph_forget (i : Fin (H.atlas U).componentCount)
    (v : PhaseComponent F ζ hζ U R P H i) :
    q F ζ hζ U (componentHomeomorph F ζ hζ U R P H ⟨i,v⟩) =
      (H.atlas U).components ⟨i, forgetPhase F ζ hζ U R P H i v⟩ := by
  induction v using Quotient.inductionOn with
  | h p =>
    obtain ⟨m, x⟩ := p
    induction m using Quotient.inductionOn with
    | h ε =>
      change q F ζ hζ U (componentHomeomorph F ζ hζ U R P H
        ⟨i, Quotient.mk _ (phaseClass F ζ hζ U ε, x)⟩) = _
      rw [componentHomeomorph_mk]
      rw [← z_mk, q_z, q_mk]
      rw [(H.atlas U).components_formula]
      rfl

def complexProjectiveEmbedding : KPCuspArithmetic.PGL2 F →*
    KPArithmeticAction.ProjectiveGroup (KPCuspLogShape.dimension F) where
  toFun γ j := Matrix.ProjGenLinGroup.map (KPCusp.complexPlace F j).embedding γ
  map_one' := by funext j; simp
  map_mul' γ δ := by funext j; simp

theorem complexProjectiveEmbedding_smul (γ : KPCuspArithmetic.PGL2 F)
    (x : SymmetricSpace F) :
    complexProjectiveEmbedding F γ • x = γ • x := by
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective γ
  funext j
  show Matrix.ProjGenLinGroup.mk
      (Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F j).embedding A) • x j =
    (KPCuspSiegel.action F (Matrix.ProjGenLinGroup.mk A) x) j
  rw [KPCuspSiegel.action_mk, KPCuspSiegel.glAction, KPArch.productAction]
  rfl

private theorem pglmap_inj (f : F →+* ℂ) :
    Function.Injective (Matrix.ProjGenLinGroup.map (n := Fin 2) f) := by
  have hi : Function.Injective (Matrix.GeneralLinearGroup.map (n := Fin 2) f) := by
    intro a b h
    apply Units.ext
    ext i j
    apply f.injective
    exact congrArg (fun g : Matrix.GeneralLinearGroup (Fin 2) ℂ => g i j) h
  apply (Matrix.ProjGenLinGroup.map f).ker_eq_bot_iff.mp
  apply bot_unique
  intro g hg
  obtain ⟨a, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  change Matrix.ProjGenLinGroup.map f (Matrix.ProjGenLinGroup.mk a) = 1 at hg
  rw [Matrix.ProjGenLinGroup.map_mk, Matrix.ProjGenLinGroup.mk_eq_one] at hg
  have ha : a ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) F) := by
    rw [Subgroup.mem_center_iff]
    intro b
    apply hi
    simpa only [map_mul] using
      (Subgroup.mem_center_iff.mp hg (Matrix.GeneralLinearGroup.map f b))
  simpa only [Subgroup.mem_bot, Matrix.ProjGenLinGroup.mk_eq_one] using ha

include ζ hζ in
theorem complexProjectiveEmbedding_injective :
    Function.Injective (complexProjectiveEmbedding F) := by
  have hd : 0 < KPCuspLogShape.dimension F :=
    KPCuspLogShape.dimension_pos F
      (NumberField.nrRealPlaces_eq_zero_iff.mpr
        (primitive12_totallyComplex F ζ hζ))
  intro γ δ h
  exact pglmap_inj F (KPCusp.complexPlace F ⟨0, hd⟩).embedding
    (congrFun h ⟨0, hd⟩)

abbrev ArchComponent (i : Fin (H.atlas U).componentCount) :=
  (Component F ζ hζ U R P H i).map (complexProjectiveEmbedding F)

abbrev OrbifoldChart (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F) :=
  KPArithmeticAction.OrbifoldChart (KPCuspLogShape.dimension F)
    (ArchComponent F ζ hζ U R P H i) x

private theorem archproper (i : Fin (H.atlas U).componentCount) :
    ProperlyDiscontinuousSMul (ArchComponent F ζ hζ U R P H i) (SymmetricSpace F) := by
  letI : ProperlyDiscontinuousSMul (Component F ζ hζ U R P H i) (SymmetricSpace F) :=
    KPFiniteAdelicCuspEnds.FundamentalDomainGeometry.arithmeticStabilizer_properlyDiscontinuous_of_compact
      F H.totallyComplex _ (KPCuspGenuineMonodromy.finiteBase_level_compact F ζ hζ U) _
  let e := (Component F ζ hζ U R P H i).equivMapOfInjective
    (complexProjectiveEmbedding F) (complexProjectiveEmbedding_injective F ζ hζ)
  constructor
  intro K L hK hL
  have hs := ProperlyDiscontinuousSMul.finite_disjoint_inter_image
    (Γ := Component F ζ hζ U R P H i) hK hL
  apply (hs.image e).subset
  intro γ hγ
  refine ⟨e.symm γ, ?_, e.apply_symm_apply γ⟩
  have he : complexProjectiveEmbedding F (e.symm γ).val = γ.val :=
    congrArg Subtype.val (e.apply_symm_apply γ)
  have ha : (fun y : SymmetricSpace F => (e.symm γ : KPCuspArithmetic.PGL2 F) • y) =
      fun y => γ • y := by
    funext y
    rw [← complexProjectiveEmbedding_smul, he]
    rfl
  change ((fun y => (e.symm γ : KPCuspArithmetic.PGL2 F) • y) '' K ∩ L).Nonempty
  rw [ha]
  exact hγ
private theorem chart_from_proper (d : ℕ) (Γ : Subgroup (KPArithmeticAction.ProjectiveGroup d))
    [ProperlyDiscontinuousSMul Γ (KPArch.Space d)] (z : KPArch.Space d) :
    Nonempty (KPArithmeticAction.OrbifoldChart d Γ z) := by
  letI : Finite (MulAction.stabilizer Γ z) := ProperlyDiscontinuousSMul.finite_stabilizer z
  let H := MulAction.stabilizer Γ z
  letI : ContinuousConstSMul Γ (KPArch.Space (d)) :=
    ⟨fun g => continuous_const_smul (Γ := KPArithmeticAction.ProjectiveGroup (d)) g.val⟩
  letI : ContinuousConstSMul H (KPArch.Space (d)) :=
    ⟨fun h => continuous_const_smul (Γ := Γ) h.val⟩
  obtain ⟨W, hW, hsep⟩ := ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self Γ z
  obtain ⟨V, hVW, hVo, hzV⟩ := mem_nhds_iff.1 hW
  let U : Set (KPArch.Space (d)) := ⋂ h : H, (fun w => h • w) ⁻¹' V
  have hUo : IsOpen U := isOpen_iInter_of_finite (fun h => hVo.preimage (continuous_const_smul h))
  have hzU : z ∈ U := by
    simp only [U, Set.mem_iInter, Set.mem_preimage]
    intro h
    change h.val • z ∈ V
    rw [MulAction.mem_stabilizer_iff.1 h.property]
    exact hzV
  have hUV : U ⊆ V := by
    intro w hw
    simpa using Set.mem_iInter.1 hw (1 : H)
  have hUi (h : H) : (fun w : KPArch.Space (d) => h • w) '' U = U := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      apply Set.mem_iInter.2
      intro k
      simpa only [Set.mem_preimage, mul_smul] using Set.mem_iInter.1 hv (k * h)
    · intro hw
      refine ⟨h⁻¹ • w, ?_, by simp⟩
      apply Set.mem_iInter.2
      intro k
      simpa only [Set.mem_preimage, mul_smul] using Set.mem_iInter.1 hw (k * h⁻¹)
  have hUs (g : Γ) (hg : ((fun w => g • w) '' U ∩ U).Nonempty) : g ∈ H := by
    apply hsep g
    exact hg.mono (Set.inter_subset_inter (Set.image_mono (hUV.trans hVW)) (hUV.trans hVW))
  let q := KPArithmeticAction.orbitProjection (d) Γ
  have hqo : IsOpenMap q := isOpenMap_quotient_mk'_mul
  let f : U → q '' U := fun w => ⟨q w.val, Set.mem_image_of_mem _ w.property⟩
  have hfo : IsOpenMap f := (hqo.comp hUo.isOpenMap_subtype_val).subtype_mk _
  have hfc : Continuous f := (continuous_quot_mk.comp continuous_subtype_val).subtype_mk _
  have hfs : Function.Surjective f := by
    rintro ⟨y, w, hw, rfl⟩
    exact ⟨⟨w, hw⟩, rfl⟩
  have hker : KPArithmeticAction.localOrbitRel (d) Γ z U = Setoid.ker f := by
    ext v w
    change (∃ h : H, h • w.val = v.val) ↔ f v = f w
    constructor
    · rintro ⟨h, hh⟩
      apply Subtype.ext
      exact Quotient.sound ⟨h.val, hh⟩
    · intro he
      have he' : q v.val = q w.val := congrArg Subtype.val he
      obtain ⟨g, hg⟩ := Quotient.exact he'
      have gm : g ∈ H := hUs g ⟨v.val, ⟨w.val, w.property, hg⟩, v.property⟩
      exact ⟨⟨g, gm⟩, hg⟩
  let e : Quotient (KPArithmeticAction.localOrbitRel (d) Γ z U) ≃ₜ q '' U :=
    (Homeomorph.Quotient.congrRight (fun v w => by rw [hker])).trans
      (Topology.IsQuotientMap.homeomorph (f := ⟨f, hfc⟩) (hfo.isQuotientMap hfc hfs))
  refine ⟨⟨U, hUo, hzU, inferInstance, hUi, hUs, hqo _ hUo, e, ?_⟩⟩
  intro w
  rfl

theorem orbifoldChart_exists (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F) :
    Nonempty (OrbifoldChart F ζ hζ U R P H i x) := by
  letI := archproper F ζ hζ U R P H i
  exact chart_from_proper (KPCuspLogShape.dimension F)
    (ArchComponent F ζ hζ U R P H i) x

def baseChartImage (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U) :=
  (fun v => (H.atlas U).components ⟨i,v⟩) ''
    (KPCuspSiegel.projection F (Component F ζ hζ U R P H i) '' O.neighborhood)

instance instMulActionChartProduct (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) :
    MulAction (MulAction.stabilizer (Component F ζ hζ U R P H i) x)
      (PhaseSheets F ζ hζ U × O.neighborhood) where
  smul σ p :=
    (p.1 * phaseClass F ζ hζ U (((H.atlas U).line i).rho σ.val)⁻¹,
      ⟨(σ.val : KPCuspArithmetic.PGL2 F) • p.2.val, by
        let τ : MulAction.stabilizer (ArchComponent F ζ hζ U R P H i) x :=
          ⟨⟨complexProjectiveEmbedding F σ.val.val,
            ⟨σ.val.val, σ.val.property, rfl⟩⟩, by
            change complexProjectiveEmbedding F σ.val.val • x = x
            rw [complexProjectiveEmbedding_smul]
            exact σ.property⟩
        have he := O.invariant τ
        have hy := Set.mem_image_of_mem (fun y : SymmetricSpace F => τ • y) p.2.property
        rw [he] at hy
        change complexProjectiveEmbedding F σ.val.val • p.2.val ∈ O.neighborhood at hy
        simpa only [complexProjectiveEmbedding_smul] using hy⟩)
  one_smul := by
    intro p
    apply Prod.ext
    · change p.1 * phaseClass F ζ hζ U (((H.atlas U).line i).rho 1)⁻¹ = p.1
      simp
    · apply Subtype.ext
      exact one_smul (KPCuspArithmetic.PGL2 F) p.2.val
  mul_smul := by
    intro σ τ p
    apply Prod.ext
    · change p.1 * phaseClass F ζ hζ U (((H.atlas U).line i).rho (σ.val * τ.val))⁻¹ =
        (p.1 * phaseClass F ζ hζ U (((H.atlas U).line i).rho τ.val)⁻¹) *
          phaseClass F ζ hζ U (((H.atlas U).line i).rho σ.val)⁻¹
      simp only [map_mul, mul_inv_rev, mul_assoc]
    · apply Subtype.ext
      exact mul_smul (σ.val : KPCuspArithmetic.PGL2 F)
        (τ.val : KPCuspArithmetic.PGL2 F) p.2.val

theorem chartProduct_smul (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x)
    (σ : MulAction.stabilizer (Component F ζ hζ U R P H i) x)
    (m : PhaseSheets F ζ hζ U) (y : O.neighborhood) :
    ((σ • (m,y)).1, ((σ • (m,y)).2 : SymmetricSpace F)) =
      (m * phaseClass F ζ hζ U (((H.atlas U).line i).rho σ.val)⁻¹,
        (σ.val : KPCuspArithmetic.PGL2 F) • (y : SymmetricSpace F)) := rfl

theorem chart_stabilizer_finite (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) :
    Finite (MulAction.stabilizer (Component F ζ hζ U R P H i) x) := by
  letI := O.finite_stabilizer
  let f : MulAction.stabilizer (Component F ζ hζ U R P H i) x →
      MulAction.stabilizer (ArchComponent F ζ hζ U R P H i) x := fun σ =>
    ⟨⟨complexProjectiveEmbedding F σ.val.val,
      ⟨σ.val.val, σ.val.property, rfl⟩⟩, by
      change complexProjectiveEmbedding F σ.val.val • x = x
      rw [complexProjectiveEmbedding_smul]
      exact σ.property⟩
  apply Finite.of_injective f
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  apply complexProjectiveEmbedding_injective F ζ hζ
  exact congrArg (fun σ : MulAction.stabilizer (ArchComponent F ζ hζ U R P H i) x =>
    σ.val.val) hab

abbrev CoveredChartDomain (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) :=
  Quotient (MulAction.orbitRel (MulAction.stabilizer (Component F ζ hζ U R P H i) x)
    (PhaseSheets F ζ hζ U × O.neighborhood))

 def localMap (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) : PhaseSheets F ζ hζ U × O.neighborhood →
    (q F ζ hζ U ⁻¹' baseChartImage F ζ hζ U R P H i x O) := fun p =>
  ⟨componentHomeomorph F ζ hζ U R P H ⟨i, Quotient.mk _ (p.1,p.2.val)⟩, by
    change q F ζ hζ U _ ∈ baseChartImage F ζ hζ U R P H i x O
    rw [componentHomeomorph_forget]
    exact ⟨KPCuspSiegel.projection F (Component F ζ hζ U R P H i) p.2.val,
      ⟨p.2.val,p.2.property,rfl⟩,rfl⟩⟩

 theorem localMap_cont (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) : Continuous (localMap F ζ hζ U R P H i x O) := by
  apply Continuous.subtype_mk
  apply (componentHomeomorph F ζ hζ U R P H).continuous.comp
  apply continuous_sigmaMk.comp
  exact continuous_quot_mk.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

 theorem localMap_surj (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) : Function.Surjective (localMap F ζ hζ U R P H i x O) := by
  rintro ⟨w,hw⟩
  obtain ⟨⟨j,v⟩,rfl⟩ := (componentHomeomorph F ζ hζ U R P H).surjective w
  rw [Set.mem_preimage, componentHomeomorph_forget] at hw
  obtain ⟨v',⟨y,hy,rfl⟩,he⟩ := hw
  have he' := (H.atlas U).components.injective he
  have hij := congrArg Sigma.fst he'
  dsimp at hij
  subst j
  have hv : KPCuspSiegel.projection F (Component F ζ hζ U R P H i) y =
      forgetPhase F ζ hζ U R P H i v := eq_of_heq (Sigma.mk.inj he').2
  induction v using Quotient.inductionOn with
  | h p =>
    obtain ⟨γ,hγ⟩ := Quotient.exact hv
    refine ⟨((γ • p).1,⟨y,hy⟩), ?_⟩
    apply Subtype.ext
    apply congrArg (componentHomeomorph F ζ hζ U R P H)
    congr 1
    change Quotient.mk _ ((γ • p).1,y) = Quotient.mk _ p
    have hp : ((γ • p).1,y) = γ • p := Prod.ext rfl hγ.symm
    rw [hp]
    exact Quotient.sound ⟨γ,rfl⟩

 theorem localMap_ker (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) : MulAction.orbitRel
      (MulAction.stabilizer (Component F ζ hζ U R P H i) x)
      (PhaseSheets F ζ hζ U × O.neighborhood) =
    Setoid.ker (localMap F ζ hζ U R P H i x O) := by
  ext p r
  constructor
  · intro h
    obtain ⟨σ,hσ⟩ := h
    apply Subtype.ext
    apply congrArg (componentHomeomorph F ζ hζ U R P H)
    congr 1
    apply Quotient.sound
    refine ⟨σ.val, ?_⟩
    exact congrArg (fun p : PhaseSheets F ζ hζ U × O.neighborhood => (p.1,p.2.val)) hσ
  · intro h
    have he := (componentHomeomorph F ζ hζ U R P H).injective (congrArg Subtype.val h)
    have he' : (Quotient.mk _ (p.1,p.2.val) : PhaseComponent F ζ hζ U R P H i) =
        Quotient.mk _ (r.1,r.2.val) := by
      exact eq_of_heq (Sigma.mk.inj he).2
    obtain ⟨γ,hγ⟩ := Quotient.exact he'
    let γa : ArchComponent F ζ hζ U R P H i :=
      ⟨complexProjectiveEmbedding F γ.val,⟨γ.val,γ.property,rfl⟩⟩
    have hγx : γa ∈ MulAction.stabilizer (ArchComponent F ζ hζ U R P H i) x := by
      apply O.separated γa
      refine ⟨p.2.val,⟨r.2.val,r.2.property,?_⟩,p.2.property⟩
      change complexProjectiveEmbedding F γ.val • r.2.val = p.2.val
      rw [complexProjectiveEmbedding_smul]
      exact congrArg Prod.snd hγ
    have hfix : γ ∈ MulAction.stabilizer (Component F ζ hζ U R P H i) x := by
      change γ.val • x = x
      change complexProjectiveEmbedding F γ.val • x = x at hγx
      rwa [complexProjectiveEmbedding_smul] at hγx
    refine ⟨⟨γ,hfix⟩, ?_⟩
    apply Prod.ext
    · change r.1 * phaseClass F ζ hζ U (((H.atlas U).line i).rho γ)⁻¹ = p.1
      exact congrArg Prod.fst hγ
    · apply Subtype.ext
      exact congrArg Prod.snd hγ
 theorem localMap_open (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) : IsOpenMap (localMap F ζ hζ U R P H i x O) := by
  letI : ContinuousConstSMul (Component F ζ hζ U R P H i)
      (PhaseSheets F ζ hζ U × SymmetricSpace F) := ⟨fun γ => by
    change Continuous (fun p : PhaseSheets F ζ hζ U × SymmetricSpace F =>
      (p.1 * phaseClass F ζ hζ U (((H.atlas U).line i).rho γ)⁻¹, γ.val • p.2))
    apply Continuous.prodMk
    · exact (continuous_of_discreteTopology : Continuous (fun m : PhaseSheets F ζ hζ U =>
        m * phaseClass F ζ hζ U (((H.atlas U).line i).rho γ)⁻¹)).comp continuous_fst
    · have hc : Continuous (fun y : SymmetricSpace F =>
          complexProjectiveEmbedding F γ.val • y) := continuous_const_smul _
      simpa only [Function.comp_def, complexProjectiveEmbedding_smul] using hc.comp continuous_snd⟩
  have he : IsOpenMap (fun p : PhaseSheets F ζ hζ U × O.neighborhood =>
      (p.1, p.2.val) : PhaseSheets F ζ hζ U × O.neighborhood →
        PhaseSheets F ζ hζ U × SymmetricSpace F) :=
    IsOpenMap.id.prodMap O.isOpen.isOpenMap_subtype_val
  have hq : IsOpenMap (fun p : PhaseSheets F ζ hζ U × O.neighborhood =>
      (Quotient.mk _ (p.1,p.2.val) : PhaseComponent F ζ hζ U R P H i)) :=
    isOpenMap_quotient_mk'_mul.comp he
  exact ((componentHomeomorph F ζ hζ U R P H).isOpenMap.comp
    (isOpenMap_sigmaMk.comp hq)).subtype_mk _

 def actualChart (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) : CoveredChartDomain F ζ hζ U R P H i x O ≃ₜ
    (q F ζ hζ U ⁻¹' baseChartImage F ζ hζ U R P H i x O) :=
  (Homeomorph.Quotient.congrRight (fun p r => by
    rw [localMap_ker F ζ hζ U R P H i x O])).trans
    (Topology.IsQuotientMap.homeomorph
      (f := ⟨localMap F ζ hζ U R P H i x O, localMap_cont F ζ hζ U R P H i x O⟩)
      ((localMap_open F ζ hζ U R P H i x O).isQuotientMap
        (localMap_cont F ζ hζ U R P H i x O) (localMap_surj F ζ hζ U R P H i x O)))

private theorem actualChart_mk (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) (ε : rootsOfUnity 3 F) (y : O.neighborhood) :
    (actualChart F ζ hζ U R P H i x O (Quotient.mk _ (phaseClass F ζ hζ U ε,y))).val =
      Quotient.mk (coveredRelation F ζ hζ U)
        (y.val,KPCuspGenuineMonodromy.central F ζ hζ ε * (H.atlas U).representative i) := by
  exact componentHomeomorph_mk F ζ hζ U R P H i ε y.val

def coveredChart (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) :
    CoveredChartDomain F ζ hζ U R P H i x O ≃ₜ
      (q F ζ hζ U ⁻¹' baseChartImage F ζ hζ U R P H i x O) :=
  actualChart F ζ hζ U R P H i x O

theorem coveredChart_mk (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) (ε : rootsOfUnity 3 F) (y : O.neighborhood) :
    (coveredChart F ζ hζ U R P H i x O
      (Quotient.mk _ (phaseClass F ζ hζ U ε, y))).val =
        Quotient.mk (coveredRelation F ζ hζ U)
          (y.val, KPCuspGenuineMonodromy.central F ζ hζ ε * (H.atlas U).representative i) := by
  exact actualChart_mk F ζ hζ U R P H i x O ε y

theorem baseChartImage_isOpen (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) :
    IsOpen (baseChartImage F ζ hζ U R P H i x O) := by
  letI : ContinuousConstSMul (Component F ζ hζ U R P H i) (SymmetricSpace F) :=
    ⟨fun γ => by
      change Continuous (fun y : SymmetricSpace F => γ.val • y)
      have h : Continuous (fun y : SymmetricSpace F =>
          complexProjectiveEmbedding F γ.val • y) := continuous_const_smul
        (Γ := KPArithmeticAction.ProjectiveGroup (KPCuspLogShape.dimension F))
        (complexProjectiveEmbedding F γ.val)
      simpa only [complexProjectiveEmbedding_smul] using h⟩
  have ho : IsOpen (KPCuspSiegel.projection F (Component F ζ hζ U R P H i) ''
      O.neighborhood) := isOpenMap_quotient_mk'_mul _ O.isOpen
  change IsOpen ((fun v => (H.atlas U).components (Sigma.mk i v)) '' _)
  rw [← Set.image_image]
  exact (H.atlas U).components.isOpenMap _ (isOpenMap_sigmaMk _ ho)

end DedekindZetaZeroFree.KPContSectorPhaseComponentCharts

end
