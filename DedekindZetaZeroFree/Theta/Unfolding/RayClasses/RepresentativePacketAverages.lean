module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.AffineRepresentativeCosets
public import DedekindZetaZeroFree.Theta.Unfolding.RayClasses.NormalizedDualLatticeIndices
public import DedekindZetaZeroFree.Theta.RayClasses.ResidueUnitAverages

@[expose] public section

noncomputable section

open Classical
open scoped NumberField nonZeroDivisors
open DedekindZetaZeroFree.AbelianQuotient

namespace DedekindZetaZeroFree.Hecke.Theta

variable {F : Type} [Field F] [NumberField F]

 def cosetPrimalIndexEquiv (E : RayCoset.Data F) :
    {l : F // l ∈ ((rayIdealFractionalIdeal F E.a E.ideal_ne_bot *
      rayIdealFractionalIdeal F E.m E.modulus_ne_bot) : FractionalIdeal (𝓞 F)⁰ F)} ≃
      RayCoset.normalizedLattice E := by
  let s := affineResidueScale (rayIdealFractionalIdeal F E.a E.ideal_ne_bot)
  refine Equiv.ofBijective (fun l ↦ ⟨s • Theta.traceEmbedding F l.val, ?_⟩) ⟨?_, ?_⟩
  · rw [← commonNormalizedLattice_eq_normalizedLattice E]
    exact Submodule.mem_map.mpr ⟨Theta.traceEmbedding F l.val,
      (Theta.traceEmbedding_mem_traceIdealLattice F _).mpr l.property, rfl⟩
  · intro l k he
    apply Subtype.ext
    have ht := (smul_right_injective _ (affineResidueScale_pos
      (rayIdealFractionalIdeal F E.a E.ideal_ne_bot)).ne') (congrArg Subtype.val he)
    apply NumberField.mixedEmbedding_injective F
    simpa [Theta.traceEmbedding] using congrArg (Theta.traceToMixed F) ht
  · intro v
    have hv := v.property
    have hv' : v.val ∈ commonNormalizedLattice E.m E.modulus_ne_bot
        (rayIdealFractionalIdeal F E.a E.ideal_ne_bot) := by
      simpa only [commonNormalizedLattice_eq_normalizedLattice] using hv
    obtain ⟨w, hw, he⟩ := Submodule.mem_map.mp hv'
    obtain ⟨l, hl, hle⟩ := Theta.exists_traceEmbedding_eq_of_mem_traceIdealLattice F _ hw
    exact ⟨⟨l, hl⟩, Subtype.ext (by simpa only [s, hle, LinearMap.smul_apply, LinearMap.id_apply] using he)⟩

 def cosetBasepointLift (E : RayCoset.Data F) :
    {x : F // x ∈ (rayIdealFractionalIdeal F E.a E.ideal_ne_bot : FractionalIdeal (𝓞 F)⁰ F)} :=
  ⟨(E.b : F), (FractionalIdeal.mem_coeIdeal _).mpr ⟨E.b, E.basepoint_mem, rfl⟩⟩

private theorem coset_primal_integrand (E : RayCoset.Data F)
    (u : ℝ) (h : RayCoset.logHyperplane F) :
    (∑' l : RayCoset.normalizedLattice E,
      RayParity.gδ F ∅ (RayParity.Q F (RayTheta.q F u h)
        (RayCoset.normalizedBasepoint E + (l : NumberField.mixedEmbedding.euclidean.mixedSpace F)))) =
      affineResidueTheta E.m E.modulus_ne_bot
        (rayIdealFractionalIdeal F E.a E.ideal_ne_bot) (cosetBasepointLift E) u h := by
  rw [← (cosetPrimalIndexEquiv E).tsum_eq]
  unfold affineResidueTheta
  apply tsum_congr
  intro l
  change RayParity.gδ F ∅ (RayParity.Q F (RayTheta.q F u h)
      (RayCoset.normalizationScale E • Theta.traceEmbedding F (E.b : F) +
        affineResidueScale (rayIdealFractionalIdeal F E.a E.ideal_ne_bot) •
          Theta.traceEmbedding F l.val)) = _
  rw [RayCoset.normalizationScale, ← affineResidueScale_rayIdealFractionalIdeal E.a E.ideal_ne_bot]
  simp only [cosetBasepointLift, Theta.traceEmbedding, map_add, smul_add]

private theorem coset_dual_integrand (E : RayCoset.Data F)
    (u : ℝ) (h : RayCoset.logHyperplane F) :
    (∑' l : Theta.dualLattice (RayCoset.normalizedLattice E),
      Complex.exp ((2 * Real.pi : ℝ) * Complex.I *
        (inner ℝ (l : NumberField.mixedEmbedding.euclidean.mixedSpace F)
          (RayCoset.normalizedBasepoint E) : ℂ)) *
      RayParity.gδ F ∅ (RayParity.Q F (RayTheta.q F u (-h)) l.val)) =
      affineResidueDualTheta E.m E.modulus_ne_bot
        (rayIdealFractionalIdeal F E.a E.ideal_ne_bot) (cosetBasepointLift E) u h := by
  rw [← (normalizedCosetDualIndexEquiv E).tsum_eq]
  unfold affineResidueDualTheta
  apply tsum_congr
  intro β
  rw [normalizedCosetDualIndex_tracePhase, normalizedCosetDualIndexEquiv_apply]
  rfl

theorem rayTheta_fδ_eq_affineResidueAverage
    (hF : NumberField.IsTotallyComplex F)
    (m a : Ideal (𝓞 F)) (hm : m ≠ ⊥) (ha : a ≠ ⊥)
    (hcop : a ⊔ m = ⊤) (hmt : m ≠ ⊤)
    (D : RayThetaRepresentatives F m hm)
    (q : coprimeIdealResidueUnits F m a hm ha hcop hmt)
    (x : {x : F // x ∈
      (rayIdealFractionalIdeal F a ha : FractionalIdeal (𝓞 F)⁰ F)})
    (hx : fractionalIdealQuotientMk
      (rayIdealFractionalIdeal F a ha : FractionalIdeal (𝓞 F)⁰ F)
      ((rayIdealFractionalIdeal F a ha * rayIdealFractionalIdeal F m hm) :
        FractionalIdeal (𝓞 F)⁰ F) x = q.val)
    (u : ℝ) (hu : 0 < u) :
    let c := (coprimeIdealResidueRayClass hF m a hm ha hcop hmt q).val
    RayTheta.fδ (D.coset c) ∅ u =
      (RayCoset.rayUnitTorsionCard F m : ℂ)⁻¹ *
        affineResidueAverage m hm (rayIdealFractionalIdeal F a ha) x u := by
  dsimp only
  let c := (coprimeIdealResidueRayClass hF m a hm ha hcop hmt q).val
  let I := rayIdealFractionalIdeal F a ha
  let J := rayIdealFractionalIdeal F (D.coset c).a (D.coset c).ideal_ne_bot
  obtain ⟨γ, y, hJ, hγy, hya, hym, hyb⟩ :=
    exists_rayRepresentative_affine_multiplier hF m a hm ha hcop hmt D q x hx
  let z : {z : F // z ∈ (J : FractionalIdeal (𝓞 F)⁰ F)} :=
    ⟨(γ : F) * x.val, principalMul_mem_ideal I J γ hJ x⟩
  have hby : (cosetBasepointLift (D.coset c)).val - z.val ∈
      ((J * rayIdealFractionalIdeal F m hm) : FractionalIdeal (𝓞 F)⁰ F) := by
    change ((D.coset c).b : F) - (γ : F) * x.val ∈ _
    rw [← hγy, ← map_sub]
    simp only [Units.val_mul, rayIdealFractionalIdeal_coe, ← FractionalIdeal.coeIdeal_mul,
      FractionalIdeal.mem_coeIdeal, J]
    refine ⟨(D.coset c).b - y, ?_, rfl⟩
    convert ((D.coset c).a * m).neg_mem hyb using 1 <;> ring
  rw [RayTheta.fδ, if_pos hu]
  simp_rw [coset_primal_integrand]
  change (RayCoset.rayUnitTorsionCard F (D.coset c).m : ℂ)⁻¹ *
    affineResidueAverage (D.coset c).m (D.coset c).modulus_ne_bot J
      (cosetBasepointLift (D.coset c)) u = _
  simp only [D.modulus_eq c]
  change (RayCoset.rayUnitTorsionCard F m : ℂ)⁻¹ *
    affineResidueAverage m hm J (cosetBasepointLift (D.coset c)) u = _
  congr 1
  rw [affineResidueAverage_congr m hm J (cosetBasepointLift (D.coset c)) u hu z hby]
  unfold affineResidueAverage
  simp_rw [show ∀ h, affineResidueTheta m hm J z u h =
      affineResidueTheta m hm I x u (h + principalNormalizedLogShift hF γ) from
    fun h ↦ affineResidueTheta_principal_mul hF m hm I J γ hJ x u hu h]
  exact rayUnitPeriodicLogHaarIntegral_translation F m hm _
    (affineResidueTheta_continuous m hm I x u hu)
    (affineResidueTheta_rayUnit_periodic hF m hm I x u hu)
    (principalNormalizedLogShift hF γ)

theorem rayTheta_gδDual_eq_affineResidueDualAverage
    (hF : NumberField.IsTotallyComplex F)
    (m a : Ideal (𝓞 F)) (hm : m ≠ ⊥) (ha : a ≠ ⊥)
    (hcop : a ⊔ m = ⊤) (hmt : m ≠ ⊤)
    (D : RayThetaRepresentatives F m hm)
    (q : coprimeIdealResidueUnits F m a hm ha hcop hmt)
    (x : {x : F // x ∈
      (rayIdealFractionalIdeal F a ha : FractionalIdeal (𝓞 F)⁰ F)})
    (hx : fractionalIdealQuotientMk
      (rayIdealFractionalIdeal F a ha : FractionalIdeal (𝓞 F)⁰ F)
      ((rayIdealFractionalIdeal F a ha * rayIdealFractionalIdeal F m hm) :
        FractionalIdeal (𝓞 F)⁰ F) x = q.val)
    (u : ℝ) (hu : 0 < u) :
    let c := (coprimeIdealResidueRayClass hF m a hm ha hcop hmt q).val
    RayTheta.gδDual (D.coset c) ∅ u =
      ((RayCoset.rayUnitTorsionCard F m : ℂ) *
        (RayCoset.modulusCovolume F m : ℂ))⁻¹ *
        affineResidueDualAverage m hm (rayIdealFractionalIdeal F a ha) x u := by
  dsimp only
  let c := (coprimeIdealResidueRayClass hF m a hm ha hcop hmt q).val
  let I := rayIdealFractionalIdeal F a ha
  let J := rayIdealFractionalIdeal F (D.coset c).a (D.coset c).ideal_ne_bot
  obtain ⟨γ, y, hJ, hγy, hya, hym, hyb⟩ :=
    exists_rayRepresentative_affine_multiplier hF m a hm ha hcop hmt D q x hx
  let z : {z : F // z ∈ (J : FractionalIdeal (𝓞 F)⁰ F)} :=
    ⟨(γ : F) * x.val, principalMul_mem_ideal I J γ hJ x⟩
  have hby : (cosetBasepointLift (D.coset c)).val - z.val ∈
      ((J * rayIdealFractionalIdeal F m hm) : FractionalIdeal (𝓞 F)⁰ F) := by
    change ((D.coset c).b : F) - (γ : F) * x.val ∈ _
    rw [← hγy, ← map_sub]
    simp only [Units.val_mul, rayIdealFractionalIdeal_coe, ← FractionalIdeal.coeIdeal_mul,
      FractionalIdeal.mem_coeIdeal, J]
    refine ⟨(D.coset c).b - y, ?_, rfl⟩
    convert ((D.coset c).a * m).neg_mem hyb using 1 <;> ring
  rw [RayTheta.gδDual, if_pos hu]
  simp_rw [coset_dual_integrand]
  change ((RayCoset.rayUnitTorsionCard F (D.coset c).m : ℂ) *
    (RayCoset.modulusCovolume F (D.coset c).m : ℂ))⁻¹ *
    affineResidueDualAverage (D.coset c).m (D.coset c).modulus_ne_bot J
      (cosetBasepointLift (D.coset c)) u = _
  simp only [D.modulus_eq c]
  congr 1
  rw [affineResidueDualAverage_congr m hm J (cosetBasepointLift (D.coset c)) u hu z hby]
  unfold affineResidueDualAverage
  simp_rw [show ∀ h, affineResidueDualTheta m hm J z u h =
      affineResidueDualTheta m hm I x u (h + principalNormalizedLogShift hF γ) from
    fun h ↦ affineResidueDualTheta_principal_mul hF m hm I J γ hJ x u hu h]
  exact rayUnitPeriodicLogHaarIntegral_translation F m hm _
    (affineResidueDualTheta_continuous m hm I x u hu)
    (affineResidueDualTheta_rayUnit_periodic hF m hm I x u hu)
    (principalNormalizedLogShift hF γ)

end DedekindZetaZeroFree.Hecke.Theta

end
