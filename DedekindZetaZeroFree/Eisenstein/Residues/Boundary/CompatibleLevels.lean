module

public import DedekindZetaZeroFree.Eisenstein.Residues.Boundary.LevelRestriction

@[expose] public section

noncomputable section
open scoped Classical NumberField
namespace DedekindZetaZeroFree.FourierContinuation.ResidualBoundaryRelevel
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
local notation "Level" => KPGlobalTorusFunctionData.FiniteLevel F ζ hζ

theorem exists_common_level (J : Level) (n : ℕ) (U : Fin n → Level) :
    ∃ V : Level, V.toOpenSubgroup.toSubgroup ≤ J.toOpenSubgroup.toSubgroup ∧
      ∀ i, V.toOpenSubgroup.toSubgroup ≤ (U i).toOpenSubgroup.toSubgroup := by
  induction n with
  | zero => exact ⟨J, le_rfl, fun i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨V,hJ,hV⟩ := ih (fun i => U i.castSucc)
    refine ⟨meetLevel F ζ hζ V (U (Fin.last n)), ?_, ?_⟩
    · exact le_trans inf_le_left hJ
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact inf_le_right
      · exact le_trans inf_le_left (hV j)

theorem globalLevel_mono {U V : Level}
    (h : U.toOpenSubgroup.toSubgroup ≤ V.toOpenSubgroup.toSubgroup) :
    KPGlobalTorusFunctionData.globalLevel F ζ hζ U ≤
      KPGlobalTorusFunctionData.globalLevel F ζ hζ V :=
  Subgroup.map_mono h
end DedekindZetaZeroFree.FourierContinuation.ResidualBoundaryRelevel

end
