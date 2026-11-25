/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Field.ULift
public import WeilConjectures.AlgebraicGeometry.Sites.PointConstantSheaf
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Devissage
public import WeilConjectures.SixFunctors.Etale.Derived.RestrictScalarsLowerStar
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# Higher direct images of constant sheaves and their coefficients

For `h : Y ⟶ X` and a ring `R`, we consider the functor `M ↦ R^q h_* (M_Y)` from `R`-modules to
sheaves of `R`-modules on `X_ét` (`AlgebraicGeometry.Etale.higherDirectImageConstantFunctor`).

- It commutes with restriction of scalars along a ring map `R →+* R'`
  (`AlgebraicGeometry.Etale.restrictScalarsHigherDirectImageConstantIso`), so whether it
  vanishes does not depend on the coefficient ring.
- Over a field `𝕜` and for `h` quasi-compact and quasi-separated, it vanishes at every module
  as soon as it vanishes at `𝕜`: every vector space is the filtered colimit of finite direct sums
  of copies of `𝕜`
  (`AlgebraicGeometry.Etale.not_isZero_higherDirectImageConstantFunctor_self`).
- Consequently a module `M` killed by a prime `r` with `R^q h_* (M_Y) ≠ 0` gives
  `R^q h_* (Λ/rΛ) ≠ 0`
  (`AlgebraicGeometry.Etale.not_isZero_higherDirectImage_constantModSheaf_of_smul_eq_zero`).

We also record the prime-factor dévissage for nonvanishing
(`CategoryTheory.exists_prime_dvd_not_isZero_map_of_nsmul_id_eq_zero`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Abelian C] [Category* D] [Abelian D]

/-- **Prime-factor dévissage for nonvanishing.** Let `Φ` be a functor between abelian categories
which is exact in the middle on short exact sequences. If `Φ F ≠ 0` for an object `F` killed by
a positive integer `n`, then `Φ G ≠ 0` for an object `G` killed by a prime `r ∣ n`: use the
short exact sequence `0 ⟶ F[r] ⟶ F ⟶ rF ⟶ 0` and induct on `n`. -/
theorem exists_prime_dvd_not_isZero_map_of_nsmul_id_eq_zero (Φ : C ⥤ D)
    [Φ.PreservesZeroMorphisms] (hΦ : ∀ S : ShortComplex C, S.ShortExact → (S.map Φ).Exact) :
    ∀ n : ℕ, 0 < n → ∀ F : C, n • 𝟙 F = 0 → ¬ IsZero (Φ.obj F) →
      ∃ r : ℕ, r.Prime ∧ r ∣ n ∧ ∃ G : C, r • 𝟙 G = 0 ∧ ¬ IsZero (Φ.obj G) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn F hF hne
    by_cases h1 : n = 1
    · subst h1
      rw [one_nsmul] at hF
      exact absurd (Φ.map_isZero ((IsZero.iff_id_eq_zero F).2 hF)) hne
    obtain ⟨r, hr, hrn⟩ := Nat.exists_prime_and_dvd h1
    by_cases hK : IsZero (Φ.obj (kernel (r • 𝟙 F)))
    · by_cases hI : IsZero (Φ.obj (Limits.image (r • 𝟙 F)))
      · exact absurd ((hΦ _ (Abelian.shortExact_nsmulShortComplex F r)).isZero_of_both_zeros
          (hK.eq_of_src _ _) (hI.eq_of_tgt _ _)) hne
      · obtain ⟨s, hs, hsn, G, hG, hGne⟩ := ih (n / r) (Nat.div_lt_self hn hr.one_lt)
          (Nat.div_pos (Nat.le_of_dvd hn hrn) hr.pos) _
          (Abelian.nsmul_id_image_eq_zero F hF hrn) hI
        exact ⟨s, hs, hsn.trans (Nat.div_dvd_of_dvd hrn), G, hG, hGne⟩
    · exact ⟨r, hr, hrn, _, Abelian.nsmul_id_kernel_eq_zero F r, hK⟩

end CategoryTheory

namespace AlgebraicGeometry

/-- The functor `M ↦ R^q h_* (M_Y)` sending a module to the higher direct image of the
constant sheaf with that value. -/
noncomputable abbrev Etale.higherDirectImageConstantFunctor (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ) :
    ModuleCat.{u + 1} A ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
    (DerivedCategory.Plus.singleFunctor _ 0 ⋙ R+((h)_*[ModuleCat.{u + 1} A]) ⋙
      DerivedCategory.Plus.homologyFunctor _ q)

instance Etale.additive_higherDirectImageConstantFunctor (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ) :
    (Etale.higherDirectImageConstantFunctor A h q).Additive := by
  dsimp only [Etale.higherDirectImageConstantFunctor]
  infer_instance

section RestrictScalars

variable {A A' : Type (u + 1)} [CommRing A] [CommRing A'] (φ : A →+* A')

/-- Restriction of scalars preserves sheafification, being a left adjoint. -/
instance Etale.preservesSheafification_restrictScalars (S : Scheme.{u}) :
    S.smallEtaleTopology.PreservesSheafification (ModuleCat.restrictScalars.{u + 1} φ) :=
  Sheaf.preservesSheafification_of_adjunction _
    (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ)

/-- Restriction of scalars commutes with `M ↦ R^q h_* (M_Y)`: the constant sheaf, the inclusion
in degree `0`, the derived direct image and the cohomology sheaves all commute with it. -/
noncomputable def Etale.restrictScalarsHigherDirectImageConstantIso {X Y : Scheme.{u}}
    (h : Y ⟶ X) (q : ℤ) (N : ModuleCat.{u + 1} A') :
    (Sheaf.restrictScalars X.smallEtaleTopology φ).obj
        ((Etale.higherDirectImageConstantFunctor A' h q).obj N) ≅
      (Etale.higherDirectImageConstantFunctor A h q).obj
        ((ModuleCat.restrictScalars.{u + 1} φ).obj N) :=
  ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlusHomologyFunctorIso
      q).app _ ≪≫
    (DerivedCategory.Plus.homologyFunctor _ q).mapIso
      ((asIso (Etale.rightDerivedLowerStarRestrictScalars φ h)).app _ ≪≫
        R+((h)_*[ModuleCat.{u + 1} A]).mapIso
          (((Sheaf.restrictScalars Y.smallEtaleTopology φ).mapDerivedCategoryPlusSingleFunctor
              0).app _ ≪≫
            (DerivedCategory.Plus.singleFunctor _ 0).mapIso
              ((constantCommuteCompose Y.smallEtaleTopology
                (ModuleCat.restrictScalars.{u + 1} φ)).app N)))

/-- Whether `R^q h_* (M_Y)` vanishes does not depend on the coefficient ring. -/
lemma Etale.isZero_higherDirectImageConstantFunctor_restrictScalars_iff {X Y : Scheme.{u}}
    (h : Y ⟶ X) (q : ℤ) (N : ModuleCat.{u + 1} A') :
    IsZero ((Etale.higherDirectImageConstantFunctor A h q).obj
        ((ModuleCat.restrictScalars.{u + 1} φ).obj N)) ↔
      IsZero ((Etale.higherDirectImageConstantFunctor A' h q).obj N) := by
  rw [← (Etale.restrictScalarsHigherDirectImageConstantIso φ h q N).isZero_iff]
  refine ⟨fun hz ↦ ?_, fun hz ↦ (Sheaf.restrictScalars X.smallEtaleTopology φ).map_isZero hz⟩
  rw [IsZero.iff_id_eq_zero]
  refine (Sheaf.restrictScalars X.smallEtaleTopology φ).map_injective ?_
  rw [CategoryTheory.Functor.map_id, Functor.map_zero]
  exact hz.eq_of_src _ _

end RestrictScalars

section Field

variable {𝕜 : Type (u + 1)} [Field 𝕜]

/-- A functor out of vector spaces which vanishes at a space `W` vanishes at every space `V`
admitting an injective linear map `V ⟶ W`, `V` being a retract of `W`. -/
lemma Etale.isZero_obj_of_injective {A : Type*} [Category* A] [Preadditive A]
    (Φ : ModuleCat.{u + 1} 𝕜 ⥤ A) {V W : ModuleCat.{u + 1} 𝕜} (f : V ⟶ W)
    (hf : Function.Injective f) (hW : IsZero (Φ.obj W)) : IsZero (Φ.obj V) := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f.hom (LinearMap.ker_eq_bot.2 hf)
  have hfg : f ≫ ModuleCat.ofHom g = 𝟙 V := ModuleCat.hom_ext hg
  rw [IsZero.iff_id_eq_zero, ← CategoryTheory.Functor.map_id, ← hfg, Functor.map_comp,
    hW.eq_of_src (Φ.map (ModuleCat.ofHom g)) 0, comp_zero]

/-- Over a field `𝕜`, an additive functor `Φ` out of vector spaces vanishing at `𝕜` vanishes
at every space `V` at whose filtered system of finitely generated subspaces it preserves
colimits: these subspaces are finite direct sums of copies of `𝕜`. -/
theorem Etale.isZero_obj_of_isZero_obj_self {D : Type*} [Category* D] [Abelian D]
    (Φ : ModuleCat.{u + 1} 𝕜 ⥤ D) [Φ.Additive] (V : ModuleCat.{u + 1} 𝕜)
    [PreservesColimitsOfShape {N : Submodule 𝕜 V // N.FG} Φ]
    (h𝕜 : IsZero (Φ.obj (ModuleCat.of 𝕜 𝕜))) : IsZero (Φ.obj V) := by
  classical
  -- the finite free modules
  have hfin (k : ℕ) : IsZero (Φ.obj (ModuleCat.of 𝕜 (Fin k → 𝕜))) := by
    let f : Fin k → ModuleCat.{u + 1} 𝕜 := fun _ ↦ ModuleCat.of 𝕜 𝕜
    refine IsZero.of_iso ?_ (Φ.mapIso (ModuleCat.biproductIsoPi f).symm ≪≫ Φ.mapBiproduct f)
    rw [IsZero.iff_id_eq_zero]
    exact biproduct.hom_ext _ _ fun j ↦ h𝕜.eq_of_tgt _ _
  -- the finitely generated subspaces
  have hfg (N : {N : Submodule 𝕜 V // N.FG}) : IsZero (Φ.obj (ModuleCat.of 𝕜 N.1)) := by
    have : Module.Finite 𝕜 N.1 := Module.Finite.iff_fg.2 N.2
    exact (hfin _).of_iso (Φ.mapIso (Module.finBasis 𝕜 N.1).equivFun.toModuleIso)
  -- the filtered colimit
  have : Nonempty {N : Submodule 𝕜 V // N.FG} := ⟨⟨⊥, Submodule.fg_bot⟩⟩
  have hc := isColimitOfPreserves Φ
    (ModuleCat.directLimitIsColimit (fun N : {N : Submodule 𝕜 V // N.FG} ↦ N.1)
      (Module.fgSystem 𝕜 V))
  have hz : IsZero (Φ.obj (ModuleCat.directLimitCocone
      (fun N : {N : Submodule 𝕜 V // N.FG} ↦ N.1) (Module.fgSystem 𝕜 V)).pt) := by
    rw [IsZero.iff_id_eq_zero]
    exact hc.hom_ext fun N ↦ (hfg N).eq_of_src _ _
  exact hz.of_iso (Φ.mapIso (Module.fgSystem.equiv 𝕜 V).toModuleIso.symm)

/-- Over a field `𝕜` and for `h` quasi-compact and quasi-separated, if `R^q h_* (V_Y) ≠ 0` for
some vector space `V`, then `R^q h_* (𝕜_Y) ≠ 0`: `V` is the filtered colimit of its finite
dimensional subspaces, which are finite direct sums of copies of `𝕜`, and `R^q h_*` commutes
with filtered colimits (`AlgebraicGeometry.Etale.preservesColimitsOfShape_higherDirectImage`). -/
theorem Etale.not_isZero_higherDirectImageConstantFunctor_self {X Y : Scheme.{u}}
    (h : Y ⟶ X) [QuasiCompact h] [QuasiSeparated h] (q : ℤ) (V : ModuleCat.{u + 1} 𝕜)
    (hV : ¬ IsZero ((Etale.higherDirectImageConstantFunctor 𝕜 h q).obj V)) :
    ¬ IsZero ((Etale.higherDirectImageConstantFunctor 𝕜 h q).obj (ModuleCat.of 𝕜 𝕜)) := by
  have : Nonempty {N : Submodule 𝕜 V // N.FG} := ⟨⟨⊥, Submodule.fg_bot⟩⟩
  have : EssentiallySmall.{u + 1} {N : Submodule 𝕜 V // N.FG} :=
    essentiallySmallSelf.{u + 1} _
  have := Etale.preservesColimitsOfShape_higherDirectImage 𝕜 h q {N : Submodule 𝕜 V // N.FG}
  have : PreservesColimitsOfSize.{u + 1, u + 1}
      (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} 𝕜)) :=
    (constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u + 1} 𝕜)
      terminalIsTerminal).leftAdjoint_preservesColimits
  exact fun h𝕜 ↦ hV (Etale.isZero_obj_of_isZero_obj_self _ V h𝕜)

end Field

variable (Λ : Type (u + 1)) [CommRing Λ]

-- the linear maps into restrictions of scalars need to unfold `ModuleCat.restrictScalars`
set_option backward.isDefEq.respectTransparency false in
/-- Let `r` be a prime and `M` a `Λ`-module killed by `r`. If `R^q h_* (M_Y) ≠ 0` for a
quasi-compact quasi-separated `h`, then `R^q h_* (Λ/rΛ) ≠ 0`. Indeed `M` and `Λ/rΛ` are modules
over `Λ₁ = Λ/rΛ`, hence vector spaces over `𝔽_r ⊆ Λ₁`, and `Λ₁ ≠ 0`; the vanishing of
`R^q h_*` of a constant sheaf does not depend on the coefficient ring, and over `𝔽_r` it
vanishes at `M` if it vanishes at `𝔽_r`, which is a direct summand of `Λ₁`. -/
theorem Etale.not_isZero_higherDirectImage_constantModSheaf_of_smul_eq_zero {X Y : Scheme.{u}}
    (h : Y ⟶ X) [QuasiCompact h] [QuasiSeparated h] (q : ℤ) (r : ℕ) [hr : Fact r.Prime]
    (M : ModuleCat.{u + 1} Λ) (hM : ∀ m : M, (r : Λ) • m = 0)
    (hne : ¬ IsZero ((Etale.higherDirectImageConstantFunctor Λ h q).obj M)) :
    ¬ IsZero (Etale.higherDirectImage Λ h q (Etale.constantModSheaf Λ Y r)) := by
  set I : Ideal Λ := Ideal.span {(r : Λ)}
  -- `Λ/rΛ` is nonzero, since `M` would vanish otherwise
  have hI : I ≠ ⊤ := by
    intro hI
    obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_top.1 hI
    refine hne (Functor.map_isZero _ ((ModuleCat.isZero_iff_subsingleton).2 ⟨fun a b ↦ ?_⟩))
    rw [← one_smul Λ a, ← one_smul Λ b, ← v.inv_mul, mul_smul, mul_smul, hv, hM, hM]
  have : Nontrivial (Λ ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI
  have : CharP (Λ ⧸ I) r := (CharP.charP_iff_prime_eq_zero hr.out).2 (by
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _)
  let φ : Λ →+* Λ ⧸ I := Ideal.Quotient.mk I
  let ψ : ULift.{u + 1} (ZMod r) →+* Λ ⧸ I :=
    (ZMod.castHom (dvd_refl r) (Λ ⧸ I)).comp ULift.ringEquiv.toRingHom
  -- `M` as a module over `Λ/rΛ`
  have hMI : Module.IsTorsionBySet Λ M I :=
    (Module.isTorsionBySet_span_singleton_iff (r : Λ)).2 hM
  let _ : Module (Λ ⧸ I) M := hMI.module
  let M₁ : ModuleCat.{u + 1} (Λ ⧸ I) := ModuleCat.of (Λ ⧸ I) M
  let eM : M ≅ (ModuleCat.restrictScalars.{u + 1} φ).obj M₁ :=
    LinearEquiv.toModuleIso
      { AddEquiv.refl M with
        map_smul' := fun a m ↦ (hMI.mk_smul a m).symm }
  have h₁ : ¬ IsZero ((Etale.higherDirectImageConstantFunctor (Λ ⧸ I) h q).obj M₁) := by
    rw [← Etale.isZero_higherDirectImageConstantFunctor_restrictScalars_iff φ]
    exact fun hz ↦ hne (hz.of_iso ((Etale.higherDirectImageConstantFunctor Λ h q).mapIso eM))
  have h₂ := Etale.not_isZero_higherDirectImageConstantFunctor_self (𝕜 := ULift.{u + 1} (ZMod r))
    h q ((ModuleCat.restrictScalars.{u + 1} ψ).obj M₁)
    (mt (Etale.isZero_higherDirectImageConstantFunctor_restrictScalars_iff ψ h q M₁).1 h₁)
  -- `𝔽_r` is a direct summand of `Λ/rΛ`
  let i₀ : ULift.{u + 1} (ZMod r) →ₗ[ULift.{u + 1} (ZMod r)]
      (ModuleCat.restrictScalars.{u + 1} ψ).obj (ModuleCat.of (Λ ⧸ I) (Λ ⧸ I)) :=
    { toFun := ψ
      map_add' := ψ.map_add
      map_smul' := ψ.map_mul }
  let i : ModuleCat.of (ULift.{u + 1} (ZMod r)) (ULift.{u + 1} (ZMod r)) ⟶
      (ModuleCat.restrictScalars.{u + 1} ψ).obj (ModuleCat.of (Λ ⧸ I) (Λ ⧸ I)) :=
    ConcreteCategory.ofHom i₀
  have h₃ : ¬ IsZero ((Etale.higherDirectImageConstantFunctor (Λ ⧸ I) h q).obj
      (ModuleCat.of (Λ ⧸ I) (Λ ⧸ I))) := by
    rw [← Etale.isZero_higherDirectImageConstantFunctor_restrictScalars_iff ψ]
    exact fun hz ↦ h₂ (Etale.isZero_obj_of_injective _ i
      (fun a b hab ↦ ψ.injective (by simpa [i, i₀] using hab)) hz)
  rw [← Etale.isZero_higherDirectImageConstantFunctor_restrictScalars_iff φ] at h₃
  let e : (ModuleCat.restrictScalars.{u + 1} φ).obj (ModuleCat.of (Λ ⧸ I) (Λ ⧸ I)) ≅
      ModuleCat.of Λ (Λ ⧸ I) :=
    LinearEquiv.toModuleIso
      { AddEquiv.refl (Λ ⧸ I) with
        map_smul' := fun a x ↦ (Algebra.smul_def a x).symm }
  have hI' : Etale.higherDirectImage Λ h q (Etale.constantModSheaf Λ Y r) =
      (Etale.higherDirectImageConstantFunctor Λ h q).obj (ModuleCat.of Λ (Λ ⧸ I)) := rfl
  rw [hI']
  exact fun hz ↦ h₃ (hz.of_iso ((Etale.higherDirectImageConstantFunctor Λ h q).mapIso e))

section SepClosed

local instance : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
  hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _

local instance : HasColimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
  hasColimitsOfSizeShrink.{u, u, u + 1, u + 1} _

/-- Over a separably closed field `K`, a sheaf `G` on `Spec K` is constant, with value a module
`M` killed by every integer killing `G`, and `R^q h_* e⁻¹ G = R^q h_* (M_Y)` for
`e : Y ⟶ Spec K`. -/
theorem Etale.exists_smul_eq_zero_not_isZero_of_isSepClosed {K : Type u} [Field K]
    [IsSepClosed K] {X Y : Scheme.{u}} (e : Y ⟶ Spec (.of K)) (h : Y ⟶ X) (q : ℤ) (r : ℕ)
    (G : Sheaf (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) (hG : r • 𝟙 G = 0)
    (hne : ¬ IsZero ((Etale.baseChangeTargetFunctor Λ e h q).obj G)) :
    ∃ M : ModuleCat.{u + 1} Λ, (∀ m : M, (r : Λ) • m = 0) ∧
      ¬ IsZero ((Etale.higherDirectImageConstantFunctor Λ h q).obj M) := by
  let c := constantSheaf (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let i : c.obj (c.objPreimage G) ≅ G := c.objObjPreimageIso G
  have hM : r • 𝟙 (c.objPreimage G) = 0 := c.map_injective (by
    rw [CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero]
    calc r • 𝟙 (c.obj (c.objPreimage G)) = i.hom ≫ (r • 𝟙 G) ≫ i.inv := by simp
      _ = 0 := by rw [hG, zero_comp, comp_zero])
  refine ⟨c.objPreimage G, fun m ↦ ?_, fun hz ↦ hne (hz.of_iso ?_)⟩
  · have := congr(($hM).hom m)
    simpa [Nat.cast_smul_eq_nsmul] using this
  · exact (Etale.baseChangeTargetFunctor Λ e h q).mapIso i.symm ≪≫
      (Etale.baseChangeTargetFunctorIso Λ e h q).app _ ≪≫
      (DerivedCategory.Plus.singleFunctor _ 0 ⋙ R+((h)_*[ModuleCat.{u + 1} Λ]) ⋙
        DerivedCategory.Plus.homologyFunctor _ q).mapIso
          ((Etale.constantSheafCompUpperStarIso Λ e).app _)

end SepClosed

end AlgebraicGeometry
