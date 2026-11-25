/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeOfCover

/-!
# Locally free module objects are free on a finite affine pro-étale cover

Let `Λ` be a commutative condensed ring and `M` a module object over `Λ_S` on `S_proét`.

* `ProEtale.CondensedRing.isFree_upperStar`: the pullback `g^* M` of a free module object is
  free.
* `ProEtale.CondensedRing.isFree_upperStar_of_isFree_mapMod`: the freeness of the sheaf pullback
  `mapMod(f^*) M` over `f^* Λ_S`, as in the definition of `ProEtale.IsLocallyFree`, implies the
  freeness of the pullback `f^* M` of module objects over `Λ`.
* `Scheme.Cover.exists_finite_affine_refinement`: a pro-étale cover of a quasi-compact scheme
  is refined by a finite pro-étale cover with affine members.
* `ProEtale.CondensedRing.exists_finite_affine_cover_isFree_upperStar`: a locally free module
  object on a quasi-compact scheme `S` becomes free on the members of a finite pro-étale cover
  of `S` by affine schemes.
* `compactSpace_quasiSeparatedSpace_of_isPullback`: the fibre product of
  two affine schemes over a quasi-separated scheme is quasi-compact and quasi-separated.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry

open Scheme

/-- A pro-étale cover of a quasi-compact scheme is refined by a finite pro-étale cover whose
members are affine: cover `S` by finitely many affine opens `Uₐ`, and refine the pullback of the
cover to each `Uₐ` by finitely many affine schemes, using that pro-étale covers are
quasi-compact. -/
lemma Scheme.Cover.exists_finite_affine_refinement {S : Scheme.{u}} [CompactSpace S]
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage S) :
    ∃ 𝒱 : Scheme.Cover.{u} Scheme.proetalePrecoverage S, Finite 𝒱.I₀ ∧
      (∀ k, IsAffine (𝒱.X k)) ∧
      ∀ k, ∃ (i : 𝒰.I₀) (g : 𝒱.X k ⟶ 𝒰.X i), g ≫ 𝒰.f i = 𝒱.f k := by
  have hle : zariskiPrecoverage ≤ Scheme.proetalePrecoverage.{u} :=
    zariskiPrecoverage_le_propQCPrecoverage
  let 𝒜 : Scheme.Cover.{u} Scheme.proetalePrecoverage S :=
    S.affineCover.finiteSubcover.weaken hle
  have h𝒜 (a : 𝒜.I₀) : IsAffine (𝒜.X a) := inferInstanceAs (IsAffine (Spec _))
  have hfin : Finite 𝒜.I₀ := inferInstanceAs (Finite S.affineCover.finiteSubcover.I₀)
  have key (a : 𝒜.I₀) : ∃ (𝒲 : Scheme.Cover.{u} Scheme.proetalePrecoverage (𝒜.X a)),
      Finite 𝒲.I₀ ∧ (∀ k, IsAffine (𝒲.X k)) ∧
      ∀ k, ∃ (i : 𝒰.I₀) (g : 𝒲.X k ⟶ 𝒰.X i), g ≫ 𝒰.f i = 𝒲.f k ≫ 𝒜.f a := by
    let 𝒰a : Scheme.Cover.{u} (propQCPrecoverage @WeaklyEtale) (𝒜.X a) :=
      𝒰.pullback₁ (𝒜.f a)
    obtain ⟨𝒱, φ, _, -⟩ := QuasiCompactCover.exists_hom.{u} 𝒰a.forgetQc
    have : ∀ j, AlgebraicGeometry.QuasiCompact (𝒱.cover.f j) := fun j ↦ by
      dsimp [AffineCover.cover]; infer_instance
    have : Finite 𝒱.cover.I₀ := ‹Finite 𝒱.I₀›
    refine ⟨Cover.ofQuasiCompactCover 𝒱.cover, ‹_›,
      fun k ↦ inferInstanceAs (IsAffine (Spec (𝒱.X k))),
      fun k ↦ ⟨φ.s₀ k, φ.h₀ k ≫ pullback.snd _ _, ?_⟩⟩
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ 𝒜.f a) (φ.w₀ k)
  choose 𝒲 h𝒲fin h𝒲aff h𝒲 using key
  refine ⟨𝒜.bind 𝒲, inferInstanceAs (Finite (Σ a, (𝒲 a).I₀)), fun k ↦ h𝒲aff k.1 k.2,
    fun k ↦ ?_⟩
  obtain ⟨i, g, hg⟩ := h𝒲 k.1 k.2
  exact ⟨i, g, hg⟩

/-- The fibre product `P = V ×_S W` of two affine schemes over a quasi-separated scheme `S` is
quasi-compact and quasi-separated: `V ⟶ S` is quasi-compact and quasi-separated, hence so is its
base change `P ⟶ W`, whose target is affine. -/
lemma compactSpace_quasiSeparatedSpace_of_isPullback {S V W P : Scheme.{u}}
    [QuasiSeparatedSpace S] [IsAffine V] [IsAffine W] {f : V ⟶ S} {g : W ⟶ S}
    {p₁ : P ⟶ V} {p₂ : P ⟶ W} (h : CategoryTheory.IsPullback p₁ p₂ f g) :
    CompactSpace P ∧ QuasiSeparatedSpace P := by
  have : AlgebraicGeometry.QuasiCompact p₂ := by
    rw [← h.isoPullback_hom_snd]; infer_instance
  have : QuasiSeparated p₂ := by
    rw [← h.isoPullback_hom_snd]; infer_instance
  exact ⟨QuasiCompact.compactSpace_of_compactSpace p₂, quasiSeparatedSpace_of_quasiSeparated p₂⟩

end AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

variable {Λ} in
/-- The pullback of module objects over `Λ` along any morphism of schemes preserves free module
objects of finite rank: it is additive and sends `Λ_Y` to `Λ_W`. -/
lemma isFree_upperStar {W Y : Scheme.{u}} (g : W ⟶ Y)
    {M : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)}
    (hM : Mod.IsFree (condensedRingObj Λ Y) M) :
    Mod.IsFree (condensedRingObj Λ W) ((g)^*⟦Λ⟧.obj M) :=
  let ⟨n, ⟨e⟩⟩ := hM
  ⟨n, ⟨(g)^*⟦Λ⟧.mapIso e ≪≫ Mod.finiteFreeIsoMap _ (upperStarObjRegularIso Λ g) n⟩⟩

variable {Λ} in
/-- If the sheaf pullback `mapMod(f^*) M` is free over the sheaf pullback `f^* Λ_X` of the
coefficient ring, as in the definition of `ProEtale.IsLocallyFree`, then the pullback `f^* M` of
module objects over `Λ` is free over `Λ_Y`. This is the converse of
`isFree_mapMod_of_isFree_upperStar`. -/
lemma isFree_upperStar_of_isFree_mapMod {X Y : Scheme.{u}} (f : Y ⟶ X)
    {M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (h : Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} f).obj (condensedRingObj Λ X))
      (((ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ X)).obj M)) :
    Mod.IsFree (condensedRingObj Λ Y) ((f)^*⟦Λ⟧.obj M) := by
  obtain ⟨d, ⟨e⟩⟩ := h
  let α := condensedPullbackHom Λ f
  exact ⟨d, ⟨((Mod.comapId _).app _).symm ≪≫ (Mod.comapCongr (IsIso.inv_hom_id α).symm).app _ ≪≫
    (Mod.comapComp (inv α) α).app _ ≪≫
    (Mod.comap (inv α)).mapIso (comapUpperStarObjIso Λ f M ≪≫ e) ≪≫
    Mod.finiteFreeIsoMap (Mod.comap (inv α)) (Mod.regularIsoOfIsIso α) d⟩⟩

variable {Λ} in
/-- **Locally free module objects are free on a finite affine cover.** A locally free module
object on a quasi-compact scheme `S` becomes free after pullback to each member of a finite
pro-étale cover of `S` by affine schemes. -/
theorem exists_finite_affine_cover_isFree_upperStar {S : Scheme.{u}} [CompactSpace S]
    {M : Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)}
    (hM : IsLocallyFree (condensedRingObj Λ S) M) :
    ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage S, Finite 𝒰.I₀ ∧
      (∀ k, IsAffine (𝒰.X k)) ∧
      ∀ k, Mod.IsFree (condensedRingObj Λ (𝒰.X k)) ((𝒰.f k)^*⟦Λ⟧.obj M) := by
  obtain ⟨𝒰, h𝒰⟩ := hM
  obtain ⟨𝒱, hfin, haff, h𝒱⟩ := 𝒰.exists_finite_affine_refinement
  refine ⟨𝒱, hfin, haff, fun k ↦ ?_⟩
  obtain ⟨i, g, hg⟩ := h𝒱 k
  obtain ⟨n, ⟨e⟩⟩ := isFree_upperStar g (isFree_upperStar_of_isFree_mapMod _ (h𝒰 i))
  exact ⟨n, ⟨eqToIso (congrArg (fun f ↦ (f)^*⟦Λ⟧.obj M) hg.symm) ≪≫
    (upperStarComp Λ g (𝒰.f i)).app M ≪≫ e⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
