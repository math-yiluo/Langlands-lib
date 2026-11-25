/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.Topology.NoetherianSpace
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeOfFinitelyPresented.Elimination

/-!
# Locally finitely presented `ℚ̲̄_ℓ`-modules on schemes of finite type are locally free

Let `Z` be a scheme of finite type over a field `k` and `M` a module object over `ℚ̲̄_ℓ,Z` on the
pro-étale site of `Z` which is locally finitely presented. Then `M` is locally free
(`ProEtale.CondensedRing.isLocallyFree_of_isLocallyFinitelyPresented`): the lisse
`ℚ̄_ℓ`-sheaves of Bhatt–Scholze, *The pro-étale topology for schemes*, Definition 6.8.6, are the
locally finitely presented ones. The statement fails on non-noetherian bases.

## The argument

1. *Charts.* Every point of `Z` lies in the image of a flat morphism `h : W ⟶ Z` from an affine
   scheme with `h^* M ≅ coker φ` for a matrix `φ : (ℚ̲̄_ℓ,W)^m ⟶ (ℚ̲̄_ℓ,W)^n`
   (`ProEtale.CondensedRing.exists_isOpenImmersion_isFinitelyPresented`): an affine open
   subscheme of a member of a pro-étale cover over which `M` is finitely presented.
2. *The rank function.* The fibre rank of a pullback `h^* M` at a point `w` (the rank of its
   pullback to `Spec κ(w)`, `ProEtale.CondensedRing.HasFiberRank`) only depends on `h w`
   (`ProEtale.CondensedRing.HasFiberRank.eq_of_apply_eq`, computing on `W₁ ×_Z W₂`); this defines
   the rank function `ProEtale.CondensedRing.fiberRankFun M : Z → ℕ`.
3. *Constancy along specializations.* If `z₁ ⤳ z₂` and `h w₂ = z₂` for a chart `h`, flatness of
   `h` lifts the specialization to `w₁ ⤳ w₂`. The entries of `φ` are continuous functions to the
   Hausdorff space `ℚ̄_ℓ`, so they take the same values at `w₁` and `w₂`, and the fibre ranks at
   `w₁` and `w₂`, which only depend on these values
   (`ProEtale.CondensedRing.hasFiberRank_cokernel_of_endValue_eq`, computed over `Spec k`),
   agree. As `Z` is noetherian, the rank function is locally constant
   (`ProEtale.CondensedRing.isLocallyConstant_fiberRankFun`).
4. *Local freeness.* On the clopen subset of a chart where the rank function takes the value at
   a given point, `coker φ` has constant fibre rank, hence is free near that point by Gaussian
   elimination (`ProEtale.CondensedRing.exists_isOpenImmersion_cokernel_iso_finiteFree`).

The description of the sections of `ℚ̲̄_ℓ` over quasi-compact quasi-separated schemes
(`ProEtale.CondensedRing.exists_endRegularRingEquiv`) rests on Bhatt–Scholze, Lemma 4.2.12
(`ProEtale.isIso_continuousMapComparison`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable {A : Type*} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  {X : Scheme.{u}} {R : Sheaf (Scheme.ProEt.topology X) A} [MonObj R]

/-- A module object is locally free if, for some pro-étale cover `{Uᵢ ⟶ X}`, every point of every
`Uᵢ` has an open neighbourhood over which the module is free: the Zariski covers of the `Uᵢ` by
these neighbourhoods refine the cover. -/
lemma IsLocallyFree.of_forall_exists_isOpenImmersion {M : Mod (Sheaf (Scheme.ProEt.topology X) A) R}
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (H : ∀ (i : 𝒰.I₀) (y : 𝒰.X i), ∃ (V : Scheme.{u}) (j : V ⟶ 𝒰.X i) (_ : IsOpenImmersion j),
      y ∈ Set.range j ∧ Mod.IsFree ((ProEtale.upperStar A (j ≫ 𝒰.f i)).obj R)
        (((ProEtale.upperStar A (j ≫ 𝒰.f i)).mapMod R).obj M)) :
    IsLocallyFree R M := by
  choose V j hj hy hfree using H
  exact ⟨𝒰.bind fun i ↦ (Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) (𝒰.X i) (V i) (j i)
      (fun y ↦ ⟨y, hy i y⟩) (hj i)).weaken Scheme.zariskiPrecoverage_le_proetalePrecoverage,
    fun ⟨i, y⟩ ↦ hfree i y⟩

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime]

section FiberRank

variable {X : Scheme.{u}}
  {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X)}

/-- The fibre ranks of two pullbacks of `M` agree at points with the same image: both are the
fibre rank of the pullback of `M` to the fibre product at a point over the two points. -/
lemma HasFiberRank.eq_of_apply_eq {W₁ W₂ : Scheme.{u}} (h₁ : W₁ ⟶ X) (h₂ : W₂ ⟶ X) {x₁ : W₁}
    {x₂ : W₂} (hx : h₁ x₁ = h₂ x₂) {d₁ d₂ : ℕ}
    (H₁ : HasFiberRank ℓ ((h₁)^*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧.obj M) x₁ d₁)
    (H₂ : HasFiberRank ℓ ((h₂)^*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧.obj M) x₂ d₂) :
    d₁ = d₂ := by
  obtain ⟨p, hp₁, hp₂⟩ := Scheme.Pullback.exists_preimage_pullback x₁ x₂ hx
  rw [← hp₁] at H₁
  rw [← hp₂] at H₂
  refine (H₁.upperStar (pullback.fst h₁ h₂)).unique ((H₂.upperStar (pullback.snd h₁ h₂)).of_iso ?_)
  exact ((upperStarComp _ _ h₂).app M).symm ≪≫
    (upperStarCongr _ pullback.condition.symm).app M ≪≫ (upperStarComp _ _ h₁).app M

variable (ℓ M) in
/-- The *rank function* of `M`: its value at `z` is the fibre rank at a point over `z` of any
pullback of `M` having a fibre rank there (`0` if there is none). It does not depend on the
choice (`ProEtale.CondensedRing.HasFiberRank.eq_fiberRankFun`). -/
noncomputable def fiberRankFun (z : X) : ℕ :=
  sInf {d | ∃ (W : Scheme.{u}) (g : W ⟶ X) (w : W), g w = z ∧
    HasFiberRank ℓ ((g)^*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧.obj M) w d}

/-- The fibre rank of a pullback of `M` is the value of the rank function. -/
lemma HasFiberRank.eq_fiberRankFun {W : Scheme.{u}} (g : W ⟶ X) {w : W} {d : ℕ}
    (H : HasFiberRank ℓ ((g)^*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧.obj M) w d) :
    d = fiberRankFun ℓ M (g w) := by
  have hmem : d ∈ {d | ∃ (W' : Scheme.{u}) (g' : W' ⟶ X) (w' : W'), g' w' = g w ∧
      HasFiberRank ℓ ((g')^*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧.obj M) w' d} := ⟨W, g, w, rfl, H⟩
  obtain ⟨W', g', w', hw', H'⟩ := Nat.sInf_mem ⟨d, hmem⟩
  exact H.eq_of_apply_eq g g' hw'.symm H'

end FiberRank

section Charts

variable {X : Scheme.{u}}
  {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X)}

/-- The members of a pro-étale cover are jointly surjective. -/
lemma _root_.AlgebraicGeometry.Scheme.Cover.exists_eq_of_proetale
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X) (x : X) : ∃ i y, 𝒰.f i y = x :=
  Scheme.Cover.exists_eq
    (𝒰.weaken (inf_le_right : Scheme.proetalePrecoverage ≤ Scheme.precoverage @WeaklyEtale)) x

/-- If the pullback of `M` along `g : Y ⟶ X` is finitely presented, every point of `Y` lies in an
affine open subscheme, over which the pullback of `M` is finitely presented. -/
lemma exists_isOpenImmersion_isFinitelyPresented {Y : Scheme.{u}} (g : Y ⟶ X)
    (hM : Mod.IsFinitelyPresented (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) Y)
      ((g)^*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧.obj M)) (y : Y) :
    ∃ (W : Scheme.{u}) (_ : IsAffine W) (i₀ : W ⟶ Y) (_ : IsOpenImmersion i₀) (w : W), i₀ w = y ∧
      Mod.IsFinitelyPresented (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) W)
        ((i₀ ≫ g)^*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧.obj M) := by
  obtain ⟨w, hw⟩ := Y.affineCover.covers y
  exact ⟨_, inferInstance, Y.affineCover.f (Y.affineCover.idx y), inferInstance, w, hw,
    (IsFinitelyPresented.upperStar _ _ hM).of_iso ((upperStarComp _ _ g).app M).symm⟩

/-- Pullback along a member of a pro-étale cover over which `M` is finitely presented, in the sense
of `ProEtale.IsLocallyFinitelyPresented`, is finitely presented as a module over `ℚ̲̄_ℓ`. -/
lemma isFinitelyPresented_upperStar_of_isLocallyFinitelyPresented
    {𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X}
    (h𝒰 : ∀ i : 𝒰.I₀, Mod.IsFinitelyPresented
      ((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).obj
        (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X))
      (((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).mapMod
        (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X)).obj M)) (i : 𝒰.I₀) :
    Mod.IsFinitelyPresented (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) (𝒰.X i))
      ((𝒰.f i)^*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧.obj M) :=
  isFinitelyPresented_upperStar_of_comap_iso _ (𝒰.f i) (𝟙 _) ((Mod.comapId _).app M) (h𝒰 i)

/-- A module object whose pullback over `ℚ̲̄_ℓ` is free is free in the sense of
`ProEtale.IsLocallyFree`, as a module over the sheaf pullback of `ℚ̲̄_ℓ,X`. -/
lemma isFree_mapMod_of_isFree {Y : Scheme.{u}} (f : Y ⟶ X)
    (h : Mod.IsFree (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) Y)
      ((f)^*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧.obj M)) :
    Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} f).obj
        (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X))
      (((ProEtale.upperStar Ab.{u + 1} f).mapMod
        (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X)).obj M) := by
  obtain ⟨d, ⟨e⟩⟩ := h
  let α := condensedPullbackHom (Profinite.padicAlgClRingObj.{u} ℓ) f
  exact ⟨d, ⟨(comapUpperStarObjIso _ f M).symm ≪≫ (Mod.comap α).mapIso e ≪≫
    Mod.finiteFreeIsoMap (Mod.comap α)
      ((Mod.comapCongr (IsIso.inv_inv (f := α)).symm).app _ ≪≫ Mod.regularIsoOfIsIso (inv α)) d⟩⟩

end Charts

section FiniteType

variable {k : Type u} [Field k] (Z : Over (Spec (.of k))) [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom]

omit [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] in
/-- **The rank function is constant along specializations.** Lift the specialization to a chart
`h : W ⟶ Z` (flatness of `h`); the entries of the presentation of `h^* M` take the same values at
both points, and the fibre ranks only depend on these values. -/
lemma fiberRankFun_eq_of_specializes
    {M : Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) Z.left)}
    (hM : IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z.left)
      M) {z₁ z₂ : Z.left} (hz : z₁ ⤳ z₂) : fiberRankFun ℓ M z₁ = fiberRankFun ℓ M z₂ := by
  obtain ⟨𝒰, h𝒰⟩ := hM
  obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq_of_proetale z₂
  obtain ⟨W, _, i₀, _, w₂, rfl, ⟨n, m, φ, ⟨e⟩⟩⟩ := exists_isOpenImmersion_isFinitelyPresented
    (𝒰.f i) (isFinitelyPresented_upperStar_of_isLocallyFinitelyPresented h𝒰 i) y
  have : WeaklyEtale (𝒰.f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ 𝒰.mem₀ (.mk i)
  rw [← Scheme.Hom.comp_apply] at hz ⊢
  obtain ⟨w₁, hw, rfl⟩ := Flat.generalizingMap (i₀ ≫ 𝒰.f i) hz
  -- the matrix of values of `φ` at `w₁` and `w₂`, realized over `Spec k`
  choose t ht using fun (a : Fin n) (b : Fin m) ↦
    exists_endValue_eq_const (W := Spec (.of k)) (endValue ℓ (Mod.finFreeEntry φ a b) w₁)
  let ψ : Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) (Spec (.of k))) m ⟶
      Mod.finiteFree _ n := biproduct.matrix fun b a ↦ (t a b).asHom
  have hψ (a : Fin n) (b : Fin m) : Mod.finFreeEntry ψ a b = t a b := by
    apply End.ext
    simp [ψ, Mod.finFreeEntry]
  obtain ⟨d, -, -, ⟨e'⟩⟩ := exists_le_iso_cokernel_biproduct_fin
    (isIso_of_ne_zero_of_subsingleton (W := Spec (.of k))) ψ
  obtain ⟨pt⟩ : Nonempty (Spec (.of k)) := inferInstance
  have H (x : W) (hx : ∀ a b, endValue ℓ (Mod.finFreeEntry φ a b) x =
      endValue ℓ (Mod.finFreeEntry φ a b) w₁) : d = fiberRankFun ℓ M ((i₀ ≫ 𝒰.f i) x) :=
    ((hasFiberRank_cokernel_of_endValue_eq φ ψ x pt
      (W.fromSpecResidueField x ≫ i₀ ≫ 𝒰.f i ≫ Z.hom) (fun a b ↦ by rw [hψ, ht, hx])
      e').of_iso e.symm).eq_fiberRankFun (i₀ ≫ 𝒰.f i)
  -- the entries of `φ` are continuous, so they take the same values at `w₁` and `w₂`
  exact (H w₁ fun _ _ ↦ rfl).symm.trans
    (H w₂ fun a b ↦ ((hw.map (continuous_endValue _)).eq).symm)

/-- **The rank function is locally constant**, `Z` being noetherian. -/
lemma isLocallyConstant_fiberRankFun
    {M : Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) Z.left)}
    (hM : IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z.left)
      M) : IsLocallyConstant (fiberRankFun ℓ M) := by
  have : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  have : IsNoetherian Z.left := ⟨⟩
  exact TopologicalSpace.NoetherianSpace.isLocallyConstant_of_specializes fun _ _ h ↦
    fiberRankFun_eq_of_specializes Z hM h

/-- **Local freeness over a chart.** If `M` is locally finitely presented and its pullback along
`g : Y ⟶ Z` is finitely presented, every point of `Y` has an open neighbourhood over which the
pullback of `M` is free: on an affine open neighbourhood `W`, the pullback is the cokernel of a
matrix `φ`, of constant fibre rank on the clopen subset of `W` where the rank function of `M`
takes its value at the given point; conclude by Gaussian elimination. -/
lemma exists_isOpenImmersion_isFree
    {M : Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) Z.left)}
    (hM : IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z.left)
      M) {Y : Scheme.{u}} (g : Y ⟶ Z.left)
    (hg : Mod.IsFinitelyPresented (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) Y)
      ((g)^*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧.obj M)) (y : Y) :
    ∃ (V : Scheme.{u}) (j : V ⟶ Y) (_ : IsOpenImmersion j), y ∈ Set.range j ∧
      Mod.IsFree (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) V)
        ((j ≫ g)^*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧.obj M) := by
  obtain ⟨W, _, i₀, _, w, rfl, ⟨n, m, φ, ⟨e⟩⟩⟩ := exists_isOpenImmersion_isFinitelyPresented g hg y
  have hrank (v : W) : HasFiberRank ℓ (cokernel φ) v (fiberRankFun ℓ M ((i₀ ≫ g) v)) := by
    obtain ⟨d, hd⟩ := exists_hasFiberRank_cokernel φ v
    rwa [← (hd.of_iso e.symm).eq_fiberRankFun (i₀ ≫ g)]
  have hS := ((isLocallyConstant_fiberRankFun Z hM).isClopen_fiber
    (fiberRankFun ℓ M ((i₀ ≫ g) w))).preimage (i₀ ≫ g).continuous
  let U : W.Opens := ⟨_, hS.isOpen⟩
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hS.isClosed.isCompact
  have : QuasiSeparatedSpace U.toScheme := U.ι.isOpenEmbedding.quasiSeparatedSpace
  have hd (v : U.toScheme) : HasFiberRank ℓ (cokernel (upperStarFinFreeMap _ U.ι φ)) v
      (fiberRankFun ℓ M ((i₀ ≫ g) w)) := by
    have hv : fiberRankFun ℓ M ((i₀ ≫ g) (U.ι v)) = fiberRankFun ℓ M ((i₀ ≫ g) w) := v.2
    rw [← hv]
    exact ((hrank (U.ι v)).upperStar U.ι).of_iso (cokernelUpperStarFinFreeMapIso _ U.ι φ).symm
  obtain ⟨V, j, _, ⟨v, hv⟩, ⟨e'⟩⟩ :=
    exists_isOpenImmersion_cokernel_iso_finiteFree n _ hd (⟨w, rfl⟩ : U)
  refine ⟨V, j ≫ U.ι ≫ i₀, inferInstance, ⟨v, ?_⟩, fiberRankFun ℓ M ((i₀ ≫ g) w),
    ⟨(upperStarCongr _ (by simp only [Category.assoc])).app M ≪≫
      (upperStarComp _ j (U.ι ≫ i₀ ≫ g)).app M ≪≫
      (j)^*⟦_⟧.mapIso ((upperStarComp _ U.ι (i₀ ≫ g)).app M ≪≫ (U.ι)^*⟦_⟧.mapIso e ≪≫
        (cokernelUpperStarFinFreeMapIso _ U.ι φ).symm) ≪≫ e'⟩⟩
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hv, Scheme.Opens.ι_apply]

end FiniteType

/-- **A pro-étale locally finitely presented `ℚ̲̄_ℓ`-module on a separated `k`-scheme of finite type
is locally free** (the lisse `ℚ̄_ℓ`-sheaves of Bhatt–Scholze, Definition 6.8.6), proved from the
description of the sections of `ℚ̲̄_ℓ` (`ProEtale.CondensedRing.exists_endRegularRingEquiv`).
Refine a pro-étale cover over which `M` is finitely presented by the Zariski covers of its
members given by `ProEtale.CondensedRing.exists_isOpenImmersion_isFree`. -/
theorem isLocallyFree_of_isLocallyFinitelyPresented (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u}
    [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] (Z : Over (Spec (.of k)))
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    {M : Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z.left)}
    (hM : IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z.left)
      M) :
    IsLocallyFree (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z.left) M := by
  obtain ⟨𝒰, h𝒰⟩ := id hM
  refine IsLocallyFree.of_forall_exists_isOpenImmersion 𝒰 fun i y ↦ ?_
  obtain ⟨V, j, hj, hy, hfree⟩ := exists_isOpenImmersion_isFree Z hM (𝒰.f i)
    (isFinitelyPresented_upperStar_of_isLocallyFinitelyPresented h𝒰 i) y
  exact ⟨V, j, hj, hy, isFree_mapMod_of_isFree _ hfree⟩

end AlgebraicGeometry.ProEtale.CondensedRing
