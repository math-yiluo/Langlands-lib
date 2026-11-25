/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.NearbyCycles.OpenExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BaseChangePaste
public import WeilConjectures.TraceFormula.OpenCover

/-!

# Reduction of the smooth pullback exchange of nearby cycles to affine spaces

Let `g ≫ j_Y = j_X ≫ t` be a cartesian square of schemes with `t : X ⟶ Y` smooth. This file reduces
the invertibility of the base change morphism `Lt^* Rj_{Y*} ⟶ Rj_{X*} Lg^*` at an object `E` to the
case of the projections `𝔸ⁿ_Y ⟶ Y`
(`ProEtale.CondensedRing.isIso_baseChangeMap_app_of_smooth`), and the invertibility of the
pullback exchange of nearby cycles at `K` to that of the base change morphism of the square of
geometric generic fibres at `Lε^* K`
(`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_isIso_baseChangeMap_app`).

## Main results

- `ProEtale.CondensedRing.isIso_baseChangeMap_app_paste_iff`: pointwise pasting of base change
  morphisms along a square with invertible base change morphism.
- `ProEtale.CondensedRing.isIso_baseChangeMap_app_of_smooth`: the reduction to affine spaces, by
  joint conservativity of the pullbacks along a finite affine open cover and weakly étale base
  change along the étale charts.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

set_option hygiene false in
/-- The derived category `D(X_proét, Λ) = D(Mod_{Λ_X})` of module objects over `Λ_X`. -/
local notation "𝔻(" X ")" =>
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section Paste

variable {X Y X' Y' X'' Y'' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
  {g' : X' ⟶ X} {h : Y'' ⟶ Y'} {h' : X'' ⟶ X'} {f'' : X'' ⟶ Y''}

/-- **Pointwise pasting of base change morphisms**: for two horizontally pasted squares
```
X'' --h'--> X' --g'--> X
 |f''       |f'        |f
 v          v          v
Y'' --h---> Y' --g---> Y
```
such that the base change morphism of the left square `sq₂` is invertible, the base change
morphism of the outer square is invertible at `M` if and only if `Lh^*` of the base change
morphism of the right square `sq₁` at `M` is invertible. -/
theorem isIso_baseChangeMap_app_paste_iff (sq₁ : CommSq g' f' f g) (sq₂ : CommSq h' f'' f' h)
    (sq : CommSq (h' ≫ g') f'' f (h ≫ g)) [IsIso (baseChangeMap Λ sq₂)] (M : 𝔻(X)) :
    IsIso ((baseChangeMap Λ sq).app M) ↔
      IsIso ((L((h)^*⟦Λ⟧)).map ((baseChangeMap Λ sq₁).app M)) := by
  -- Infer horizontal functors from the comparisons to avoid repeated instance synthesis.
  have key := Adjunction.isIso_exchangeRight_app_paste_iff
    (derivedUpperStarLowerStarAdjunction Λ f)
    (derivedUpperStarLowerStarAdjunction Λ f') (derivedUpperStarLowerStarAdjunction Λ f'')
    (pullbackSquareComparison Λ sq₁) (pullbackSquareComparison Λ sq₂)
    (pullbackSquareComparison Λ sq) (leftDerivedUpperStarComp Λ h g)
    (leftDerivedUpperStarComp Λ h' g') (pullbackSquareComparison_paste Λ sq₁ sq₂ sq) ‹_› M
  have e : baseChangeMap Λ sq = Adjunction.exchangeRight (derivedUpperStarLowerStarAdjunction Λ f)
      (derivedUpperStarLowerStarAdjunction Λ f'') (pullbackSquareComparison Λ sq) := rfl
  have e₁ : baseChangeMap Λ sq₁ = Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction Λ f) (derivedUpperStarLowerStarAdjunction Λ f')
      (pullbackSquareComparison Λ sq₁) := rfl
  rw [e, e₁]
  exact key

/-- The base change morphisms of two commutative squares with the same vertical maps and equal
horizontal maps are simultaneously invertible at every object. -/
lemma isIso_baseChangeMap_app_congr {X Y X' Y' : Scheme.{u}} {p : X ⟶ Y} {p' : X' ⟶ Y'}
    {g₁ g₂ : Y' ⟶ Y} {g₁' g₂' : X' ⟶ X} (sq₁ : CommSq g₁' p' p g₁) (sq₂ : CommSq g₂' p' p g₂)
    (e : g₁ = g₂) (e' : g₁' = g₂') (M : 𝔻(X)) :
    IsIso ((baseChangeMap Λ sq₁).app M) ↔ IsIso ((baseChangeMap Λ sq₂).app M) := by
  subst e e'
  rw [Subsingleton.elim sq₁ sq₂]

end Paste

/-! ### Reduction of smooth base change to affine spaces -/

section Smooth

variable {X Y XΩ YΩ : Scheme.{u}} {t : X ⟶ Y} {jX : XΩ ⟶ X} {jY : YΩ ⟶ Y} {g : XΩ ⟶ YΩ}

/-- The étale-local step of smooth base change, for abstract squares: in the diagram of
commutative squares
```
W_Ω --ι_Ω--> X_Ω --g--> Y_Ω      W_Ω --e_Ω--> A_Ω --π_Ω--> Y_Ω
 |j_W         |j_X       |j_Y      |j_W         |j_A          |j_Y
 v            v          v         v            v             v
 W  ---ι--->  X  --t-->  Y         W  ---e--->  A  ---π--->   Y
```
with `ι ≫ t = e ≫ π`, `ι_Ω ≫ g = e_Ω ≫ π_Ω`, and cartesian squares of `ι` and `e` with `ι`, `ι_Ω`,
`e`, `e_Ω` weakly étale, if the base change morphism of the square of `π` is invertible at `E`,
then so is `Lι^*` of the base change morphism of the square of `t` at `E`. -/
theorem isIso_map_baseChangeMap_app_of_paste {W WΩ A AΩ : Scheme.{u}} {ι : W ⟶ X}
    {ιΩ : WΩ ⟶ XΩ} {jW : WΩ ⟶ W} {π : A ⟶ Y} {πΩ : AΩ ⟶ YΩ} {jA : AΩ ⟶ A} {e : W ⟶ A}
    {eΩ : WΩ ⟶ AΩ} (sq : CommSq g jX jY t) (sqι : IsPullback ιΩ jW jX ι)
    (sqA : CommSq πΩ jA jY π) (sqe : IsPullback eΩ jW jA e) (h : ι ≫ t = e ≫ π)
    (hΩ : ιΩ ≫ g = eΩ ≫ πΩ) [WeaklyEtale ι] [WeaklyEtale ιΩ] [WeaklyEtale e] [WeaklyEtale eΩ]
    (E : 𝔻(YΩ)) (hE : IsIso ((baseChangeMap Λ sqA).app E)) :
    IsIso ((L((ι)^*⟦Λ⟧)).map ((baseChangeMap Λ sq).app E)) := by
  have := isIso_baseChangeMap_of_weaklyEtale Λ sqι
  have := isIso_baseChangeMap_of_weaklyEtale Λ sqe
  rw [← isIso_baseChangeMap_app_paste_iff Λ sq sqι.toCommSq (sqι.toCommSq.horiz_comp sq) E,
    isIso_baseChangeMap_app_congr Λ (sqι.toCommSq.horiz_comp sq) (sqe.toCommSq.horiz_comp sqA) h hΩ,
    isIso_baseChangeMap_app_paste_iff Λ sqA sqe.toCommSq (sqe.toCommSq.horiz_comp sqA) E]
  infer_instance

/-- **Étale-local step of smooth base change**: let `g ≫ j_Y = j_X ≫ t` be a cartesian square,
`ι : W ⟶ X` an open immersion and `e : W ⟶ 𝔸ⁿ_Y` an étale morphism with `e ≫ π = ι ≫ t`, for the
projection `π : 𝔸ⁿ_Y ⟶ Y`. If the base change morphism of the square of `j_Y` along `π` is
invertible at `E`, then so is the restriction along `ι` of the base change morphism of the square
`g ≫ j_Y = j_X ≫ t` at `E`: both are related through weakly étale base change along `ι` and `e`. -/
theorem isIso_map_baseChangeMap_app_of_etale_affineSpace (hj : IsPullback g jX jY t)
    (E : 𝔻(YΩ)) {W : Scheme.{u}} (ι : W ⟶ X) [IsOpenImmersion ι] {n : ℕ}
    (e : W ⟶ 𝔸(ULift.{u} (Fin n); Y)) [Etale e] (he : e ≫ 𝔸(ULift.{u} (Fin n); Y) ↘ Y = ι ≫ t)
    (hA : IsIso ((baseChangeMap Λ
      (IsPullback.of_hasPullback jY (𝔸(ULift.{u} (Fin n); Y) ↘ Y)).toCommSq).app E)) :
    IsIso ((L((ι)^*⟦Λ⟧)).map ((baseChangeMap Λ hj.toCommSq).app E)) := by
  have h₁ := IsPullback.of_hasPullback jX ι
  let e' := pullback.lift (pullback.fst jX ι ≫ g) (pullback.snd jX ι ≫ e) (by
    simp only [Category.assoc]
    rw [hj.w, pullback.condition_assoc, he])
  have hout : IsPullback (e' ≫ pullback.fst jY (𝔸(ULift.{u} (Fin n); Y) ↘ Y))
      (pullback.snd jX ι) jY (e ≫ 𝔸(ULift.{u} (Fin n); Y) ↘ Y) := by
    rw [pullback.lift_fst, he]
    exact h₁.paste_horiz hj
  have hleft : IsPullback e' (pullback.snd jX ι)
      (pullback.snd jY (𝔸(ULift.{u} (Fin n); Y) ↘ Y)) e :=
    IsPullback.of_right hout (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  have : WeaklyEtale e' :=
    MorphismProperty.of_isPullback (P := @WeaklyEtale) hleft.flip inferInstance
  have : WeaklyEtale (pullback.fst jX ι) :=
    MorphismProperty.of_isPullback (P := @WeaklyEtale) h₁.flip inferInstance
  exact isIso_map_baseChangeMap_app_of_paste Λ hj.toCommSq h₁
    (IsPullback.of_hasPullback jY (𝔸(ULift.{u} (Fin n); Y) ↘ Y)).toCommSq hleft he.symm
    (pullback.lift_fst _ _ _).symm E hA

/-- **Reduction of smooth base change to affine spaces**: let `g ≫ j_Y = j_X ≫ t` be a cartesian
square with `t` smooth and `X` quasi-compact and quasi-separated, and let `E` be a complex on the
source of `j_Y`. If, for every `n`, the base change morphism of the square of `j_Y` along the
projection `𝔸ⁿ_Y ⟶ Y` is invertible at `E`, then the base change morphism
`Lt^* Rj_{Y*} E ⟶ Rj_{X*} Lg^* E` is invertible. Indeed `t` is, locally on `X`, étale over some
`𝔸ⁿ_Y` (`AlgebraicGeometry.Smooth.exists_etale_affineSpace`); the pullbacks along a finite
affine open cover jointly reflect isomorphisms, and the étale-local step is
`isIso_map_baseChangeMap_app_of_etale_affineSpace`. -/
theorem isIso_baseChangeMap_app_of_smooth [Smooth t] [CompactSpace X] [QuasiSeparatedSpace X]
    (hj : IsPullback g jX jY t) (E : 𝔻(YΩ))
    (hA : ∀ n : ℕ, IsIso ((baseChangeMap Λ
      (IsPullback.of_hasPullback jY (𝔸(ULift.{u} (Fin n); Y) ↘ Y)).toCommSq).app E)) :
    IsIso ((baseChangeMap Λ hj.toCommSq).app E) := by
  choose W ι hι hW hx n e he hte using Smooth.exists_etale_affineSpace t
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ Set.range (ι x).base)
    (fun x ↦ (ι x).isOpenEmbedding.isOpen_range) fun x _ ↦ Set.mem_iUnion.2 ⟨x, hx x⟩
  have (a : s) : QuasiCompact (ι a) := by
    have := hW a
    infer_instance
  have hP := jointlyReflectIsomorphisms_leftDerivedUpperStar_of_cover Λ (fun a : s ↦ ι a)
    fun x ↦ by
      obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
      exact ⟨⟨a, ha⟩, hxa⟩
  have (a : s) := isIso_map_baseChangeMap_app_of_etale_affineSpace Λ hj E (ι a) (e a) (hte a)
    (hA _)
  exact hP.isIso _

end Smooth

/-! ### The pullback exchange at an object -/

namespace NearbyCyclesModel.Hom

/-- A transformation `α = θi ≫ I_M(E_N^*β ≫ J_{M*}θε)` of the shape of the pullback exchange, with
`θi` and `θε` invertible, is invertible at `o` if `β` is invertible at `E_N o`; `β` is given
together with `β'`, invertible at `E_N o`, and a proof of `β' = β`. -/
private lemma isIso_pullbackExchange_app_aux
    {DY' DX' DTN DTM DGN DGM DY DX : Type*} [Category DY'] [Category DX'] [Category DTN]
    [Category DTM] [Category DGN] [Category DGM] [Category DY] [Category DX]
    {Fp' : DY' ⥤ DX'} {IN : DTN ⥤ DY'} {IM : DTM ⥤ DX'} {T : DTN ⥤ DTM}
    {JNs : DGN ⥤ DTN} {JMs : DGM ⥤ DTM} {G : DGN ⥤ DGM} {EN : DY ⥤ DGN} {EM : DX ⥤ DGM}
    {F : DY ⥤ DX} (θi : IN ⋙ Fp' ⟶ T ⋙ IM) [IsIso θi] (β β' : JNs ⋙ T ⟶ G ⋙ JMs)
    (h : β' = β) (θε : EN ⋙ G ⟶ F ⋙ EM) [IsIso θε]
    (α : (EN ⋙ JNs ⋙ IN) ⋙ Fp' ⟶ F ⋙ EM ⋙ JMs ⋙ IM)
    (hα : α = Functor.whiskerLeft (EN ⋙ JNs) θi ≫
      Functor.whiskerRight (Functor.whiskerLeft EN β ≫ Functor.whiskerRight θε JMs) IM)
    (o : DY) (hβ : IsIso (β'.app (EN.obj o))) : IsIso (α.app o) := by
  subst h hα
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

variable {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'} (φ : M.Hom N f f')

/-- **The pullback exchange at an object**: if the base change morphism
`Lt^* Rj_{N*} ⟶ Rj_{M*} Lg^*` of the square of geometric generic fibres of a morphism of models
is invertible at `Lε_N^* K`, then the pullback exchange `α_f` is invertible at `K`. -/
theorem isIso_pullbackExchange_app_of_isIso_baseChangeMap_app (K : 𝔻(Y))
    (hK : IsIso ((baseChangeMap Λ φ.commSq_j).app ((L((N.ε)^*⟦Λ⟧)).obj K))) :
    IsIso ((φ.pullbackExchange Λ).app K) :=
  isIso_pullbackExchange_app_aux (pullbackSquareComparison Λ φ.commSq_i).hom
    (mateEquiv (derivedUpperStarLowerStarAdjunction Λ N.j)
      (derivedUpperStarLowerStarAdjunction Λ M.j)
      (pullbackSquareComparison Λ φ.commSq_j).hom)
    (baseChangeMap Λ φ.commSq_j) (φ.baseChangeMap_commSq_j_eq_mateEquiv Λ)
    (pullbackSquareComparison Λ φ.commSq_ε).hom (φ.pullbackExchange Λ) rfl K hK

end NearbyCyclesModel.Hom

end AlgebraicGeometry.ProEtale.CondensedRing
