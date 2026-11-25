/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.UpperStarLimits.Sections

/-!
# Sections of pullbacks over affine objects with split affine covers

Let `g : Z ⟶ Y` be a morphism of schemes such that every object `V` of `Z_proét` which is affine
with split affine covers (`AlgebraicGeometry.Scheme.AffineCoversSplit`) has a weakly étale hull
`V ⟶ W₀ ⟶ Y`. Then for such `V` the sections of the pullback `g^* F` of a pro-étale sheaf of
modules `F` over `V` are naturally the sections of `F` over `W₀`
(`AlgebraicGeometry.ProEtale.isIso_hullSectionsNatTrans`).

Every covering of `V` is refined by a finite decomposition `V = ∐ Tᵢ` into open and closed pieces
(`AlgebraicGeometry.ProEtale.exists_finite_clopen_cover`), which are again affine with split
affine covers. The hull of `V` is the disjoint union of the hulls of the `Tᵢ`, so the presheaf
pullback `P = Lan F` satisfies `P(V) = ∏ P(Tᵢ)`
(`AlgebraicGeometry.ProEtale.bijective_lan_map_of_isColimit_cofan`), and sheafification does not
change `P(V)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- Every covering sieve of an object `V` of `X_proét` which is affine with split affine covers
contains the inclusions of a finite decomposition of `V` into disjoint open and closed
subschemes. -/
lemma exists_finite_clopen_cover {X : Scheme.{u}} {V : X.ProEt} [IsAffine V.left]
    (hV : V.left.AffineCoversSplit) {S : Sieve V} (hS : S ∈ ProEt.topology X V) :
    ∃ (ι : Type u) (_ : Finite ι) (O : ι → V.left.Opens),
      (∀ i, S (ProEt.ofOpenImmersionHom V (O i).ι)) ∧ (∀ x, ∃ i, x ∈ O i) ∧
        (∀ i j, i ≠ j → Disjoint (O i) (O j)) ∧ ∀ i, IsClopen (O i : Set V.left) := by
  obtain ⟨κ, O, hdisj, hcov, hO⟩ :=
    ProEt.exists_disjoint_opens_of_forall_exists_retraction (R := Γ(V.left, ⊤))
      (hV.of_iso V.left.isoSpec).exists_retraction V.left.isoSpec hS
  let ι := {k : κ // (O k : Set V.left).Nonempty}
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun k ↦ (O k : Set V.left))
    (fun k ↦ (O k).isOpen) (fun x _ ↦ Set.mem_iUnion.2 (hcov x))
  have hmem (i : ι) : i.1 ∈ t := by
    obtain ⟨x, hx⟩ := i.2
    obtain ⟨k, hk, hxk⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    by_cases h : i.1 = k
    · rwa [h]
    · exact ((disjoint_iff.1 (hdisj _ _ h)).le ⟨hx, hxk⟩).elim
  have : Finite ι := Finite.of_injective (β := t) (fun i ↦ ⟨i.1, hmem i⟩)
    (fun i j h ↦ Subtype.ext (by simpa using congrArg Subtype.val h))
  refine ⟨ι, this, fun i ↦ O i.1, fun i ↦ hO i.1, fun x ↦ ?_, fun i j hij ↦
    hdisj _ _ fun h ↦ hij (Subtype.ext h), fun i ↦ ⟨⟨?_⟩, (O i.1).isOpen⟩⟩
  · obtain ⟨k, hk⟩ := hcov x
    exact ⟨⟨k, x, hk⟩, hk⟩
  · have : (O i.1 : Set V.left)ᶜ = ⋃ l ∈ {l | l ≠ i.1}, (O l : Set V.left) := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
      refine ⟨fun hx ↦ ?_, fun ⟨l, hl, hx⟩ hx' ↦ (disjoint_iff.1 (hdisj l i.1 hl)).le ⟨hx, hx'⟩⟩
      obtain ⟨l, hl⟩ := hcov x
      exact ⟨l, fun h ↦ hx (h ▸ hl), hl⟩
    rw [this]
    exact isOpen_biUnion fun l _ ↦ (O l).isOpen

variable {R : Type (u + 1)} [Ring R] {Z Y : Scheme.{u}} (g : Z ⟶ Y) {V : Z.ProEt} {W₀ : Y.ProEt}
  {ψ : V.left ⟶ W₀.left}

/-- **The presheaf pullback on a disjoint union.** If `V` is the disjoint union of finitely many
`Tᵢ` and all of them have hulls, the presheaf pullback `P = Lan F` of a sheaf `F` satisfies
`P(V) = ∏ P(Tᵢ)`: the hull of `V` is the disjoint union of the hulls of the `Tᵢ`. -/
lemma bijective_lan_map_of_isColimit_cofan (hψ : ProEt.IsHull (V.hom ≫ g) W₀ ψ) {ι : Type u}
    [Finite ι] {T : ι → Z.ProEt}
    (f : ∀ i, T i ⟶ V) (hf : IsColimit (Cofan.mk V.left fun i ↦ (f i).left)) {W : ι → Y.ProEt}
    {ψ' : ∀ i, (T i).left ⟶ (W i).left} (hψ' : ∀ i, ProEt.IsHull ((T i).hom ≫ g) (W i) (ψ' i))
    (F : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R)) :
    Function.Bijective (fun (x : ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.lan.obj
      F.obj).obj (op V)) i ↦
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.lan.obj F.obj).map (f i).op x) := by
  have hsi (i : ι) : ∃ s : W i ⟶ W₀, ψ' i ≫ s.left = (f i).left ≫ ψ :=
    ((hψ' i).2 W₀ ((f i).left ≫ ψ) (by
      rw [Category.assoc, hψ.1, ← Category.assoc, MorphismProperty.Over.w (f i)])).exists
  choose s hs using hsi
  have hψ'' (i : ι) : ProEt.IsHull ((f i).left ≫ V.hom ≫ g) (W i) (ψ' i) := by
    rw [← Category.assoc, MorphismProperty.Over.w (f i)]
    exact hψ' i
  obtain ⟨hc⟩ := ProEt.nonempty_isColimit_cofan_of_isHull (fun i ↦ (f i).left) hf (V.hom ≫ g) hψ
    hψ'' s hs
  have hρ := bijective_moduleCat_of_isLimit_fan _ (isLimitSectionsFanOfIsColimitCofan F s hc)
  have : IsIso (hullLanMap g hψ F.obj) := isIso_hullLanMap g hψ F.obj
  have hθ : Function.Bijective (hullLanMap g hψ F.obj) :=
    (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  have hθ' : Function.Bijective (fun (y : ∀ i, F.obj.obj (op (W i))) i ↦
      hullLanMap g (hψ' i) F.obj (y i)) :=
    Function.Bijective.piMap fun i ↦ by
      have : IsIso (hullLanMap g (hψ' i) F.obj) := isIso_hullLanMap g (hψ' i) F.obj
      exact (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  rw [← Function.Bijective.of_comp_iff _ hθ]
  convert hθ'.comp hρ using 1
  funext y i
  exact ConcreteCategory.congr_hom (hullLanMap_comp_map g hψ F.obj (f i) (hψ' i) (s i) (hs i)) y

/-- **Sheafification at an affine object with split affine covers.** If every affine object of
`Z_proét` with split affine covers has a hull, the sheafification map of the presheaf pullback
`P = Lan F` is bijective on sections over such objects. -/
lemma bijective_toSheafify_lan_app (hψ : ProEt.IsHull (V.hom ≫ g) W₀ ψ) [IsAffine V.left]
    (hV : V.left.AffineCoversSplit)
    (hhull : ∀ V' : Z.ProEt, IsAffine V'.left → V'.left.AffineCoversSplit →
      ∃ W ψ', ProEt.IsHull (V'.hom ≫ g) W ψ')
    (F : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R)) :
    Function.Bijective ((toSheafify (ProEt.topology Z)
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.lan.obj F.obj)).app (op V)) := by
  refine bijective_toSheafify_app_of_forall _ V fun S hS ↦ ?_
  obtain ⟨ι, _, O, hSO, hcov, hdisj, hclopen⟩ := exists_finite_clopen_cover hV hS
  let T (i : ι) : Z.ProEt := ProEt.ofOpenImmersion V (O i).ι
  have hT (i : ι) : IsAffine (T i).left := AffineCoversSplit.isAffineOpen_of_isClopen (hclopen i)
  choose W ψ' hψ' using fun i ↦ hhull (T i) (hT i) (hV.of_isClopen (hclopen i))
  obtain ⟨hc⟩ := nonempty_isColimit_cofanMk_of (fun i ↦ (O i).ι)
    (by
      rw [eq_top_iff]
      intro x _
      obtain ⟨i, hi⟩ := hcov x
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, by rwa [Scheme.Opens.opensRange_ι]⟩)
    (fun i j hij ↦ by simpa [Function.onFun] using hdisj i j hij)
  refine ⟨ι, T, fun i ↦ ProEt.ofOpenImmersionHom V (O i).ι, hSO, ?_,
    bijective_lan_map_of_isColimit_cofan g hψ _ hc hψ' F⟩
  exact ProEt.mem_topology_of_openImmersion _ (fun i ↦ (O i).ι)
    (fun x ↦ by obtain ⟨i, hi⟩ := hcov x; exact ⟨i, by rwa [Scheme.Opens.range_ι]⟩)
    (fun i ↦ Sieve.ofArrows_mk _ _ i)

/-- The comparison map `F(W₀) ⟶ (g^* F)(V)` for a hull `W₀` of `V ⟶ Y`, natural in `F`: the
value at `V` of the unit `F ⟶ g_* g^* F` at `W₀`, restricted along `V ⟶ W₀ ×_Y Z`. -/
noncomputable def hullSectionsNatTrans (hψ : ProEt.IsHull (V.hom ≫ g) W₀ ψ) :
    sheafToPresheaf (ProEt.topology Y) (ModuleCat.{u + 1} R) ⋙
        (CategoryTheory.evaluation _ _).obj (op W₀) ⟶
      (g)^*[ModuleCat.{u + 1} R] ⋙ sheafToPresheaf (ProEt.topology Z) (ModuleCat.{u + 1} R) ⋙
        (CategoryTheory.evaluation _ _).obj (op V) where
  app F := hullLanMap g hψ F.obj ≫ (toSheafify (ProEt.topology Z)
    ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.lan.obj F.obj)).app (op V)
  naturality F F' φ := by
    have h₁ := NatTrans.congr_app (toSheafify_naturality (ProEt.topology Z)
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.lan.map φ.hom)) (op V)
    rw [NatTrans.comp_app, NatTrans.comp_app] at h₁
    have h₂ : (sheafToPresheaf (ProEt.topology Y) (ModuleCat.{u + 1} R) ⋙
        (CategoryTheory.evaluation _ _).obj (op W₀)).map φ ≫
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.lanUnit.app F'.obj).app (op W₀) =
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.lanUnit.app F.obj).app (op W₀) ≫
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.lan.map φ.hom).app
          (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj W₀)) :=
      NatTrans.congr_app
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.lanUnit.naturality φ.hom) (op W₀)
    have h₃ := ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.lan.map φ.hom).naturality
      (hullHom g hψ).op
    rw [hullLanMap, hullLanMap, Category.assoc, Category.assoc]
    change _ = _ ≫ _ ≫ (sheafifyMap (ProEt.topology Z)
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.lan.map φ.hom)).app (op V)
    rw [← h₁, ← Category.assoc, h₂, Category.assoc, ← reassoc_of% h₃, Category.assoc]

/-- **Sections of the pullback over affine objects with split affine covers.** If every affine
object of `Z_proét` with split affine covers has a hull, then for such an object `V` with hull
`W₀` the sections of `g^* F` over `V` are those of `F` over `W₀`, naturally in `F`. -/
theorem isIso_hullSectionsNatTrans (hψ : ProEt.IsHull (V.hom ≫ g) W₀ ψ) [IsAffine V.left]
    (hV : V.left.AffineCoversSplit)
    (hhull : ∀ V' : Z.ProEt, IsAffine V'.left → V'.left.AffineCoversSplit →
      ∃ W ψ', ProEt.IsHull (V'.hom ≫ g) W ψ') :
    IsIso (hullSectionsNatTrans (R := R) g hψ) := by
  have (F : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R)) :
      IsIso ((hullSectionsNatTrans (R := R) g hψ).app F) := by
    have : IsIso (hullLanMap g hψ F.obj) := isIso_hullLanMap g hψ F.obj
    have : IsIso ((toSheafify (ProEt.topology Z)
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.lan.obj F.obj)).app (op V)) :=
      (ConcreteCategory.isIso_iff_bijective _).2 (bijective_toSheafify_lan_app g hψ hV hhull F)
    exact inferInstanceAs (IsIso (hullLanMap g hψ F.obj ≫ _))
  exact NatIso.isIso_of_isIso_app _

end AlgebraicGeometry.ProEtale
