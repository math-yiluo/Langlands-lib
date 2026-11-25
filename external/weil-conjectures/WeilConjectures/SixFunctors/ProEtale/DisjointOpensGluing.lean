/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.DisjointGluing
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation

/-!
# Gluing pro-étale sheaves over a decomposition into disjoint opens

Let `Y` be a scheme covered by pairwise disjoint opens `O j` (e.g. the decomposition of a
w-contractible affine given by
`AlgebraicGeometry.ProEtale.exists_disjoint_opens_isConstant_comparisonUpperStar`).

- `Scheme.ProEt.isDisjointFamily_opensHom`, `Scheme.ProEt.ofArrows_opensHom_mem`: the `O j`
  form a disjoint covering family of the terminal object of `Y_proét`;
- `ProEtale.overIsoOfLocalizationRestrictionIso`: an isomorphism of restrictions to `V_proét`
  for `V : Y_proét` gives one on the localized site `J.over V`;
- `ProEtale.nonempty_iso_of_disjoint_opens`: sheaves `F`, `G` on `Y_proét` with
  `(O j)^* F ≅ (O j)^* G` for all `j` are isomorphic (no compatibility needed);
- `ProEtale.nonempty_iso_constantSheaf_of_disjoint_opens`: in particular a sheaf which is
  constant with the same value `M` on every piece is constant with value `M`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

section Opens

variable {Y : Scheme.{u}} {κ : Type*} (O : κ → Y.Opens)

/-- The inclusion of an open subscheme `O j`, as a morphism to the terminal object of
`Y_proét`. -/
noncomputable def Scheme.ProEt.opensHom (j : κ) : ProEt.mk (O j).ι ⟶ ProEt.mk (𝟙 Y) :=
  MorphismProperty.Over.homMk (O j).ι

/-- Pairwise disjoint opens form a disjoint family in the pro-étale site. -/
lemma Scheme.ProEt.isDisjointFamily_opensHom (hO : ∀ i j, i ≠ j → Disjoint (O i) (O j)) :
    Presieve.IsDisjointFamily (ProEt.opensHom O) (ProEt.topology Y) where
  mono j := ⟨fun {Z} a b h ↦ MorphismProperty.Over.Hom.ext <| (cancel_mono (O j).ι).1 <| by
    have := congrArg (fun m ↦ m.left) h
    exact this⟩
  bot_mem i j hij Z a b h := by
    have : IsEmpty Z.left := ⟨fun z ↦ by
      have hz := congrArg (fun m ↦ m.left.base z) h
      change (a.left ≫ (O i).ι) z = (b.left ≫ (O j).ι) z at hz
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hz
      have hz' : (a.left z).val = (b.left z).val := hz
      have h₂ : (a.left z).val ∈ O j := hz' ▸ (b.left z).2
      exact (hO i j hij).le_bot ⟨(a.left z).2, h₂⟩⟩
    exact ProEt.bot_mem_topology Z

/-- An open cover is a covering family of the terminal object of `Y_proét`. -/
lemma Scheme.ProEt.ofArrows_opensHom_mem (hcov : ∀ x, ∃ i, x ∈ O i) :
    Sieve.ofArrows _ (ProEt.opensHom O) ∈ ProEt.topology Y (ProEt.mk (𝟙 Y)) := by
  rw [ProEt.mem_topology_iff]
  refine ⟨Presieve.ofArrows _ (ProEt.opensHom O), ?_, Sieve.le_generate _⟩
  rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
  exact Scheme.zariskiPrecoverage_le_proetalePrecoverage _
    ((Scheme.ofArrows_mem_precoverage_iff _).mpr
      ⟨fun x ↦ by obtain ⟨i, hi⟩ := hcov x; exact ⟨i, ⟨x, hi⟩, rfl⟩,
        fun i ↦ inferInstanceAs (IsOpenImmersion (O i).ι)⟩)

end Opens

section Bridge

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {Y : Scheme.{u}} (V : Y.ProEt)

/-- The structure morphism of an object of the localized site at `V`. -/
lemma ProEtale.overLocalization_w (T : Over V) : T.hom.left ≫ V.hom = T.left.hom :=
  MorphismProperty.Over.w T.hom

/-- The functor `Over V ⥤ V_proét` from the localized site at `V : Y_proét` to the small
pro-étale site of the underlying scheme. -/
@[simps]
noncomputable def ProEtale.overLocalization : Over V ⥤ V.left.ProEt where
  obj T := MorphismProperty.Over.mk ⊤ T.hom.left
    (MorphismProperty.of_postcomp _ _ _ V.prop (by
      rw [ProEtale.overLocalization_w]; exact T.left.prop))
  map g := MorphismProperty.Over.homMk g.left.left
    (congrArg (fun f ↦ f.left) (Over.w g)) trivial

/-- Composing `ProEtale.overLocalization` with the localization functor is the forgetful
functor. -/
noncomputable def ProEtale.overLocalizationCompIso :
    ProEtale.overLocalization V ⋙ MorphismProperty.Over.map ⊤ V.prop ≅ Over.forget V :=
  NatIso.ofComponents (fun T ↦ MorphismProperty.Over.isoMk (Iso.refl _)
    (ProEtale.overLocalization_w V T).symm) (fun g ↦ by ext; simp)

/-- An isomorphism between the restrictions `j_V^* F ≅ j_V^* G` to `V_proét` along the
localization functor induces an isomorphism `F|_V ≅ G|_V` on the localized site at `V`. -/
noncomputable def ProEtale.overIsoOfLocalizationRestrictionIso
    {F G : Sheaf (ProEt.topology Y) A}
    (e : (ProEtale.localizationRestriction A V.hom V.prop).obj F ≅
      (ProEtale.localizationRestriction A V.hom V.prop).obj G) :
    F.over V ≅ G.over V :=
  (fullyFaithfulSheafToPresheaf _ A).preimageIso <|
    Functor.isoWhiskerRight (NatIso.op (ProEtale.overLocalizationCompIso V)) F.obj ≪≫
      Functor.isoWhiskerLeft (ProEtale.overLocalization V).op
        ((sheafToPresheaf _ A).mapIso e) ≪≫
      (Functor.isoWhiskerRight (NatIso.op (ProEtale.overLocalizationCompIso V)) G.obj).symm

end Bridge

section Gluing

open ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {Y : Scheme.{u}} {κ : Type*} (O : κ → Y.Opens)

/-- **Gluing isomorphisms of pro-étale sheaves over a decomposition into disjoint opens**: if
`Y` is covered by pairwise disjoint opens `O j` and the restrictions of `F` and `G` to each
`(O j)_proét` are isomorphic, then `F ≅ G`. No compatibility is needed, the pieces being
disjoint. -/
theorem ProEtale.nonempty_iso_of_disjoint_opens (hO : ∀ i j, i ≠ j → Disjoint (O i) (O j))
    (hcov : ∀ x, ∃ i, x ∈ O i) (F G : Sheaf (ProEt.topology Y) A)
    (e : ∀ j, ((O j).ι)^*[A].obj F ≅ ((O j).ι)^*[A].obj G) : Nonempty (F ≅ G) := by
  obtain ⟨e', -⟩ := (ProEt.isDisjointFamily_opensHom O hO).exists_iso_of_isTerminal
    (ProEt.isTerminalMkId Y) (ProEt.ofArrows_opensHom_mem O hcov) F G fun j ↦
      ProEtale.overIsoOfLocalizationRestrictionIso A (ProEt.mk (O j).ι)
        (((ProEtale.upperStarIsoLocalizationRestriction A (O j).ι inferInstance).app F).symm ≪≫
          e j ≪≫ (ProEtale.upperStarIsoLocalizationRestriction A (O j).ι inferInstance).app G)
  exact ⟨e'⟩

/-- **A pro-étale sheaf which is constant with value `M` on each piece of a decomposition into
disjoint opens is constant with value `M`.** -/
theorem ProEtale.nonempty_iso_constantSheaf_of_disjoint_opens
    (hO : ∀ i j, i ≠ j → Disjoint (O i) (O j)) (hcov : ∀ x, ∃ i, x ∈ O i)
    (F : Sheaf (ProEt.topology Y) A) (M : A)
    (e : ∀ j, ((O j).ι)^*[A].obj F ≅ (constantSheaf (ProEt.topology (O j)) A).obj M) :
    Nonempty (F ≅ (constantSheaf (ProEt.topology Y) A).obj M) :=
  ProEtale.nonempty_iso_of_disjoint_opens A O hO hcov _ _ fun j ↦
    e j ≪≫ ((ProEtale.constantSheafCompUpperStarIso A (O j).ι).app M).symm

end Gluing

end AlgebraicGeometry
