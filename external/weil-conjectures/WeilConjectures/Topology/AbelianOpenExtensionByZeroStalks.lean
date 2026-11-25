/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.AbelianOpenExtensionByZero
import WeilConjectures.Topology.AbelianOpenExtensionPresheafStalk
import Mathlib.Geometry.RingedSpace.Stalks
import Mathlib.Algebra.Category.Grp.Zero

/-! # Stalks of extension by zero of an abelian sheaf

Source: Stacks Project, Sheaves, Lemma 00A5, parts (2), (3), (5), and Modules,
Lemma 02UT (blueprint: lem-sc-topological-extension-by-zero-stalks).
-/

@[expose] public section

universe w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace TopCat.Sheaf

private theorem stalk_ext_preimage {X : TopCat.{w}} (U : Opens X)
    (G : TopCat.Presheaf AddCommGrpCat.{w} ((Opens.toTopCat X).obj U))
    (x : U) {A : AddCommGrpCat.{w}} {f g : G.stalk x ⟶ A}
    (h : ∀ (V : Opens X) (_hV : V ≤ U) (hx : x.val ∈ V),
      G.germ ((Opens.map U.inclusion').obj V) x hx ≫ f =
        G.germ ((Opens.map U.inclusion').obj V) x hx ≫ g) : f = g := by
  apply G.stalk_hom_ext
  intro W hxW
  let V := U.isOpenEmbedding.functor.obj W
  have hV : V ≤ U := by
    rintro y ⟨z, hz, rfl⟩
    exact z.property
  have hxV : x.val ∈ V := ⟨x, hxW, rfl⟩
  have hh := h V hV hxV
  have he : (Opens.map U.inclusion').obj V = W := Opens.map_functor_eq W
  erw [← G.germ_res (eqToHom he) x hxV, Category.assoc, Category.assoc, hh]

private theorem extensionSection_naturality {X : TopCat.{w}} (U : Opens X)
    (G H : TopCat.Sheaf AddCommGrpCat.{w} ((Opens.toTopCat X).obj U)) (α : G ⟶ H)
    (V : Opens X) (hV : V ≤ U) :
    α.hom.app (op ((Opens.map U.inclusion').obj V)) ≫
        abelianOpenExtensionSection U H V hV =
      abelianOpenExtensionSection U G V hV ≫
        ((abelianOpenExtensionByZero U).map α).hom.app (op V) := by
  classical
  unfold abelianOpenExtensionSection
  erw [Category.assoc]
  have hn := congr_app (toSheafify_naturality (Opens.grothendieckTopology X)
    ((abelianOpenExtensionPresheaf U).map α)) (op V)
  change _ ≫ _ = _ ≫ _ at hn
  change _ = _ ≫ _ ≫ (sheafifyMap (Opens.grothendieckTopology X)
    ((abelianOpenExtensionPresheaf U).map α)).app (op V)
  erw [← hn, ← Category.assoc]
  rw [← Category.assoc]
  apply congrArg (fun f ↦ f ≫
    (toSheafify (Opens.grothendieckTopology X)
      ((abelianOpenExtensionPresheaf U).obj H)).app (op V))
  ext s
  dsimp [abelianOpenExtensionPresheaf, siteExtensionByZeroPresheaf,
    siteExtensionByZeroHom, siteExtensionByZeroHomApp, openSlicePresheaf]
  let : DecidableEq (V ⟶ U) := fun a b ↦ Classical.propDecidable (a = b)
  erw [DirectSum.toAddMonoid_of]
  rfl

private theorem extensionSection_counit {X : TopCat.{w}} (U : Opens X)
    (F : TopCat.Sheaf AddCommGrpCat.{w} X) (V : Opens X) (hV : V ≤ U) :
    abelianOpenExtensionSection U (abelianOpenRestriction U F) V hV ≫
        (abelianOpenCounit U F).hom.app (op V) =
      eqToHom (congrArg (fun W : Opens X ↦ F.obj.obj (op W))
        (openImage_preimage_eq U V hV)) := by
  classical
  unfold abelianOpenExtensionSection abelianOpenCounit
  erw [Category.assoc]
  have hc := congr_app (toSheafify_sheafifyLift (Opens.grothendieckTopology X)
    (abelianOpenPresheafCounit U F) F.property) (op V)
  change _ ≫ _ = _ at hc
  dsimp only [ObjectProperty.homMk_hom]
  erw [hc]
  ext s
  dsimp [abelianOpenPresheafCounit, abelianOpenCounitApp,
    openSlicePresheaf, abelianOpenRestriction, abelianOpenRestrictionPresheaf]
  let : DecidableEq (V ⟶ U) := fun a b ↦ Classical.propDecidable (a = b)
  exact DirectSum.toAddMonoid_of _ _ _

private theorem extension_stalk_outside {X : TopCat.{w}} (U : Opens X)
    (G : TopCat.Sheaf AddCommGrpCat.{w} ((Opens.toTopCat X).obj U))
    (x : X) (hx : x ∉ U) :
    IsZero (TopCat.Presheaf.stalk (((abelianOpenExtensionByZero U).obj G).obj) x) := by
  let P := (abelianOpenExtensionPresheaf U).obj G
  have hp : IsZero (P.stalk x) := by
    apply AddCommGrpCat.isZero_iff_subsingleton.mpr
    suffices hh : ∀ t : P.stalk x, t = 0 from
      ⟨fun a b ↦ (hh a).trans (hh b).symm⟩
    intro t
    obtain ⟨V, hxV, s, rfl⟩ := P.exists_germ_eq t
    have : IsEmpty (V ⟶ U) := ⟨fun f ↦ hx (f.le hxV)⟩
    change DirectSum (V ⟶ U)
      (fun φ ↦ (openSlicePresheaf U G.obj).obj (op (Over.mk φ))) at s
    have hs : s = 0 := Subsingleton.elim _ _
    erw [hs]
    exact map_zero _
  have := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
    x AddCommGrpCat.{w} P
  exact hp.of_iso (asIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{w} x).map
    (toSheafify (Opens.grothendieckTopology X) P))).symm

/-- The stalk is the original stalk on U and zero outside U, naturally in the sheaf.
The isomorphisms are specified by their values on germs of sections on opens contained
in U, so they are the canonical maps, rather than arbitrary abstract isomorphisms.
Under the canonical restriction-stalk identification, the counit induces the identity.
Source: Stacks, Sheaves, Lemma 00A5 and Modules, Lemma 02UT
(blueprint: lem-sc-topological-extension-by-zero-stalks).

Proof: (1) Apply `stalkFunctor_map_unit_toSheafify_isIso`, the recorded
`lem-weil-pbc-stalk-sheafification-space`, to the extension presheaf. This preserves germs.
(2) Outside U, every neighborhood has no inclusion into U, so its section group is the
empty direct sum, zero. Its filtered colimit and therefore its sheafified stalk are zero.
(3) Inside U, neighborhoods contained in U are cofinal. Each has precisely one summand,
with the original restriction maps. The colimit comparison followed by (1) is the
canonical stalk isomorphism, with the displayed germ equation.
(4) All comparisons commute with sheaf morphisms because restrictions, direct-sum
injections and the sheafification unit do. The presheaf counit is identity on each sole
summand and zero on an empty sum. Thus its stalk map, after the two canonical germ
identifications, is identity on F_x. This gives the final compatibility equation. -/
theorem abelianOpenExtensionByZero_stalks (X : TopCat.{w}) (U : Opens X) :
    ∃ e : ∀ (x : U)
        (G : TopCat.Sheaf AddCommGrpCat.{w} ((Opens.toTopCat X).obj U)),
        TopCat.Presheaf.stalk (G.obj) x ≅
          TopCat.Presheaf.stalk (((abelianOpenExtensionByZero U).obj G).obj) x.val,
      (∀ (x : U) (G : TopCat.Sheaf AddCommGrpCat.{w} ((Opens.toTopCat X).obj U))
        (V : Opens X) (hV : V ≤ U) (hx : x.val ∈ V),
        TopCat.Presheaf.germ (G.obj) ((Opens.map U.inclusion').obj V) x hx ≫ (e x G).hom =
          abelianOpenExtensionSection U G V hV ≫
            TopCat.Presheaf.germ (((abelianOpenExtensionByZero U).obj G).obj) V x.val hx) ∧
      (∀ (x : U)
        (G H : TopCat.Sheaf AddCommGrpCat.{w} ((Opens.toTopCat X).obj U)) (α : G ⟶ H),
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{w} x).map α.hom ≫ (e x H).hom =
          (e x G).hom ≫ (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{w} x.val).map
            ((abelianOpenExtensionByZero U).map α).hom) ∧
      (∀ (G : TopCat.Sheaf AddCommGrpCat.{w} ((Opens.toTopCat X).obj U))
        (x : X), x ∉ U →
          IsZero (TopCat.Presheaf.stalk (((abelianOpenExtensionByZero U).obj G).obj) x)) ∧
      (∀ (F : TopCat.Sheaf AddCommGrpCat.{w} X) (x : U),
        ∃ r : TopCat.Presheaf.stalk ((abelianOpenRestriction U F).obj) x ≅
            TopCat.Presheaf.stalk (F.obj) x.val,
          (∀ (V : Opens X) (hV : V ≤ U) (hx : x.val ∈ V),
            TopCat.Presheaf.germ ((abelianOpenRestriction U F).obj)
                ((Opens.map U.inclusion').obj V) x hx ≫ r.hom =
              eqToHom (congrArg (fun W : Opens X ↦ F.obj.obj (op W))
                (openImage_preimage_eq U V hV)) ≫ TopCat.Presheaf.germ (F.obj) V x.val hx) ∧
          (e x (abelianOpenRestriction U F)).hom ≫
              (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{w} x.val).map
                (abelianOpenCounit U F).hom = r.hom) := by
  classical
  choose a ha using fun (x : U) G ↦ abelianOpenExtensionPresheaf_stalk X U x G
  let e := fun (x : U) G ↦ (a x G).trans
    (by
      let P := (abelianOpenExtensionPresheaf U).obj G
      have := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
        x.val AddCommGrpCat.{w} P
      exact asIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{w} x.val).map
        (toSheafify (Opens.grothendieckTopology X) P)))
  have he (x : U) (G : TopCat.Sheaf AddCommGrpCat.{w} ((Opens.toTopCat X).obj U))
      (V : Opens X) (hV : V ≤ U) (hx : x.val ∈ V) :
      TopCat.Presheaf.germ G.obj ((Opens.map U.inclusion').obj V) x hx ≫ (e x G).hom =
        abelianOpenExtensionSection U G V hV ≫
          TopCat.Presheaf.germ (((abelianOpenExtensionByZero U).obj G).obj) V x.val hx := by
    dsimp [e]
    erw [← Category.assoc, ha x G V hV hx, Category.assoc,
      TopCat.Presheaf.stalkFunctor_map_germ]
    simp only [abelianOpenExtensionSection, Category.assoc]
    rfl
  refine ⟨e, he, ?_, extension_stalk_outside U, ?_⟩
  · intro x G H α
    apply stalk_ext_preimage U G.obj x
    intro V hV hx
    calc
      _ = α.hom.app (op ((Opens.map U.inclusion').obj V)) ≫
          (TopCat.Presheaf.germ H.obj ((Opens.map U.inclusion').obj V) x hx ≫
            (e x H).hom) := by
        simp only [TopCat.Presheaf.stalkFunctor_map_germ_assoc]
      _ = α.hom.app (op ((Opens.map U.inclusion').obj V)) ≫
          (abelianOpenExtensionSection U H V hV ≫
            TopCat.Presheaf.germ (((abelianOpenExtensionByZero U).obj H).obj) V x.val hx) :=
        congrArg (fun f ↦ α.hom.app (op ((Opens.map U.inclusion').obj V)) ≫ f)
          (he x H V hV hx)
      _ = abelianOpenExtensionSection U G V hV ≫
          (((abelianOpenExtensionByZero U).map α).hom.app (op V) ≫
            TopCat.Presheaf.germ (((abelianOpenExtensionByZero U).obj H).obj) V x.val hx) :=
        by rw [← Category.assoc, extensionSection_naturality, Category.assoc]
      _ = (abelianOpenExtensionSection U G V hV ≫
          TopCat.Presheaf.germ (((abelianOpenExtensionByZero U).obj G).obj) V x.val hx) ≫
            (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{w} x.val).map
              ((abelianOpenExtensionByZero U).map α).hom := by
        rw [Category.assoc, TopCat.Presheaf.stalkFunctor_map_germ]
      _ = _ := by rw [← he x G V hV hx, Category.assoc]
  · intro F x
    let S : AlgebraicGeometry.PresheafedSpace AddCommGrpCat.{w} := ⟨X, F.obj⟩
    let r := S.restrictStalkIso U.isOpenEmbedding x
    have hr (V : Opens X) (hV : V ≤ U) (hx : x.val ∈ V) :
        TopCat.Presheaf.germ ((abelianOpenRestriction U F).obj)
            ((Opens.map U.inclusion').obj V) x hx ≫
            r.hom =
          eqToHom (congrArg (fun W : Opens X ↦ F.obj.obj (op W))
            (openImage_preimage_eq U V hV)) ≫ TopCat.Presheaf.germ F.obj V x.val hx := by
      have hh := S.restrictStalkIso_hom_eq_germ U.isOpenEmbedding
        ((Opens.map U.inclusion').obj V) x hx
      change _ ≫ r.hom = _ at hh
      erw [hh]
      have hg (A B : Opens X) (h : A = B) (ha : x.val ∈ A) (hb : x.val ∈ B) :
          TopCat.Presheaf.germ F.obj A x.val ha =
            eqToHom (congrArg (fun W : Opens X ↦ F.obj.obj (op W)) h) ≫
              TopCat.Presheaf.germ F.obj B x.val hb := by
        subst B
        simp
      exact hg _ _ (openImage_preimage_eq U V hV) _ hx
    refine ⟨r, hr, ?_⟩
    apply stalk_ext_preimage U (abelianOpenRestriction U F).obj x
    intro V hV hx
    erw [← Category.assoc, he x (abelianOpenRestriction U F) V hV hx, Category.assoc,
      TopCat.Presheaf.stalkFunctor_map_germ, ← Category.assoc,
      extensionSection_counit U F V hV, hr V hV hx]

end TopCat.Sheaf
