/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
public import WeilConjectures.SixFunctors.Etale.SupportCohomologyTriangle

/-!
# Functoriality of the pro-étale triangle of cohomology with support in the pair

This is the pro-étale counterpart of
`WeilConjectures.SixFunctors.Etale.SupportCohomologyTrianglePullback`. Let `e : X' ⟶ X` be a
morphism of schemes, `i : Z ⟶ X` and `i' : Z' ⟶ X'` closed immersions with open complements
`U` and `U'` such that `U' ⊆ e⁻¹(U)`. The pullback of sections along `e` on the small pro-étale
sites (`AlgebraicGeometry.ProEtale.sectionsPullback`) gives maps `Γ(X, F) ⟶ Γ(X', e^* F)`,
`F(U) ⟶ (e^* F)(U')` and `Γ_Z(X, F) ⟶ Γ_{Z'}(X', e^* F)`, and the pullback maps of the right
derived functors form a morphism of triangles

`RΓ_Z(X, K) ⟶ RΓ(X, K) ⟶ RΓ(U, K) ⟶ RΓ_Z(X, K)[1]`
`RΓ_Z'(X', e^*K) ⟶ RΓ(X', e^*K) ⟶ RΓ(U', e^*K) ⟶ RΓ_Z'(X', e^*K)[1]`

natural in the bounded below complex `K` of pro-étale sheaves
(`AlgebraicGeometry.ProEtale.sectionsWithSupportTrianglePullback`), so that the long exact
sequence of cohomology with support on the pro-étale site of blueprint
`thm-pur-with-support-exactness` is functorial in the pair
(`AlgebraicGeometry.ProEtale.homology_sectionsWithSupportTrianglePullback_comm`), compatibly with
composition (`AlgebraicGeometry.ProEtale.sectionsWithSupportTrianglePullback_comp`).
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite Pretriangulated DerivedCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section HomToPullback

variable {R T : Scheme.{u}} (t : T ⟶ R)

@[reassoc]
lemma proEt_comp_left {X : Scheme.{u}} {V₁ V₂ V₃ : X.ProEt} (a : V₁ ⟶ V₂) (b : V₂ ⟶ V₃) :
    (a ≫ b).left = a.left ≫ b.left :=
  rfl

@[simp]
lemma overPullback_obj_left (U : R.ProEt) :
    ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ t).obj U).left = pullback U.hom t :=
  rfl

@[simp]
lemma overPullback_obj_hom (U : R.ProEt) :
    ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ t).obj U).hom = pullback.snd U.hom t :=
  rfl

lemma overPullback_map_left {U U' : R.ProEt} (b : U' ⟶ U) :
    ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ t).map b).left =
      pullback.lift (pullback.fst U'.hom t ≫ b.left) (pullback.snd U'.hom t)
        (by rw [Category.assoc, MorphismProperty.Over.w b, pullback.condition]) :=
  rfl

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
lemma lowerStar_obj_val_map (G : Sheaf (Scheme.ProEt.topology T) A) {b b' : R.ProEt}
    (φ : b ⟶ b') :
    ((t)_*[A].obj G).obj.map φ.op =
      G.obj.map ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ t).map φ).op :=
  rfl

/-- The morphism `V ⟶ U ×_R T` of weakly étale `T`-schemes induced by a morphism `φ : V ⟶ U`
over `R`. -/
noncomputable def homToPullback {V : T.ProEt} {U : R.ProEt} (φ : V.left ⟶ U.left)
    (hφ : φ ≫ U.hom = V.hom ≫ t) :
    V ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ t).obj U :=
  MorphismProperty.Over.homMk (pullback.lift φ V.hom hφ) (pullback.lift_snd _ _ _)

@[reassoc (attr := simp)]
lemma homToPullback_left_fst {V : T.ProEt} {U : R.ProEt} (φ : V.left ⟶ U.left)
    (hφ : φ ≫ U.hom = V.hom ≫ t) :
    (homToPullback t φ hφ).left ≫ pullback.fst U.hom t = φ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma homToPullback_left_snd {V : T.ProEt} {U : R.ProEt} (φ : V.left ⟶ U.left)
    (hφ : φ ≫ U.hom = V.hom ≫ t) :
    (homToPullback t φ hφ).left ≫ pullback.snd U.hom t = V.hom :=
  pullback.lift_snd _ _ _

end HomToPullback

section Sections

variable {X X' : Scheme.{u}} (e : X' ⟶ X)

/-- The pullback of sections `F(V) ⟶ (e^* F)(W)` along a morphism `φ : W ⟶ V` over
`e : X' ⟶ X` from an pro-étale `X'`-scheme `W` to an pro-étale `X`-scheme `V`, natural in `F`. -/
noncomputable def sectionsPullback {V : X.ProEt} {W : X'.ProEt} (φ : W.left ⟶ V.left)
    (hφ : φ ≫ V.hom = W.hom ≫ e) :
    (sheafSections (Scheme.ProEt.topology X) A).obj (op V) ⟶
      (e)^*[A] ⋙ (sheafSections (Scheme.ProEt.topology X') A).obj (op W) where
  app F := ((upperStarLowerStarAdjunction A e).unit.app F).hom.app (op V) ≫
    ((e)^*[A].obj F).obj.map (homToPullback e φ hφ).op
  naturality F G f := by
    have h₁ := congr_arg (fun k ↦ k.hom.app (op V))
      ((upperStarLowerStarAdjunction A e).unit.naturality f)
    dsimp at h₁ ⊢
    rw [reassoc_of% h₁, assoc]
    congr 1
    exact (((e)^*[A].map f).hom.naturality (homToPullback e φ hφ).op).symm

lemma sectionsPullback_app {V : X.ProEt} {W : X'.ProEt} (φ : W.left ⟶ V.left)
    (hφ : φ ≫ V.hom = W.hom ≫ e) (F : Sheaf (Scheme.ProEt.topology X) A) :
    (sectionsPullback A e φ hφ).app F =
      ((upperStarLowerStarAdjunction A e).unit.app F).hom.app (op V) ≫
        ((e)^*[A].obj F).obj.map (homToPullback e φ hφ).op :=
  rfl

/-- The pullback of sections is compatible with the restrictions. -/
@[reassoc]
lemma sectionsPullback_app_comp_map {V V₁ : X.ProEt} {W W₁ : X'.ProEt} (φ : W.left ⟶ V.left)
    (hφ : φ ≫ V.hom = W.hom ≫ e) (φ₁ : W₁.left ⟶ V₁.left) (hφ₁ : φ₁ ≫ V₁.hom = W₁.hom ≫ e)
    (b : V₁ ⟶ V) (c : W₁ ⟶ W) (hbc : c.left ≫ φ = φ₁ ≫ b.left)
    (F : Sheaf (Scheme.ProEt.topology X) A) :
    (sectionsPullback A e φ hφ).app F ≫ ((e)^*[A].obj F).obj.map c.op =
      F.obj.map b.op ≫ (sectionsPullback A e φ₁ hφ₁).app F := by
  have h₁ := ((upperStarLowerStarAdjunction A e).unit.app F).hom.naturality b.op
  dsimp at h₁
  rw [sectionsPullback_app, sectionsPullback_app, reassoc_of% h₁, assoc, lowerStar_obj_val_map]
  congr 1
  simp only [← Functor.map_comp, ← op_comp]
  congr 2
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · rw [show (homToPullback e φ₁ hφ₁ ≫
        (MorphismProperty.Over.pullback @WeaklyEtale ⊤ e).map b).left =
      (homToPullback e φ₁ hφ₁).left ≫
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ e).map b).left from rfl]
    simp only [proEt_comp_left, assoc, homToPullback_left_fst, overPullback_map_left,
      pullback.lift_fst, homToPullback_left_fst_assoc, hbc]
  · rw [show (homToPullback e φ₁ hφ₁ ≫
        (MorphismProperty.Over.pullback @WeaklyEtale ⊤ e).map b).left =
      (homToPullback e φ₁ hφ₁).left ≫
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ e).map b).left from rfl]
    simp only [proEt_comp_left, assoc, homToPullback_left_snd, overPullback_map_left,
      pullback.lift_snd]
    exact MorphismProperty.Over.w c

instance isIso_natTransΓRes_mkId (X : Scheme.{u}) :
    IsIso (Sheaf.natTransΓRes (Scheme.ProEt.topology X) A (op (Scheme.ProEt.mk (𝟙 X)))) := by
  have (M : Sheaf (Scheme.ProEt.topology X) A) :
      IsIso ((Sheaf.natTransΓRes (Scheme.ProEt.topology X) A (op (Scheme.ProEt.mk (𝟙 X)))).app M) :=
    M.isLimitConeΓ.isIso_π_app_of_isInitial _ (Scheme.ProEt.isTerminalMkId X).op
  exact NatIso.isIso_of_isIso_app _

lemma etaleMkId_hom_comp : e ≫ (Scheme.ProEt.mk (𝟙 X)).hom = (Scheme.ProEt.mk (𝟙 X')).hom ≫ e :=
  (comp_id e).trans (id_comp e).symm

/-- The pullback of global sections `Γ(X, F) ⟶ Γ(X', e^* F)`, natural in `F`. -/
noncomputable def ΓPullback :
    Sheaf.Γ (Scheme.ProEt.topology X) A ⟶ (e)^*[A] ⋙ Sheaf.Γ (Scheme.ProEt.topology X') A :=
  Sheaf.natTransΓRes _ A (op (Scheme.ProEt.mk (𝟙 X))) ≫
    sectionsPullback A e (V := Scheme.ProEt.mk (𝟙 X)) (W := Scheme.ProEt.mk (𝟙 X')) e
      (etaleMkId_hom_comp e) ≫
    Functor.whiskerLeft _ (inv (Sheaf.natTransΓRes _ A (op (Scheme.ProEt.mk (𝟙 X')))))

/-- The pullback of global sections is compatible with the restrictions to `V` and `W`. -/
@[reassoc]
lemma ΓPullback_app_comp_ΓRes {V : X.ProEt} {W : X'.ProEt} (φ : W.left ⟶ V.left)
    (hφ : φ ≫ V.hom = W.hom ≫ e) (F : Sheaf (Scheme.ProEt.topology X) A) :
    (ΓPullback A e).app F ≫ ((e)^*[A].obj F).ΓRes (op W) =
      F.ΓRes (op V) ≫ (sectionsPullback A e φ hφ).app F := by
  have h₁ : inv ((Sheaf.natTransΓRes _ A (op (Scheme.ProEt.mk (𝟙 X')))).app ((e)^*[A].obj F)) ≫
      ((e)^*[A].obj F).ΓRes (op W) = ((e)^*[A].obj F).obj.map
        ((Scheme.ProEt.isTerminalMkId X').from W).op := by
    rw [IsIso.inv_comp_eq]
    exact (Sheaf.ΓRes_map _ _).symm
  have hc : ((Scheme.ProEt.isTerminalMkId X').from W).left = W.hom := by
    have := MorphismProperty.Over.w ((Scheme.ProEt.isTerminalMkId X').from W)
    erw [comp_id] at this
    exact this
  have hb : ((Scheme.ProEt.isTerminalMkId X).from V).left = V.hom := by
    have := MorphismProperty.Over.w ((Scheme.ProEt.isTerminalMkId X).from V)
    erw [comp_id] at this
    exact this
  have h₂ := sectionsPullback_app_comp_map A e (V := Scheme.ProEt.mk (𝟙 X))
    (W := Scheme.ProEt.mk (𝟙 X')) e (etaleMkId_hom_comp e) φ hφ
    ((Scheme.ProEt.isTerminalMkId X).from V) ((Scheme.ProEt.isTerminalMkId X').from W)
    (by rw [hc, hb, hφ]) F
  have h₃ : (ΓPullback A e).app F = F.ΓRes (op (Scheme.ProEt.mk (𝟙 X))) ≫
      (sectionsPullback A e (V := Scheme.ProEt.mk (𝟙 X)) (W := Scheme.ProEt.mk (𝟙 X')) e
        (etaleMkId_hom_comp e)).app F ≫
      inv ((Sheaf.natTransΓRes _ A (op (Scheme.ProEt.mk (𝟙 X')))).app ((e)^*[A].obj F)) := by
    simp [ΓPullback]
  rw [h₃, assoc, assoc, h₁, h₂, ← assoc]
  congr 1
  exact Sheaf.ΓRes_map _ _

section CompAux

variable {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)

/-- The unit form of the definition of `AlgebraicGeometry.ProEtale.upperStarComp`:
transposing the composition isomorphism of the pullbacks along the adjunctions `h^* ⊣ h_*`
gives the composition isomorphism of the pushforwards. -/
lemma upperStarComp_hom_app_unit_app (F : Sheaf (Scheme.ProEt.topology R) A) :
    (upperStarLowerStarAdjunction A (h₁ ≫ h₂)).unit.app F ≫
        ((h₁ ≫ h₂)_*[A]).map ((upperStarComp A h₁ h₂).hom.app F) =
      ((upperStarLowerStarAdjunction A h₂).comp
          (upperStarLowerStarAdjunction A h₁)).unit.app F ≫
        (lowerStarComp A h₁ h₂).hom.app (((h₁)^*[A]).obj (((h₂)^*[A]).obj F)) := by
  have hconj : conjugateEquiv ((upperStarLowerStarAdjunction A h₂).comp
        (upperStarLowerStarAdjunction A h₁))
      (upperStarLowerStarAdjunction A (h₁ ≫ h₂)) (upperStarComp A h₁ h₂).hom =
      (lowerStarComp A h₁ h₂).hom :=
    congrArg Iso.inv ((conjugateIsoEquiv (upperStarLowerStarAdjunction A (h₁ ≫ h₂))
      ((upperStarLowerStarAdjunction A h₂).comp
        (upperStarLowerStarAdjunction A h₁))).apply_symm_apply (lowerStarComp A h₁ h₂).symm)
  have hh := unit_conjugateEquiv ((upperStarLowerStarAdjunction A h₂).comp
      (upperStarLowerStarAdjunction A h₁))
    (upperStarLowerStarAdjunction A (h₁ ≫ h₂)) (upperStarComp A h₁ h₂).hom F
  rw [hconj] at hh
  exact hh.symm

end CompAux

section Comp

variable {X'' : Scheme.{u}} (e' : X'' ⟶ X')

/-- Base change of a morphism over `e ≫ e'` through the pasting isomorphism of pullbacks. -/
lemma homToPullback_comp_pullbackComp {V : X.ProEt} {W : X'.ProEt} {W'' : X''.ProEt}
    (φ : W.left ⟶ V.left) (hφ : φ ≫ V.hom = W.hom ≫ e) (φ' : W''.left ⟶ W.left)
    (hφ' : φ' ≫ W.hom = W''.hom ≫ e') :
    homToPullback (e' ≫ e) (φ' ≫ φ) (by rw [assoc, hφ, ← assoc, hφ', assoc]) ≫
        (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) e' e).hom.app V =
      homToPullback e' φ' hφ' ≫ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ e').map
        (homToPullback e φ hφ) := by
  apply MorphismProperty.Over.Hom.ext
  rw [show (homToPullback (e' ≫ e) (φ' ≫ φ) (by rw [assoc, hφ, ← assoc, hφ', assoc]) ≫
      (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) e' e).hom.app V).left =
      (homToPullback (e' ≫ e) (φ' ≫ φ) (by rw [assoc, hφ, ← assoc, hφ', assoc])).left ≫
        ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) e' e).hom.app V).left
      from rfl,
    show (homToPullback e' φ' hφ' ≫ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ e').map
      (homToPullback e φ hφ)).left = (homToPullback e' φ' hφ').left ≫
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ e').map (homToPullback e φ hφ)).left
      from rfl]
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp [MorphismProperty.Over.pullbackComp_hom_app_left, homToPullback]
    · simp only [MorphismProperty.Over.pullbackComp_hom_app_left, assoc,
        overPullback_obj_left, overPullback_map_left, pullback.lift_fst_assoc,
        homToPullback_left_fst_assoc, homToPullback_left_snd]
      simp [homToPullback, hφ', pullback.condition]
  · simp [MorphismProperty.Over.pullbackComp_hom_app_left, homToPullback]

/-- The pullback of sections is compatible with the composition of morphisms of schemes. -/
lemma sectionsPullback_comp {V : X.ProEt} {W : X'.ProEt} {W'' : X''.ProEt}
    (φ : W.left ⟶ V.left) (hφ : φ ≫ V.hom = W.hom ≫ e) (φ' : W''.left ⟶ W.left)
    (hφ' : φ' ≫ W.hom = W''.hom ≫ e') (F : Sheaf (Scheme.ProEt.topology X) A) :
    (sectionsPullback A (e' ≫ e) (φ' ≫ φ) (by rw [assoc, hφ, ← assoc, hφ', assoc])).app F ≫
        ((upperStarComp A e' e).hom.app F).hom.app (op W'') =
      (sectionsPullback A e φ hφ).app F ≫ (sectionsPullback A e' φ' hφ').app ((e)^*[A].obj F) := by
  have hu := congr_arg (fun k ↦ k.hom.app (op V)) (upperStarComp_hom_app_unit_app A e' e F)
  have n₁ := ((upperStarComp A e' e).hom.app F).hom.naturality
    (homToPullback (e' ≫ e) (φ' ≫ φ) (by rw [assoc, hφ, ← assoc, hφ', assoc])).op
  have n₂ := ((upperStarLowerStarAdjunction A e').unit.app ((e)^*[A].obj F)).hom.naturality
    (homToPullback e φ hφ).op
  dsimp at hu n₁ n₂
  rw [Adjunction.comp_unit_app] at hu
  dsimp at hu
  rw [lowerStarComp_hom_app_hom_app] at hu
  simp only [sectionsPullback_app, assoc]
  rw [n₁]
  erw [reassoc_of% hu, reassoc_of% n₂]
  simp only [lowerStar_obj_val_map]
  congr 2
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp,
    homToPullback_comp_pullbackComp]

/-- The pullback of global sections is compatible with the composition of morphisms of
schemes. -/
lemma ΓPullback_comp :
    ΓPullback A (e' ≫ e) ≫ Functor.whiskerRight (upperStarComp A e' e).hom _ =
      ΓPullback A e ≫ Functor.whiskerLeft _ (ΓPullback A e') := by
  ext F
  have : IsIso ((((e')^*[A]).obj ((e)^*[A].obj F)).ΓRes (op (Scheme.ProEt.mk (𝟙 X'')))) :=
    (((e')^*[A]).obj ((e)^*[A].obj F)).isLimitConeΓ.isIso_π_app_of_isInitial _
      (Scheme.ProEt.isTerminalMkId X'').op
  rw [← cancel_mono ((((e')^*[A]).obj ((e)^*[A].obj F)).ΓRes
    (op (Scheme.ProEt.mk (𝟙 X''))))]
  have h := ΓPullback_app_comp_ΓRes A e' (V := Scheme.ProEt.mk (𝟙 X'))
    (W := Scheme.ProEt.mk (𝟙 X'')) e' (etaleMkId_hom_comp e') ((e)^*[A].obj F)
  have h' := ΓPullback_app_comp_ΓRes A (e' ≫ e) (V := Scheme.ProEt.mk (𝟙 X))
    (W := Scheme.ProEt.mk (𝟙 X'')) (e' ≫ e) (etaleMkId_hom_comp _) F
  have h'' := ΓPullback_app_comp_ΓRes A e (V := Scheme.ProEt.mk (𝟙 X))
    (W := Scheme.ProEt.mk (𝟙 X')) e (etaleMkId_hom_comp e) F
  have hc := sectionsPullback_comp A e e' (V := Scheme.ProEt.mk (𝟙 X))
    (W := Scheme.ProEt.mk (𝟙 X')) (W'' := Scheme.ProEt.mk (𝟙 X'')) e (etaleMkId_hom_comp e) e'
    (etaleMkId_hom_comp e') F
  have hn := Sheaf.ΓRes_naturality ((upperStarComp A e' e).hom.app F)
    (op (Scheme.ProEt.mk (𝟙 X'')))
  dsimp at h h' h'' hc hn ⊢
  rw [assoc, hn, reassoc_of% h', hc, assoc, h, reassoc_of% h'']

end Comp

end Sections

section Pair

variable {X X' Z Z' : Scheme.{u}} (e : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
  (i' : Z' ⟶ X') [IsClosedImmersion i'] (h : i'.openComplement ≤ e ⁻¹ᵁ i.openComplement)

/-- The pullback `F(U) ⟶ (e^* F)(U')` of sections over the open complements. -/
noncomputable def openComplementSectionsPullback :
    (sheafSections (Scheme.ProEt.topology X) A).obj (op (Scheme.ProEt.mk i.openComplement.ι)) ⟶
      (e)^*[A] ⋙
        (sheafSections (Scheme.ProEt.topology X') A).obj
          (op (Scheme.ProEt.mk i'.openComplement.ι)) :=
  sectionsPullback A e (V := Scheme.ProEt.mk i.openComplement.ι)
    (W := Scheme.ProEt.mk i'.openComplement.ι) (e.resLE _ _ h) (Scheme.Hom.resLE_comp_ι _ _)

lemma ΓPullback_comp_natTransΓRes :
    ΓPullback A e ≫ Functor.whiskerLeft _
        (Sheaf.natTransΓRes _ A (op (Scheme.ProEt.mk i'.openComplement.ι))) =
      Sheaf.natTransΓRes _ A (op (Scheme.ProEt.mk i.openComplement.ι)) ≫
        openComplementSectionsPullback A e i i' h := by
  ext F
  exact ΓPullback_app_comp_ΓRes A e _ _ F

/-- The kernel fork of `Γ(X', e^* F) ⟶ (e^* F)(U')` given by the sections with support in `Z'`
is limiting. -/
noncomputable def isLimitΓSupportι (F : Sheaf (Scheme.ProEt.topology X') A) :=
  KernelFork.mapIsLimit _ (kernelIsKernel (Sheaf.natTransΓRes _ A
    (op (Scheme.ProEt.mk i'.openComplement.ι)))) ((evaluation _ A).obj F)

include h in
lemma ΓSupportι_app_comp_ΓPullback_app_comp_ΓRes (F : Sheaf (Scheme.ProEt.topology X) A) :
    ((Sheaf.ΓSupportι _ A (op (Scheme.ProEt.mk i.openComplement.ι))).app F ≫
        (ΓPullback A e).app F) ≫
      ((e)^*[A].obj F).ΓRes (op (Scheme.ProEt.mk i'.openComplement.ι)) = 0 := by
  have := congr_app (ΓPullback_comp_natTransΓRes A e i i' h) F
  dsimp at this
  rw [assoc]
  erw [this]
  erw [Sheaf.ΓSupportι_app_comp_ΓRes_assoc]
  rw [zero_comp]

include h in
/-- The pullback `Γ_Z(X, F) ⟶ Γ_{Z'}(X', e^* F)` of the sections with support, for one sheaf. -/
noncomputable def sectionsWithSupportPullbackApp (F : Sheaf (Scheme.ProEt.topology X) A) :
    (Sheaf.ΓSupport (Scheme.ProEt.topology X) A (op (Scheme.ProEt.mk i.openComplement.ι))).obj F ⟶
      (Sheaf.ΓSupport (Scheme.ProEt.topology X') A
        (op (Scheme.ProEt.mk i'.openComplement.ι))).obj ((e)^*[A].obj F) :=
  (isLimitΓSupportι A i' ((e)^*[A].obj F)).lift (KernelFork.ofι _
    (ΓSupportι_app_comp_ΓPullback_app_comp_ΓRes A e i i' h F))

@[reassoc]
lemma sectionsWithSupportPullbackApp_comp (F : Sheaf (Scheme.ProEt.topology X) A) :
    sectionsWithSupportPullbackApp A e i i' h F ≫
        (Sheaf.ΓSupportι _ A (op (Scheme.ProEt.mk i'.openComplement.ι))).app ((e)^*[A].obj F) =
      (Sheaf.ΓSupportι _ A (op (Scheme.ProEt.mk i.openComplement.ι))).app F ≫
        (ΓPullback A e).app F :=
  (isLimitΓSupportι A i' ((e)^*[A].obj F)).fac _ WalkingParallelPair.zero

/-- The pullback `Γ_Z(X, F) ⟶ Γ_{Z'}(X', e^* F)` of the sections with support, natural in
`F`. -/
noncomputable def sectionsWithSupportPullback :
    Sheaf.ΓSupport (Scheme.ProEt.topology X) A (op (Scheme.ProEt.mk i.openComplement.ι)) ⟶
      (e)^*[A] ⋙
        Sheaf.ΓSupport (Scheme.ProEt.topology X') A (op (Scheme.ProEt.mk i'.openComplement.ι)) where
  app F := sectionsWithSupportPullbackApp A e i i' h F
  naturality F G f := by
    rw [← cancel_mono ((Sheaf.ΓSupportι _ A (op (Scheme.ProEt.mk i'.openComplement.ι))).app
      ((e)^*[A].obj G))]
    have n₁ := (Sheaf.ΓSupportι _ A (op (Scheme.ProEt.mk i.openComplement.ι))).naturality f
    have n₂ := (Sheaf.ΓSupportι _ A (op (Scheme.ProEt.mk i'.openComplement.ι))).naturality
      ((e)^*[A].map f)
    have n₃ := (ΓPullback A e).naturality f
    simp only [assoc]
    rw [sectionsWithSupportPullbackApp_comp, reassoc_of% n₁, n₃]
    erw [n₂]
    rw [sectionsWithSupportPullbackApp_comp_assoc]
    rfl

@[simp]
lemma sectionsWithSupportPullback_app (F : Sheaf (Scheme.ProEt.topology X) A) :
    (sectionsWithSupportPullback A e i i' h).app F = sectionsWithSupportPullbackApp A e i i' h F :=
  rfl

lemma sectionsWithSupportPullback_comp :
    sectionsWithSupportPullback A e i i' h ≫ Functor.whiskerLeft _
        (Sheaf.ΓSupportι _ A (op (Scheme.ProEt.mk i'.openComplement.ι))) =
      Sheaf.ΓSupportι _ A (op (Scheme.ProEt.mk i.openComplement.ι)) ≫ ΓPullback A e := by
  ext F
  exact sectionsWithSupportPullbackApp_comp A e i i' h F

/-- Blueprint `thm-pur-with-support-exactness`: Long exact sequence for cohomology with support
(functoriality in the pair, for arbitrary morphisms of pairs).

For a morphism of schemes `e : X' ⟶ X` and closed immersions `i : Z ⟶ X`, `i' : Z' ⟶ X'` whose
open complements satisfy `U' ⊆ e⁻¹(U)` (i.e. `e⁻¹(Z) ⊆ Z'`), the pullback maps
`RΓ_Z(X, K) ⟶ RΓ_{Z'}(X', e^* K)`, `RΓ(X, K) ⟶ RΓ(X', e^* K)` and `RΓ(U, K) ⟶ RΓ(U', e^* K)`
form a morphism of triangles from `sectionsWithSupportTriangle` of `(X, Z)` to that of
`(X', Z')` applied to `e^* K`, natural in the bounded below complex `K` of pro-étale sheaves.
Here the exact pullback `e^*` acts termwise on complexes. -/
noncomputable def sectionsWithSupportTrianglePullback :
    sectionsWithSupportTriangle A i ⟶ D+((e)^*[A]) ⋙ sectionsWithSupportTriangle A i' :=
  ShortComplex.rightDerivedTrianglePullback (e)^*[A]
    (Sheaf.shortExactOnInjectives_ΓSupportShortComplex _ A _)
    (Sheaf.shortExactOnInjectives_ΓSupportShortComplex _ A _)
    (sectionsWithSupportPullback A e i i' h) (ΓPullback A e)
    (openComplementSectionsPullback A e i i' h) (sectionsWithSupportPullback_comp A e i i' h).symm
    (ΓPullback_comp_natTransΓRes A e i i' h).symm

/-- Blueprint `thm-pur-with-support-exactness`: Long exact sequence for cohomology with support
(functoriality of the long exact sequence in the pair).

The pullback maps along a morphism of pairs `e : (X', X' ∖ Z') ⟶ (X, X ∖ Z)` commute with all
the maps of the long exact sequences

`⋯ ⟶ H^q_Z(X, K) ⟶ H^q(X, K) ⟶ H^q(U, K) ⟶ H^{q+1}_Z(X, K) ⟶ ⋯`
`⋯ ⟶ H^q_{Z'}(X', e^*K) ⟶ H^q(X', e^*K) ⟶ H^q(U', e^*K) ⟶ H^{q+1}_{Z'}(X', e^*K) ⟶ ⋯`,

including the connecting maps. -/
theorem homology_sectionsWithSupportTrianglePullback_comm
    (K : Plus (Sheaf (Scheme.ProEt.topology X) A)) (q₀ q₁ : ℤ) (hq : q₀ + 1 = q₁) :
    (homologyFunctor A q₀).map ((sectionsWithSupportTriangle A i).obj K).mor₁ ≫
        (homologyFunctor A q₀).map ((sectionsWithSupportTrianglePullback A e i i' h).app K).hom₂ =
      (homologyFunctor A q₀).map ((sectionsWithSupportTrianglePullback A e i i' h).app K).hom₁ ≫
        (homologyFunctor A q₀).map
          ((sectionsWithSupportTriangle A i').obj (D+((e)^*[A]).obj K)).mor₁ ∧
    (homologyFunctor A q₀).map ((sectionsWithSupportTriangle A i).obj K).mor₂ ≫
        (homologyFunctor A q₀).map ((sectionsWithSupportTrianglePullback A e i i' h).app K).hom₃ =
      (homologyFunctor A q₀).map ((sectionsWithSupportTrianglePullback A e i i' h).app K).hom₂ ≫
        (homologyFunctor A q₀).map
          ((sectionsWithSupportTriangle A i').obj (D+((e)^*[A]).obj K)).mor₂ ∧
    HomologySequence.δ ((sectionsWithSupportTriangle A i).obj K) q₀ q₁ hq ≫
        (homologyFunctor A q₁).map ((sectionsWithSupportTrianglePullback A e i i' h).app K).hom₁ =
      (homologyFunctor A q₀).map ((sectionsWithSupportTrianglePullback A e i i' h).app K).hom₃ ≫
        HomologySequence.δ ((sectionsWithSupportTriangle A i').obj (D+((e)^*[A]).obj K)) q₀ q₁
          hq := by
  set φ := (sectionsWithSupportTrianglePullback A e i i' h).app K
  refine ⟨?_, ?_, ?_⟩
  · simp only [← Functor.map_comp, φ.comm₁]
    rfl
  · simp only [← Functor.map_comp, φ.comm₂]
    rfl
  · exact ((homologyFunctor A 0).homologySequenceδ_naturality φ q₀ q₁ hq).symm

section Comp

variable {X'' Z'' : Scheme.{u}} (e' : X'' ⟶ X') (i'' : Z'' ⟶ X'') [IsClosedImmersion i'']
  (h' : i''.openComplement ≤ e' ⁻¹ᵁ i'.openComplement)
  (h'' : i''.openComplement ≤ (e' ≫ e) ⁻¹ᵁ i.openComplement)

lemma sectionsPullback_congr {V : X.ProEt} {W : X'.ProEt} {φ₁ φ₂ : W.left ⟶ V.left}
    (hφ₁ : φ₁ ≫ V.hom = W.hom ≫ e) (hφ : φ₁ = φ₂) :
    sectionsPullback A e φ₁ hφ₁ = sectionsPullback A e φ₂ (hφ ▸ hφ₁) := by
  subst hφ
  rfl

/-- The pullback of sections over the open complements is compatible with the composition of
morphisms of pairs. -/
lemma openComplementSectionsPullback_comp :
    openComplementSectionsPullback A (e' ≫ e) i i'' h'' ≫
        Functor.whiskerRight (upperStarComp A e' e).hom _ =
      openComplementSectionsPullback A e i i' h ≫
        Functor.whiskerLeft _ (openComplementSectionsPullback A e' i' i'' h') := by
  ext F
  have hc := sectionsPullback_comp A e e' (V := Scheme.ProEt.mk i.openComplement.ι)
    (W := Scheme.ProEt.mk i'.openComplement.ι) (W'' := Scheme.ProEt.mk i''.openComplement.ι)
    (e.resLE _ _ h) (Scheme.Hom.resLE_comp_ι _ _)
    (e'.resLE _ _ h') (Scheme.Hom.resLE_comp_ι _ _) F
  have hres : (e' ≫ e).resLE i.openComplement i''.openComplement h'' =
      e'.resLE _ _ h' ≫ e.resLE _ _ h := by
    rw [← cancel_mono i.openComplement.ι]
    simp
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    openComplementSectionsPullback]
  rw [sectionsPullback_congr A (e' ≫ e) _ hres]
  exact hc

/-- The pullback of the sections with support is compatible with the composition of morphisms
of pairs. -/
lemma sectionsWithSupportPullback_comp_comp :
    sectionsWithSupportPullback A (e' ≫ e) i i'' h'' ≫
        Functor.whiskerRight (upperStarComp A e' e).hom _ =
      sectionsWithSupportPullback A e i i' h ≫
        Functor.whiskerLeft _ (sectionsWithSupportPullback A e' i' i'' h') := by
  ext F
  rw [← cancel_mono ((Sheaf.ΓSupportι _ A (op (Scheme.ProEt.mk i''.openComplement.ι))).app
    ((e')^*[A].obj ((e)^*[A].obj F)))]
  have n := (Sheaf.ΓSupportι _ A (op (Scheme.ProEt.mk i''.openComplement.ι))).naturality
    ((upperStarComp A e' e).hom.app F)
  have hΓ := congr_app (ΓPullback_comp A e e') F
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_obj, sectionsWithSupportPullback_app] at n hΓ ⊢
  rw [assoc, n, sectionsWithSupportPullbackApp_comp_assoc, hΓ, assoc,
    sectionsWithSupportPullbackApp_comp, sectionsWithSupportPullbackApp_comp_assoc]

attribute [local instance] Limits.comp_preservesFiniteLimits Limits.comp_preservesFiniteColimits

/-- Blueprint `thm-pur-with-support-exactness`: Long exact sequence for cohomology with support
(compatibility of the functoriality in the pair with composition).

For morphisms of pairs `e : (X', Z') ⟶ (X, Z)` and `e' : (X'', Z'') ⟶ (X', Z')`, the morphism of
triangles of cohomology with support along `e' ≫ e` is the composite of the morphisms of
triangles along `e` and `e'`, up to the comparison `(e' ≫ e)^* K ≅ e'^* e^* K`. -/
theorem sectionsWithSupportTrianglePullback_comp (K : Plus (Sheaf (Scheme.ProEt.topology X) A)) :
    (sectionsWithSupportTrianglePullback A (e' ≫ e) i i'' h'').app K ≫
        (sectionsWithSupportTriangle A i'').map
          ((Functor.mapDerivedCategoryPlusNatIso (upperStarComp A e' e) ≪≫
            Functor.mapDerivedCategoryPlusCompIso (e)^*[A] (e')^*[A]).hom.app K) =
      (sectionsWithSupportTrianglePullback A e i i' h).app K ≫
        (sectionsWithSupportTrianglePullback A e' i' i'' h').app (D+((e)^*[A]).obj K) :=
  ShortComplex.rightDerivedTrianglePullback_comp (ε := upperStarComp A e' e)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (sectionsWithSupportPullback_comp_comp A e i i' h e' i'' h' h'')
    (ΓPullback_comp A e e') (openComplementSectionsPullback_comp A e i i' h e' i'' h' h'') K

end Comp

end Pair

end ProEtale

end AlgebraicGeometry
